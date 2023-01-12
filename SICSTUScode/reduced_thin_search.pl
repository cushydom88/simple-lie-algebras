:- use_module(library(clpfd) ).
:- use_module(library(lists)).
:- use_module(library(samsort)). 
:- use_module(library(ordsets)).
:- use_module(library(ugraphs)).
:- use_module(library(between)).

% The following predicate reduced_thin_search is our main predicate for
% searching for simple thin Lie algebras. The parameter N is inputted by the
% users. The output is ThinTables which is a list of NxN arrays. Each of which
% represents a thin Lie algebra of dimension 2^N - 1. For N = 2,3,4,5 each
% member of ThinTables represents a simple Lie algebra. We confirm this using
% graph. % For N >= 4 there are different members of ThinTables that represent
% the same Lie algebra. See the main body of the paper for does_not_centralise.
%
% reduced_thin_search consists of the following 4 main parts.
%
% 1. INITIAL THIN SEARCH
% The predicate thin_search generates FirstTables which consists of a list of
% tables each representing a thin Lie algebra. thin_search itself consists of
% three main components:
% a. Implement the Lie bracket as constraints so that each table produced
%    represents a valid Lie algebra.
% b. Constraints which are necessary for simplicity of the represented Lie
%    algebras via the predicates stop_certain_ideals and act_faithfully. See the
%    paper for the theoretical underpinning of these constraints.
% c. Symmetry breaking constraints via the predicate break_gl2_symmetries. These
%    constraints removes some tables which represent the same Lie algebra. Not
%    all possible symmetries can be added as constraints due to time and memory
%    issues.
% Note that the order of the predicates inside thin_search do not follow the
% order listed above. The order constraints are added impact the run time. We
% have optimised the ordering.
%
% 2. POST SEARCH SIMPLICTY CHECK
% The predicate remove_non_simple_tables takes in the tables FirstTables and
% removes certain tables representing non-simple Lie algebras. See the paper for
% a description of what ideals are checked for. The tables which pass this check
% are represented by SimpleTables. In theory this condition could have been
% converted to a constraint and added to thin_search. However doing this is
% significantly slower than performing them as a post process.
%
% 3. LEX REDUCE TABLES
% As mentioned in 1. the predicate break_gl2_symmetries does not implement all
% possible symmetries as constraints. We now implement the rest of these
% symmetries on the tables SimpleTables and output the results to ReducedTables.
% At this stage no two tables in ReducedTables can be transformed in to each
% other via permutations of roots.
%
% 4. TORAL SWITCHING 
% We now remove further tables from ReducedTables representing the same Lie
% algebra. For each table in ReducedTables we perform one toral switch for each
% nilpotent basis element in that table. A graph is then constructed with vertex
% set represented by the elements of ReducedTables and an edge between two
% vertices if a toral switch transformed the tables represented by the two
% vertices in to one another. For each connected component of this graph we take
% one table from it and output these to ThinTables.
%
% In addition to the above sections we have the following two sections that
% collect shared predicates used throughout the code.
%
% 5. SYMMETRY PREDICATES
% These are a collection of predicates used throughout the code that deal with
% permuting roots.
%
% 6. UTILITY PREDICATES
% These are a collection of generic predicates used throughout the code.
%
% An example prompt to run the main predicate is 
% ['ThinSymmetrySicstus.pl'].
% test(4, ThinTables), maplist( writeln, ThinTables).

%%% 0. THE MAIN PREDICATE %%%
reduced_thin_search( N, ThinTables ) :-
    findall( Rows, (thin_search( Vs, N, Rows), labeling( [], Vs) ), FirstTables ),
    remove_non_simple_tables( FirstTables, SimpleTables ),
    lex_reduce_tables( N, SimpleTables, ReducedTables ),
    once(perform_toral_switchings( N, ReducedTables, ThinTables )).
%%%%%%

%%% 1. INITIAL THIN SEARCH %%%
thin_search( Vs, N, Rows) :-
    M is 2^N-1,
	length(Rows, M),
	maplist(same_length(Rows),Rows),
	append(Rows, Vs), 
    domain( Vs, 0, 1),
	transpose(Rows, Rows), % Lie Bracket constraint: Symmetry of the bracket
    numlist(M, Indices),
	maplist( set_value_to_zero, Indices, Rows), % Lie Bracket constraint: [x, x] = 0
    stop_certain_ideals(Rows,Indices), % Simplicity constraints
    act_faithfully(Rows,Indices), % Simplicity constraints
	jacobi_identity_full( Indices, Rows), % Lie Bracket constraint: The Jacobi Identity
	break_gl2_symmetries( Vs, Rows, N ). % Symmetry breaking constraints

% The Jacobi Identity 
jacobi_identity_full( Indices, Rows) :-
    findall( [A,B,C], ( append( [_,[A],_,[B],_,[C],_], Indices ),  D is xor(B, C), A #\= D ), Triples ),
    maplist( jacobi_identity( Rows ), Triples ).
jacobi_identity( Rows, [I1,I2,I3] ) :-
    I4 is xor(I1, I2),
    I5 is xor(I1, I3),
    I6 is xor(I2, I3),
    get_entry( Rows, [I1, I2], A ),
    get_entry( Rows, [I3, I4], B ),
    get_entry( Rows, [I1, I3], C ),
    get_entry( Rows, [I2, I5], D ),
    get_entry( Rows, [I2, I3], E ),
    get_entry( Rows, [I1, I6], F ),
	domain( [G,H,I], 0, 1),
    G #>= A + B - 1,
    G #=< A, 
    G #=< B,
    H #>= C + D - 1,
    H #=< C, 
    H #=< D,
    I #>= E + F - 1,
    I #=< E, 
    I #=< F,
    G + H + I #\= 1,
    G + H + I #\= 3.

% Simplicity conditions 
stop_certain_ideals(Rows,Indices) :-
    make_L1_inds( Indices, L1s),
    maplist( check_L1_makes_L0(Rows, Indices), L1s ).
make_L1_inds( Indices, L1s) :-
    maplist( root_to_L1(Indices), Indices, L1s ).
root_to_L1(Indices, Root, L1 ) :-
    findall(A, (member(A,Indices), B is (Root /\ A), dec2bin(B, Bin), sum(Bin,#=,S), (S mod 2) #= 1) , L1).
check_L1_makes_L0(Rows, Indices, L1) :-
    exclude( member_(L1), Indices, L0 ),
    maplist(is_made_check(Rows, L1), L0).
is_made_check( Rows, L1, A ) :-
    maplist( is_made_check_helper(Rows, A), L1, Entries ),
    sum( Entries, #>, 0 ).
is_made_check_helper( Rows, A, B, Entry ) :-
    C is xor(A, B),
    get_entry( Rows, [B,C], Entry ).
act_faithfully( Rows, Indices ) :-
    make_L1_inds( Indices, L1s ),
    maplist( check_L0_acts_faithfully( Rows, Indices ), L1s ).
check_L0_acts_faithfully( Rows, Indices, L1 ) :-
    exclude( member_(L1), Indices, L0 ),
    maplist(does_not_centralise(Rows, L1), L0).
does_not_centralise( Rows, L1, X ) :-
    maplist( does_not_centralise_helper( Rows, X ), L1, Entries ),
    sum( Entries, #>, 0 ).
does_not_centralise_helper( Rows, X, A, Entry ) :-
    get_entry( Rows, [A,X], Entry ).

%%% Symmetry breaking code %%%

% gl_2 is hardcoded due to its small size
get_gl2( GL2 ) :- GL2 = [ [[1,0],[1,1]],[[1,1],[0,1]],[[1,1],[1,0]],[[0,1],[1,1]],[[0,1],[1,0]] ].

% For each pair of simple roots and each element of gl_2
% create a symmetry breaking constraint
break_gl2_symmetries( Vs, Rows, N ) :-
    get_gl2( GL2 ),
    numlist( N, SimpleInds ),
    findall( [A,B], ( member(A, SimpleInds), member(B, SimpleInds), A #< B ), Pairs ),
    maplist( break_gl2_symmetry( Vs, Rows, N, GL2), Pairs ).
break_gl2_symmetry( Vs, Rows, N, GL2, [J,K] ) :-
    maplist( add_to_gln_small( N, [J, K] ), GL2, SmolGLN ),
    get_roots(N,Roots), 
    make_powers(N,Powers),
    maplist( make_perm(Roots,Powers), SmolGLN, RowPerms ),
    maplist( break_symmetry( Vs, Rows), RowPerms ). 

% Create the subset of gl_n we create constraints for
add_to_gln_small( N, [J,K], Mat1, NewMat ) :- 
    M is N - 2,
    row_of_n_zeros( M, ZeroRow ),
    nth1( 1, Mat1, Row1 ),
    nth1( 2, Mat1, Row2 ),
    nth1( 1, Row1, A ),
    nth1( 2, Row1, B ),
    nth1( 1, Row2, C ),
    nth1( 2, Row2, D ),
    place_entry( J, A, ZeroRow, Row3 ),
    place_entry( K, B, Row3, Row4 ), % Place this at pos J
    place_entry( J, C, ZeroRow, Row5 ),
    place_entry( K, D, Row5, Row6 ), % Place this at pos K
    numlist( N, Indices ),
    findall( I, ( member( I, Indices ), I #\= J, I #\= K ), IdInds ),
    maplist( make_kth_row( Indices ), IdInds, Mat2 ),
    place_entry( J, Row4, Mat2, Mat3 ),
    place_entry( K, Row6, Mat3, NewMat ).

% Create the symmetry breaking constraint
% RowPerm is a permutation generated by an element of gl_n
% RowPerm is applied to the rows and columns of Row to obtain NewerRows
% Add the constraint that Rows is lexicographically lower than NewerRows
break_symmetry( Vs, Rows, RowPerm ) :-
    maplist(permute_rows(Rows), RowPerm, NewRows ),
    transpose(NewRows, TNewRows),
    maplist(permute_rows(TNewRows), RowPerm, NewerRows ),
    same_length( Vs, Ns ),
    append(NewerRows, Ns),
	lex_chain( [ Vs, Ns ] ).
%%%%%%

%%% 2. POST SEARCH SIMPLICITY CHECK %%%
% Search for certain non-trivial ideals for each table in Tables
% See paper for explanation
remove_non_simple_tables( Tables, SimpleTables ) :-
    include( simple_check, Tables, SimpleTables ).
simple_check( Rows ) :-
	length( Rows, N ),
    numlist( N, Indices ),
    maplist( my_sum, Rows, RowSums ),
    sort( RowSums, UniqueRowSums ),
    findall( A, ( member( B, UniqueRowSums ), A #= B + 1 ), IdealSizes ),
    maplist( check_for_ideals( Rows, Indices ), IdealSizes ).
sum_plus_one( Elems, Tot ) :-
    sum( Elems, #=, Tot0 ),
    Tot #= Tot0 + 1.
check_for_ideals(Rows, Indices, IdealSize ) :-
    findall( A, ( member( A, Indices ), nth1( A, Rows, Row ), sum( Row, #=, S ), S #= IdealSize - 1 ), CorrectRankRoots ),
    findall( A, ( length( A, IdealSize), subset_set( A, CorrectRankRoots ) ), PossibleIdeals ),
    maplist( check_ideal( Rows ), PossibleIdeals ).
check_ideal( Rows, PossibleIdeal ) :-
    maplist( check_ideal_helper(Rows, PossibleIdeal), PossibleIdeal, Mat ),
    append( Mat, Ms ),
    sum( Ms, #=, Tot ),
    length( PossibleIdeal, N ),
    M is N^2 - N,
    Tot #\= M.
check_ideal_helper( Rows, PossibleIdeal, X, Row ) :-
    maplist( check_ideal_helper_2( Rows, X), PossibleIdeal, Row ).
check_ideal_helper_2( _, X, X, Entry ) :-
    Entry #= 0.
check_ideal_helper_2( Rows, X, Y, Entry ) :-
    X #\= Y,
    I is xor(X,Y),
    get_entry( Rows, [I,X], Entry).
%%%%%%

%%% 3. LEX REDUCE TABLES %%%
% Remove all tables from SimpleTables that are not in their lexicographically min form
lex_reduce_tables( N, SimpleTables, ReducedTables ) :-
    get_roots( N, Roots ),
    make_powers( N, Powers ),
    % For each table calculate its row sums and partition SimpleTables based on this
    populate_row_sum_tables_list( SimpleTables, TablesList ),
    % For each list of tables remove tables not in lexicographically min form
    maplist( lex_reduce(N, Roots, Powers), TablesList, ReducedTablesList ),
    % Combine ReducedTablesList in to ReducedTables
    append( ReducedTablesList, ReducedTables ).

% Recursively generate ReducedList from List
% 1. Add the element of List with min lexicographical order to ReducedList, call this MinTable
% 2. Remove all elements equivalent to MinTable via row permutations from List
% 3. Repeat 1. and 2. until List is empty 
lex_reduce( N, Roots, Powers, List, ReducedList ) :-
    lex_reduce( N, Roots, Powers, List, [], ReducedList).
lex_reduce( _, _, _, [], Mins, ReducedList) :- 
    ReducedList = Mins.
lex_reduce( _, _, _, List, Mins, ReducedList) :-
    length( List, 1 ),
    append( Mins, List, ReducedList ).
lex_reduce( N, Roots, Powers, List, Mins, ReducedList) :-
    length( List, K ),
    K #> 1,
    min_member( my_lex, MinTable, List ),
    sorted_row_sums( MinTable, SortedRowSums ),
    exclude( can_permute_dispatcher( N, Roots, Powers, SortedRowSums, MinTable), List,  NewList ),
    append( Mins, [MinTable], NewMins ),
    lex_reduce( N, Roots, Powers, NewList, NewMins, ReducedList).

% Calculate row sums and partition with respect to row sums
populate_row_sum_tables_list( SimpleTables, TablesList ) :-
    maplist( full_sorted_row_sums, SimpleTables, TooManyRowSums ),
    list_to_ord_set( TooManyRowSums, RowSumsList ),
    maplist( filter_by_row_sum(SimpleTables), RowSumsList, TablesList ).
filter_by_row_sum( SimpleTables, RowSums, Tables ) :-
    findall( Table, ( member( Table, SimpleTables ), full_sorted_row_sums( Table, RowSums ) ), Tables ).

% lexicographical order for arrays
my_lex( A, B ) :-
    append( A, As ),
    append( B, Bs ),
    lex_chain( [As, Bs] ).
%%%%%%

%%% 4. TORAL SWITCHING %%%
perform_toral_switchings( N, Tables, SwitchedTables ) :-
    M is 2^N-1,
    K is 2^(N-1),
    numlist( M, Indices ),
    get_roots( N,Roots ),
    make_powers( N, Powers ), 
    % For each table in Tables find all the basis elements which are nilpotent
    maplist(locate_basis_nilps( Indices, K ), Tables, NilpIndicesList ),
    % Make a torus which all switches will be made with respect to
    make_base_torus( BaseTorus, N, Indices ),
    findall( [A,B], ( member(A, Indices), member(B, Indices), A #< B ), Pairs ), 
    % Make a torus switch for each nilpotent basis element
    maplist( make_torus_switches( Indices, Pairs, Roots, BaseTorus ), Tables, NilpIndicesList, SwitchedTablesList ),
    % Lexicographically reduce each switched table
    once(canonical_order_tables_list( N, Roots, Powers, Tables, SwitchedTablesList, OrderedTablesList )), 
    % Make the graph based on toral switchings. See paper for details
    once(make_adjacency_mat( Tables, OrderedTablesList, AdjacencyMat )),
    adjacency_mat_to_ugraph( AdjacencyMat, SwitchingGraph ),
    conn_comps( SwitchingGraph, Comps ),
    % Return one table per connected component of the graph
    maplist( get_min_from_comp( Tables ), Comps, SwitchedTables ).

% Finds nilpotent basis elements
locate_basis_nilps( Indices, K, Rows, NilpIndices ) :-
    include( locate_basis_nilps_helper( Rows, K ), Indices, NilpIndices ).
locate_basis_nilps_helper( Rows, K, I ) :-
    nth1( I, Rows, Row ), 
    sum( Row, #<, K ).

% Makes standard torus to be used in all switchings
make_base_torus( BaseTorus, N, Indices ) :-
    length( BaseTorus, N ),
    numlist( N, SmolIndices ),
    maplist( make_base_torus_row( Indices ), SmolIndices, BaseTorus ).
make_base_torus_row( Indices, RowIndex, BaseTorusRow ) :-
    RootIndex is 2^(RowIndex - 1),
    maplist( make_base_torus_entry( RootIndex ), Indices, BaseTorusRow ).
make_base_torus_entry( RootIndex, ColIndex, Entry ) :-
    X is ( RootIndex /\ ColIndex ),
    make_base_torus_entry_helper( X, Entry ).
make_base_torus_entry_helper( 0, 0 ).
make_base_torus_entry_helper( X, 1 ) :-
    X #\= 0.

% Main toral switching code
make_torus_switches( _, _, _, _, _, [], SwitchedTables ) :-
    SwitchedTables = []. % no nilpotent basis elements to switch with respect to
make_torus_switches( Indices, Pairs, Roots, BaseTorus, Table, NilpIndices, SwitchedTables ) :-
    length( NilpIndices, K ),
    K #> 0,
    maplist( switch_torus( Indices, Pairs, Table, BaseTorus, Roots), NilpIndices, SwitchedTables ).
switch_torus( Indices, Pairs, Table, BaseTorus, Roots, NilpIndex, SwitchedTable ) :-
    maplist( modify_toral_element_checker( NilpIndex ), BaseTorus, ModifyToralElementChecker ),
    maplist( make_new_basis( Indices, Table, BaseTorus, NilpIndex, ModifyToralElementChecker), Roots, NewBasis ),
    make_new_table( Indices, Pairs, Table, NewBasis, SwitchedTable ).

% Checks wether the toral element in the switched torus has been modified
modify_toral_element_checker( NilpIndex, ToralRow, ModifyToralElement ) :-
    nth1( NilpIndex, ToralRow, ModifyToralElement ).

% NewBasisElement is the basis element in the rootspace with respect to Root after the toral switch
% It is expressed as a list in terms of the original thin basis
make_new_basis( Indices, Table, BaseTorus, NilpIndex, ModifyToralElementChecker, Root, NewBasisElement ) :-
    same_length( Table, NewBasisElement ),
    domain( NewBasisElement, 0, 1),
    once( make_new_basis_helper( Indices, Table, BaseTorus, NilpIndex, ModifyToralElementChecker, Root, NewBasisElement ) ),
    labeling( [], NewBasisElement ) .
make_new_basis_helper( Indices, Table, BaseTorus, NilpIndex, ModifyToralElementChecker, Root, NewBasisElement ) :-
    sum( NewBasisElement, #>, 0 ),
    maplist( apply_root_value( Indices, Table, NilpIndex, NewBasisElement), BaseTorus, ModifyToralElementChecker, Root ).

% Apply a new toral element on NewBasisElement and kill or stableise it depending on RootVal
% NewBasisElement is determined by the constraints created here
apply_root_value( Indices, Table, NilpIndex, NewBasisElement, ToralRow, ModifyToralElement, RootVal ) :-
    maplist( times, ToralRow, NewBasisElement, TorusOnElement),
    nth1( NilpIndex, Table, NilpRow ),
    maplist( nilp_on_element(NilpRow, NewBasisElement, NilpIndex), Indices, NilpOnElement ),
    maplist( times(ModifyToralElement), NilpOnElement, ScaledNilpOnElement ),
    maplist( sum_mod_2, TorusOnElement, ScaledNilpOnElement, ActedOnElement ),
    maplist( times(RootVal), NewBasisElement, ScaledNewBasisElement ),
    maplist( eq, ScaledNewBasisElement, ActedOnElement).
nilp_on_element(_, _, NilpIndex, NilpIndex, NilpOnElementEntry ) :- 
    NilpOnElementEntry #= 0.
nilp_on_element(NilpRow, NewBasisElement, NilpIndex, Index, NilpOnElementEntry ) :-
    NilpIndex #\= Index,
    NewIndex is xor(NilpIndex, Index),
    nth1( NewIndex, NewBasisElement, V),
    nth1( NewIndex, NilpRow, NilpOnElementEntry0 ),
    NilpOnElementEntry #= NilpOnElementEntry0 * V.

% Given the new thin basis NewBasis calculate its thin table 
make_new_table( Indices, Pairs, Table, NewBasis, NewTable ) :-
    maplist( set_diagonal( NewTable ), Indices ),
    maplist( intify_basis(Indices), NewBasis, IntBasis ),
    same_length( Table, NewTable ),
    maplist( same_length(NewTable), NewTable ),
    maplist( make_new_table_entry( Indices, Table, IntBasis, NewTable ), Pairs ).
make_new_table_entry( Indices, Table, IntBasis, NewTable, [I1, I2] ) :-
    I3 is xor( I1, I2 ),
    nth1( I1, IntBasis, Ints1 ),
    nth1( I2, IntBasis, Ints2 ),
    nth1( I3, IntBasis, Ints3 ),
    nth1( 1, Ints3, MainInt ),
    maplist( make_xor_pair(MainInt), Indices, XORPairs ),
    include( filter_xor_pairs( Ints1, Ints2 ), XORPairs, FilteredPairs ), 
    get_entries( Table, FilteredPairs, Entries ),
    sum(Entries, #=, Tot),
    Val #= ( Tot mod 2 ),
    get_entry( NewTable, [I1, I2], Val ),
    get_entry( NewTable, [I2, I1], Val ).
% The below predicates appear as they are due to Sicstus not having a version
% of xor compatible with  the # operation in CLPFD. 
filter_xor_pairs( Ints1, Ints2, [I, J ] ) :-
    member(I, Ints1),
    member(J, Ints2).
make_xor_pair( A, B, [B, C] ) :-
    C is xor( A, B).
intify_basis( Indices, BasisRow, Ints ) :-
    include( intify_basis_helper(BasisRow), Indices, Ints ).
intify_basis_helper( BasisRow, I ) :-
    nth1( I, BasisRow, 1 ).
set_diagonal( NewTable, I ) :-
    get_entry( NewTable, [I,I], 0 ).

% Lexicographically reduce switched tables. Similar methods to 3. LEX REDUCE TABLES 
canonical_order_tables_list( N, Roots, Powers, Tables, SwitchedTablesList, OrderedTablesList) :-
    maplist( make_table_row_sum_pair, Tables, TablesWithSums ),
    maplist( canonical_order_rows0( N, Roots, Powers, TablesWithSums ), SwitchedTablesList, OrderedTablesList ).
make_table_row_sum_pair( Table, [X, Y] ) :-
    X = Table,
    full_sorted_row_sums( Table, Y ).
canonical_order_rows0( _, _, _, _, [], OrderedTables) :-
    OrderedTables = [].
canonical_order_rows0( N, Roots, Powers, SimpleTablesWithSums, Tables, OrderedTables) :-
    length(Tables, K),
    K #> 0,
    maplist(canonical_order_rows( N, Roots, Powers, SimpleTablesWithSums ), Tables, OrderedTables).
canonical_order_rows( N, Roots, Powers, SimpleTablesWithSums, Rows, OrderedRows) :-
    full_sorted_row_sums( Rows, RowSums),
    sort( RowSums, SortedRowSums),
    findall( Table, ( member(TableWithSums, SimpleTablesWithSums), TableWithSums = [ Table, RowSums ] ), SimpleTables ),
    first_sol( lex_reduce_to_simple( N, Roots, Powers, Rows, SortedRowSums ), SimpleTables, OrderedRows ).
lex_reduce_to_simple( N, Roots, Powers, Rows, SortedRowSums, Table ) :-
    can_permute_dispatcher( N, Roots, Powers, SortedRowSums, Rows, Table).

% Make the toral switching graph
% If a table T1 switches to T2 then T2 might not have switched to T1
% Thus we calculate a directed graph first
% We then remove the directions on edges 
make_adjacency_mat( Tables, OrderedTablesList, AdjacencyMat ) :-
	length( Tables, M ),
    numlist( M, Indices ),
    maplist( make_adjacency_row( Tables, OrderedTablesList, Indices ), Indices, Mat ),
    transpose( Mat, TMat),
    maplist(maplist( my_max ), Mat, TMat, AdjacencyMat).
make_adjacency_row( Tables, OrderedTablesList, Indices, RowIndex, AdjacencyRow ) :-
    maplist( make_adjacency_entry( Tables, OrderedTablesList, RowIndex ), Indices, AdjacencyRow ).
make_adjacency_entry( _, _, RowIndex , RowIndex, AdjacencyEntry ) :-
    AdjacencyEntry #= 0.
make_adjacency_entry( Tables, OrderedTablesList, RowIndex , ColIndex, AdjacencyEntry ) :-
    RowIndex #\= ColIndex,
    nth1( RowIndex, Tables, Table ),
    nth1( ColIndex, OrderedTablesList, TableList ),
    set_adjacency_entry( Table, TableList, AdjacencyEntry ).
set_adjacency_entry( Table, TableList, AdjacencyEntry ) :-
    member( Table, TableList ),
    AdjacencyEntry #= 1.
set_adjacency_entry( Table, TableList, AdjacencyEntry ) :-
    (\+ member( Table, TableList )),
    AdjacencyEntry #= 0.
% Convert an adjacency matrix to a ugraph
adjacency_mat_to_ugraph( A, G ) :-
    length( A, N ),
    numlist(N, Indices),
    maplist( collect_nbrs(A,Indices), Indices, NbrsList ), 
    maplist( make_vertex, Indices, NbrsList, G ).
make_vertex( Index, Nbrs, V ) :-
    V = Index-Nbrs. % This is the ugraph notation for defining a vertex and its neighbours
% Find the neighbours (Nbrs) of a vertex (Index)
collect_nbrs(A, Indices, Index, Nbrs ) :-
    nth1( Index, A, Row ),
    findall( X, ( member( X, Indices ), nth1( X, Row, 1 ) ), Nbrs).

% Calculate the connected components of a graph.
% We make use of transitive_closure from ugraphs
conn_comps( G, Comps ) :-
    length( G, N), 
    numlist(N, Indices),
    transitive_closure(G, C),
    maplist( get_closure(C), Indices, RepeatComps  ),
    setof( Comp, member( Comp, RepeatComps ), Comps ).
get_closure(C, Index, Closure ) :-
    neighbours( Index, C, PreClosure),
    add_self( Index, PreClosure, NotSortedClosure),
    sort( NotSortedClosure, Closure).
add_self( Index, A, B) :-
    member(Index, A),
    B = A.
add_self( Index, A, B) :-
    (\+ member( Index, A )),
    append( [A, [Index]], B ).
get_min_from_comp( Tables, Comp, MinTable ) :-
    get_values( Tables, Comp, CompTables ),
    min_member( my_lex, MinTable, CompTables ).
%%%%%%

%%% 5. SYMMETRY PREDICATES %%%
% Code used in symmetry breaking and lexicographically reducing tables

% Make a permutation of rows based on an element of gl_n acting on the simple roots
make_perm(Roots,Powers, Mat, RowPerm ) :-
    maplist( perm_it(Powers, Mat), Roots, RowPerm ).
perm_it(Powers, Mat, Root, Entry ) :-
    act_mat(Mat, Root, RootOut),
    bin_2_dec(Powers, RootOut, Entry).

% Apply a permutation
permute_rows(Rows, PermIndex, NewRow ) :-
    nth1( PermIndex, Rows, NewRow).

%%% The predicate can_permute_dispatcher checks if Table1 can be permuted in to Table2
% This is used in both lex reducing and toral switching
can_permute_dispatcher( N, Roots, Powers, SortedRowSums, Table1, Table2 ) :-
    length( Mat, N ),
	maplist(same_length(Mat), Mat),
    once(can_permute( N, Roots, Powers, Table1, Table2, Mat, SortedRowSums ) ).
can_permute( N, Roots, Powers, T1, T2, Mat, SortedRowSums ) :-
    length( Mat, N ),
	append( Mat, Ms), 
    domain( Ms, 0, 1),
    % Use the row sums of T1 and T2 to create constraints on which rows of T1 are mapped to which rows of T2
    partition_by_row_sums( T1, SortedRowSums, Partition1 ),
    partition_by_row_sums( T2, SortedRowSums, Partition2 ),
    maplist( map_partitions(N, Mat, Powers), Partition1, Partition2 ),
    make_perm( Roots, Powers, Mat, RowPerm ),
    maplist(permute_rows(T2), RowPerm, NewRows ),
    transpose(NewRows, TNewRows),
    maplist(permute_rows(TNewRows), RowPerm, T1 ).
map_partitions( N, Mat, _, L1, L2 ) :-
    length( L1, K ),
    K #= 1,
    Rank is N,
    nth1( 1, L1, N1 ),
    nth1( 1, L2, N2 ),
    dec_2_bin( Rank, N1, B1 ),
    dec_2_bin( Rank, N2, B2 ),
    act_mat( Mat, B1, B2 ).
map_partitions( N, Mat, Powers, L1, L2 ) :-
    length( L1, K ),
    K #> 1,
    Rank is N,
    maplist( dec_2_bin( Rank ), L1, Domain ),
    maplist( set_range( Mat, Powers, L2 ), Domain ).
set_range( Mat, Powers, Range, B1 ) :-
    act_mat( Mat, B1, B2 ),
    bin_2_dec( Powers, B2, D ),
    element( _, Range, D ).
partition_by_row_sums( Mat, SortedRowSums, Partition ) :-
    maplist( has_row_sum(Mat), SortedRowSums, Partition ).
has_row_sum( Mat, S, L ) :-
    findall( I, ( nth1( I, Mat, R ), sum( R, #=, S ) ), L ).

% row sums with no repeats
sorted_row_sums( M, Sorted ) :-
    maplist( my_sum, M, Sums ),
    sort( Sums, Sorted ).
% row sums including repeats. Sicstus needs samsort importing
full_sorted_row_sums( M, Sorted ) :-
    maplist( my_sum, M, Sums ),
    samsort( Sums, Sorted ).
%%%%%%

%%%%%%

%%% 6. UTILITY PREDICATES %%%
% generic predicates used throughout

% Basic computations
plus(X,Y,Z) :- X+Y #= Z.
eq(A,B) :- A #= B.
equal_to_zero( X ) :- X #= 0.
sum_mod_2( A, B, C ) :- ((A + B) mod 2 ) #= C.
times(A,B,C) :- A*B  #= C.

% equivalent to sum( Elems, #=, Tot )
my_sum( Elems, Tot ) :-
    sum( Elems, #=, Tot ).

% C is the max of A and B
my_max( A, B, C ) :-
    A #< B,
    C #= B.
my_max( A, B, C ) :-
    A #>= B,
    C #= A.

% Get entries from lists and arrays
get_value( Row, Index, Value ) :-
    nth1( Index, Row, Value).
get_values( Row, Indices, Values ) :-
    maplist( get_value(Row), Indices, Values ).
get_entry( Rows, [RowIndex, ColIndex], Entry ) :-
    nth1( RowIndex, Rows, Row),
    nth1( ColIndex, Row, Entry).
get_entries( Rows, Indices, Entries ) :-
    maplist( get_entry(Rows), Indices, Entries ).

% set an element of a list to be 0
set_value_to_zero( Index, Row ) :-
    nth1( Index, Row, 0).

% Powers is a list of powers of 2
make_powers(N, Powers) :-
    make_powers0(N, Roots),
    reverse(Roots, Powers).
make_powers0(N, Roots) :-
    numlist(N, Indices),
    maplist(make_powers_helper, Indices, Roots).  
make_powers_helper(Ind, Root) :-
    Val is 2^(Ind - 1),
    Root #= Val.

% binary and decimal conversion
dec_2_bin(Rank,N,L) :-
    dec2bin(N, L0),
    length(L0,K),
    length(L,Rank),
    M #= Rank - K,
    row_of_n_zeros( M, Zs ),
    append(Zs, L0, L).
dec2bin(0,[0]).
dec2bin(1,[1]).
dec2bin(N,L):- 
    N > 1,
    X #= ( N mod 2 ),
    Y #= (N // 2),  
    dec2bin(Y,L1), 
    append(L1, [X], L).
bin_2_dec(Powers, L, N) :-
    maplist(times, Powers, L, P),
    sum(P,#=,N).

member_( L, E ) :- 
    member( E, L ).

% generate roots as elements of GF(2)^N
get_roots(N, Roots) :-
	findall(L,( length(L,N), domain( L, 0, 1 ), labeling( [], L)  ),RootsZ),
	RootsZ=[_|Roots].

% Mat acting on VecIn gives VecOut
act_mat(Mat, VecIn, VecOut) :- % NB VecIn cannot have variables
	maplist( my_scalar_prod( VecIn ), Mat, VecOut).
my_scalar_prod( V1, M1, X) :- 
    same_length( V1, Prods ),
    maplist( times, V1, M1, Prods ),
    sum( Prods, #=, Y ), 
    (Y mod 2) #= X.

% make a list of all zeroes
row_of_n_zeros( N, Row ) :-
    length( Row, N ),
    maplist( equal_to_zero, Row ).

% KthRow has the same length as Indices, a 1 in position K, and zeroes elsewhere
make_kth_row( Indices, K, KthRow ) :-
    maplist( set_kth_row( K ), Indices, KthRow ).
set_kth_row(  K, K, Entry ) :- Entry #= 1.
set_kth_row(  K, Index, Entry ) :- Index #\= K, Entry #= 0. 

% adding Entry to X at position I obtains Y
place_entry( Ind, Entry, X, Y ) :- 
    L is Ind - 1,
    length( A, L ),
    append( A, B, X ),
    append( [ A, [Entry], B ], Y ).

% recursively check if a set is a subset of another set
subset_set([], _).
subset_set([X|Xs], S) :-
    append(_, [X|S1], S),
    subset_set(Xs, S1).

% Sol is the first element of List to satisfy Goal
first_sol(Goal, List, Sol) :-
    first_sol_(List, Goal, Sol).
first_sol_([], _, []).
first_sol_([X1|Xs1], P, Sol) :-
    (   call(P, X1) ->  Sol = X1
    ;   first_sol_(Xs1, P, Sol )
    ).

% Sictus does not have writeln and one of the authors is fond of it
writeln( Stream ) :-
    write( Stream ),
    write('\n').

% Sicstus needs maplist/4 defining manually
maplist(Pred, Ws, Xs, Ys, Zs) :-
    ( foreach(W,Ws),
    foreach(X,Xs),
    foreach(Y,Ys),
    foreach(Z,Zs),
    param(Pred)
    do call(Pred, W, X, Y, Z)
    ).

%%%%%%

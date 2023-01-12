:- use_module(library(clpfd)), set_prolog_flag(clpfd_monotonic, true).

% The following code runs in SWI prolog with monotonic enabled. 
% See the Sicstus version of the code for necessary comments.

%%% 0. THE MAIN PREDICATE %%%
reduced_thin_search( N, ThinTables ) :-
    M is 2**N-1,
    findall( Rows, (thin_search( Vs, N, M, Rows), label(Vs) ), FirstTables ),
    remove_non_simple_tables( FirstTables, SimpleTables ),
    lex_reduce_tables( N, SimpleTables, ReducedTables ),
    once(perform_toral_switchings( N, ReducedTables, ThinTables )).
%%%%%%

%%% 1. INITIAL THIN SEARCH %%%
thin_search( Vs, N, M, Rows) :-
	length(Rows, M),
	maplist(same_length(Rows),Rows),
	append(Rows, Vs), Vs ins 0..1,
	numlist(M, Indices),
	transpose(Rows, Rows),
	maplist( set_value_to_zero, Indices, Rows),
    stop_certain_ideals(Rows,Indices),
    act_faithfully(Rows,Indices),
	jacobi_identity_full( Indices, Rows),
	break_gl2_symmetries( Vs, Rows, N ).

% The Jacobi Identity 
jacobi_identity_full( Indices, Rows) :-
    findall( [A,B,C], ( append( [_,[A],_,[B],_,[C],_], Indices ),  A #\= (B xor C) ), Triples ),
    maplist( jacobi_identity( Rows ), Triples ).
jacobi_identity( Rows, [I1,I2,I3] ) :-
    #(I4) #= (#(I1) xor #(I2)),
    #(I5) #= (#(I1) xor #(I3)),
    #(I6) #= (#(I2) xor #(I3)),
    get_entry( Rows, [I1, I2], A ),
    get_entry( Rows, [I3, I4], B ),
    get_entry( Rows, [I1, I3], C ),
    get_entry( Rows, [I2, I5], D ),
    get_entry( Rows, [I2, I3], E ),
    get_entry( Rows, [I1, I6], F ),
	[G,H,I] ins 0..1,
    #(G) #>= #(A) + #(B) - 1,
    #(G) #=< #(A), 
    #(G) #=< #(B),
    #(H) #>= #(C) + #(D) - 1,
    #(H) #=< #(C), 
    #(H) #=< #(D),
    #(I) #>= #(E) + #(F) - 1,
    #(I) #=< #(E), 
    #(I) #=< #(F),
    #(G) + #(H) + #(I) #\= 1,
    #(G) + #(H) + #(I) #\= 3.

% Simplicity conditions 
stop_certain_ideals(Rows,Indices) :-
    make_L1_inds( Indices, L1s),
    maplist( check_L1_makes_L0(Rows, Indices), L1s ).
make_L1_inds( Indices, L1s) :-
    maplist( root_to_L1(Indices), Indices, L1s ).
root_to_L1(Indices, Root, L1 ) :-
    findall( A, ( member(A,Indices), #(B) #= (#(Root) /\ #(A)), dec2bin(B,Bin ), sum(Bin,#=,#(S)), (#(S) mod 2) #= 1), L1).
check_L1_makes_L0(Rows, Indices, L1) :-
    exclude( member_(L1), Indices, L0 ),
    maplist(is_made_check(Rows, L1), L0)
is_made_check( Rows, L1, A ) :-
    maplist( is_made_check_helper(Rows, A), L1, Entries ),
    sum( Entries, #>, 0 ).
is_made_check_helper( Rows, A, B, Entry ) :-
    #(C) #= (#(A) xor #(B)),
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
get_gl2( GL2 ) :- GL2 = [ [[1,0],[1,1]],[[1,1],[0,1]],[[1,1],[1,0]],[[0,1],[1,1]],[[0,1],[1,0]] ].

break_gl2_symmetries( Vs, Rows, N ) :-
    get_gl2( GL2 ),
    numlist( N, SimpleInds ),
    findall( [A,B], ( member(A, SimpleInds), member(B, SimpleInds), #(A) #< #(B) ), Pairs ), 
    get_roots( N, Roots ), 
    make_powers( N, Powers ),
    numlist( N, Indices ),
    maplist( break_gl2_symmetry( Vs, Rows, N, Indices, Roots, Powers, GL2), Pairs ).
break_gl2_symmetry( Vs, Rows, N, Indices, Roots, Powers, GL2, [J,K] ) :-
    maplist( add_to_gln_small( N, Indices, [J, K] ), GL2, SmallGLN ),
    maplist( make_perm(Roots,Powers), SmallGLN, RowPerms ),
    maplist( break_symmetry( Vs, Rows), RowPerms ). 

add_to_gln_small( N, Indices, [J,K], Mat1, NewMat ) :- 
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
    exclude( member_([J,K]), Indices, IdInds ),
    maplist( make_kth_row( Indices ), IdInds, Mat2 ),
    place_entry( J, Row4, Mat2, Mat3 ),
    place_entry( K, Row6, Mat3, NewMat ).

break_symmetry( Vs, Rows, RowPerm ) :-
    maplist(permute_rows(Rows), RowPerm, NewRows ),
    transpose(NewRows, TNewRows),
    maplist(permute_rows(TNewRows), RowPerm, NewerRows ),
    same_length( Vs, Ns ),
    append(NewerRows, Ns),
	lex_chain( [ Vs, Ns ] ).
%%%%%%

%%% 2. POST SEARCH SIMPLICTY CHECK %%%
remove_non_simple_tables( Tables, SimpleTables ) :-
    include( simple_check, Tables, SimpleTables ).
simple_check( Rows ) :-
	length( Rows, N ),
    numlist( N, Indices ),
    maplist( my_sum, Rows, RowSums ),
    sort( RowSums, UniqueRowSums ),
    maplist( plus(1), UniqueRowSums, IdealSizes ),
    maplist( check_for_ideals( Rows, Indices ), IdealSizes ).
check_for_ideals(Rows, Indices, IdealSize ) :-
    S is IdealSize - 1,
    include( check_for_ideal_helper( Rows, S ), Indices, CorrectRankRoots ),
    findall( I, ( length( I, IdealSize), subset_set( I, CorrectRankRoots ) ), PossibleIdeals ),
    maplist( check_ideal( Rows ), PossibleIdeals ).
check_for_ideal_helper( Rows, S, I ) :-
    nth1( I, Rows, Row ), 
    sum( Row, #=, #(S) ).
check_ideal( Rows, PossibleIdeal ) :-
    maplist( check_ideal_helper( Rows, PossibleIdeal ), PossibleIdeal, Mat ),
    append( Mat, Ms ),
    sum( Ms, #=, #(Tot) ),
    length( PossibleIdeal, N ),
    M is N^2 - N,
    #(Tot) #\= #(M).
check_ideal_helper( Rows, PossibleIdeal, X, Row ) :-
    maplist( check_ideal_helperer( Rows, X ), PossibleIdeal, Row ).
check_ideal_helperer( _, X, X, Entry ) :-
    #(Entry) #= 0.
check_ideal_helperer( Rows, X, Y, Entry ) :-
    #(X) #\= #(Y),
    #(I) #= ( #(X) xor #(Y) ),
    get_entry( Rows, [I,X], Entry).
%%%%%%

%%% 3. LEX REDUCE TABLES %%%
lex_reduce_tables( N, SimpleTables, ReducedTables ) :-
    populate_row_sum_tables_list( SimpleTables, TablesList ),
    maplist( lex_reduce(N), TablesList, ReducedTablesList ),
    append( ReducedTablesList, ReducedTables ).


lex_reduce( N, List, ReducedList ) :-
    lex_reduce( N, List, [], ReducedList).
lex_reduce( _, [], Mins, ReducedList) :- 
    ReducedList = Mins.
lex_reduce( _, List, Mins, ReducedList) :-
    length( List, 1 ),
    append( Mins, List, ReducedList ).
lex_reduce( N, List, Mins, ReducedList) :-
    length( List, K ),
    #(K) #> 1,
    min_member( my_lex, MinTable, List ),
    sorted_row_sums( MinTable, SortedRowSums ),
    get_roots( N, Roots ),
    make_powers( N, Powers ),
    findall( Table, (member(Table, List), \+ can_permute_dispatcher( N, Roots, Powers, MinTable, Table, SortedRowSums) ), NewList ),
    append( Mins, [MinTable], NewMins ),
    lex_reduce( N, NewList, NewMins, ReducedList).

populate_row_sum_tables_list( SimpleTables, TablesList ) :-
    maplist( full_sorted_row_sums, SimpleTables, TooManyRowSums ),
    list_to_set( TooManyRowSums, RowSumsList ),
    maplist( filter_by_row_sum(SimpleTables), RowSumsList, TablesList ).
filter_by_row_sum( SimpleTables, RowSums, Tables ) :-
    include( filter_by_row_sum_helper(RowSums), SimpleTables, Tables).

my_lex( A, B ) :-
    append( A, As ),
    append( B, Bs ),
    lex_chain( [As, Bs] ).
%%%%%%

%%% 4. TORAL SWITCHING %%%
perform_toral_switchings( N, Tables, SwitchedTables ) :-
    M is 2**N-1,
    K is 2**(N-1),
    numlist( M, Indices ),
    get_roots( N, Roots ),
    make_powers( N, Powers ),    
    maplist(locate_basis_nilps( Indices, K ), Tables, NilpIndicesList ),
    make_base_torus( BaseTorus, N, Indices ),
    findall( [A,B], ( member(A, Indices), member(B, Indices), #(A) #< #(B) ), Pairs ), 
    maplist( make_torus_switches( Indices, Pairs, Roots, BaseTorus ), Tables, NilpIndicesList, SwitchedTablesList ),
    once(canonical_order_tables_list( N, Roots, Powers, Tables, SwitchedTablesList, OrderedTablesList )), 
    once(make_adjacency_mat( Tables, OrderedTablesList, AdjacencyMat )),
    adjacency_mat_to_ugraph( AdjacencyMat, SwitchingGraph ),
    conn_comps( SwitchingGraph, Comps ),
    maplist( get_min_from_comp( Tables ), Comps, SwitchedTables ).

locate_basis_nilps( Indices, K, Rows, NilpIndices ) :-
    include( locate_basis_nilps_helper( Rows, K ), Indices, NilpIndices ).
locate_basis_nilps_helper( Rows, K, I ) :-
    nth1( I, Rows, Row ), 
    sum( Row, #<, #(K) ).

make_base_torus( BaseTorus, N, Indices ) :-
    length( BaseTorus, N ),
    numlist( N, SmallIndices ),
    maplist( make_base_torus_row( Indices ), SmallIndices, BaseTorus ).
make_base_torus_row( Indices, RowIndex, BaseTorusRow ) :-
    RootIndex is 2**(RowIndex - 1),
    maplist( make_base_torus_entry( RootIndex ), Indices, BaseTorusRow ).
make_base_torus_entry( RootIndex, ColIndex, Entry ) :-
    ( #(RootIndex) /\ #(ColIndex) ) #= 0,
    #(Entry) #= 0.
make_base_torus_entry( RootIndex, ColIndex, Entry ) :-
    ( #(RootIndex) /\ #(ColIndex) ) #= #(RootIndex),
    #(Entry) #= 1.

make_torus_switches( _, _, _, _, _, [], SwitchedTables ) :-
    SwitchedTables = [].
make_torus_switches( Indices, Pairs, Roots, BaseTorus, Table, NilpIndices, SwitchedTables ) :-
    length( NilpIndices, K ),
    #(K) #> 0,
    maplist( switch_torus( Indices, Pairs, Table, BaseTorus, Roots), NilpIndices, SwitchedTables ).
switch_torus( Indices, Pairs, Table, BaseTorus, Roots, NilpIndex, SwitchedTable ) :-
    maplist( modify_toral_element_checker( NilpIndex ), BaseTorus, ModifyToralElementChecker ),
    maplist( make_new_basis( Indices, Table, BaseTorus, NilpIndex, ModifyToralElementChecker), Roots, NewBasis ),
    make_new_table( Indices, Pairs, Table, NewBasis, SwitchedTable ).

modify_toral_element_checker( NilpIndex, ToralRow, ModifyToralElement ) :-
    nth1( NilpIndex, ToralRow, ModifyToralElement ).

make_new_basis( Indices, Table, BaseTorus, NilpIndex, ModifyToralElementChecker, Root, NewBasisElement ) :-
    same_length( Table, NewBasisElement ),
    NewBasisElement ins 0..1,
    once( make_new_basis_helper( Indices, Table, BaseTorus, NilpIndex, ModifyToralElementChecker, Root, NewBasisElement ) ),
    label(NewBasisElement).
make_new_basis_helper( Indices, Table, BaseTorus, NilpIndex, ModifyToralElementChecker, Root, NewBasisElement ) :-
    sum( NewBasisElement, #>, 0 ),
    maplist( apply_root_value( Indices, Table, NilpIndex, NewBasisElement), BaseTorus, ModifyToralElementChecker, Root ).
    
apply_root_value( Indices, Table, NilpIndex, NewBasisElement, ToralRow, ModifyToralElement, RootVal ) :-
    maplist( times, ToralRow, NewBasisElement, TorusOnElement),
    nth1( NilpIndex, Table, NilpRow ),
    maplist( nilp_on_element(NilpRow, NewBasisElement, NilpIndex), Indices, NilpOnElement ),
    maplist( times(ModifyToralElement), NilpOnElement, ScaledNilpOnElement ),
    maplist( sum_mod_2, TorusOnElement, ScaledNilpOnElement, ActedOnElement ),
    maplist( times(RootVal), NewBasisElement, ScaledNewBasisElement ),
    maplist( eq, ScaledNewBasisElement, ActedOnElement).
nilp_on_element(_, _, NilpIndex, NilpIndex, NilpOnElementEntry ) :-
    #(NilpOnElementEntry) #= 0.
nilp_on_element(NilpRow, NewBasisElement, NilpIndex, Index, NilpOnElementEntry ) :-
    NilpIndex #\= Index,
    #(NewIndex) #= (NilpIndex xor Index),
    nth1( NewIndex, NewBasisElement, V),
    nth1( NewIndex, NilpRow, NilpOnElementEntry0 ),
    #(NilpOnElementEntry) #= #(NilpOnElementEntry0) * #(V).

make_new_table( Indices, Pairs, Table, NewBasis, NewTable ) :-
    maplist( set_diagonal( NewTable ), Indices ),
    maplist( intify_basis(Indices), NewBasis, IntBasis ),
    same_length( Table, NewTable ),
    maplist( same_length(NewTable), NewTable ),
    maplist( make_new_table_entry( Indices, Table, IntBasis, NewTable ), Pairs ).

make_new_table_entry( Indices, Table, IntBasis, NewTable, [I1, I2] ) :-
    nth1( I1, IntBasis, Ints1 ),
    nth1( I2, IntBasis, Ints2 ),
    #(I3) #= ( #(I1) xor #(I2) ),
    nth1( I3, IntBasis, Ints3 ),
    nth1( 1, Ints3, MainInt ),
    maplist( make_xor_pair(MainInt), Indices, XORPairs ),
    include( filter_xor_pairs( Ints1, Ints2 ), XORPairs, FilteredPairs ), 
    get_entries( Table, FilteredPairs, Entries ),
    sum( Entries, #=, #(Tot) ),
    #(Val) #= ( #(Tot) mod 2 ),
    get_entry( NewTable, [I1, I2], Val ),
    get_entry( NewTable, [I2, I1], Val ).
filter_xor_pairs( Ints1, Ints2, [I, J] ) :-
    member(I, Ints1),
    member(J, Ints2).
make_xor_pair( A, B, [C,D] ) :-
    #(C) #= #(B),
    #(D) #= ( #(A) xor #(B)).
intify_basis( Indices, BasisRow, Ints ) :-
    include( intify_basis_helper(BasisRow), Indices, Ints ).
intify_basis_helper( BasisRow, I ) :-
    nth1( I, BasisRow, 1 ).
set_diagonal( NewTable, I ) :-
    get_entry( NewTable, [I,I], 0 ).

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
    #(K) #> 0,
    maplist(canonical_order_rows( N, Roots, Powers, SimpleTablesWithSums ), Tables, OrderedTables).
canonical_order_rows( N, Roots, Powers, SimpleTablesWithSums, Rows, OrderedRows) :-
    full_sorted_row_sums( Rows, RowSums),
    sort( RowSums, SortedRowSums),
    findall( Table, ( member(TableWithSums, SimpleTablesWithSums), TableWithSums = [ Table, RowSums ] ), SimpleTables ),
    first_sol( lex_reduce_to_simple( N, Roots, Powers, Rows, SortedRowSums ), SimpleTables, OrderedRows ).
lex_reduce_to_simple( N, Roots, Powers, Rows, SortedRowSums, Table ) :-
    can_permute_dispatcher( N, Roots, Powers, Rows, Table, SortedRowSums).


make_adjacency_mat( Tables, OrderedTablesList, AdjacencyMat ) :-
	length( Tables, M ),
    numlist( M, Indices ),
    maplist( make_adjacency_row( Tables, OrderedTablesList, Indices ), Indices, Mat ),
    transpose( Mat, TMat),
    maplist(maplist( my_max ), Mat, TMat, AdjacencyMat).
make_adjacency_row( Tables, OrderedTablesList, Indices, RowIndex, AdjacencyRow ) :-
    maplist( make_adjacency_entry( Tables, OrderedTablesList, RowIndex ), Indices, AdjacencyRow ).
make_adjacency_entry( _, _, RowIndex , RowIndex, AdjacencyEntry ) :-
    #(AdjacencyEntry) #= 0.
make_adjacency_entry( Tables, OrderedTablesList, RowIndex , ColIndex, AdjacencyEntry ) :-
    #(RowIndex) #\= #(ColIndex),
    nth1( RowIndex, Tables, Table ),
    nth1( ColIndex, OrderedTablesList, TableList ),
    set_adjacency_entry( Table, TableList, AdjacencyEntry ).
set_adjacency_entry( Table, TableList, AdjacencyEntry ) :-
    (   member( Table, TableList ),
        #(AdjacencyEntry) #= 1
    ;   #(AdjacencyEntry) #= 0
    ).
adjacency_mat_to_ugraph( A, G ) :-
    length( A, N ),
    numlist(N, Indices),
    maplist( collect_nbrs(A,Indices), Indices, NbrsList ), 
    maplist( make_vertex, Indices, NbrsList, G ).
make_vertex( Index, Nbrs, V ) :-
    V = Index-Nbrs.
collect_nbrs(A, Indices, Index, Nbrs ) :-
    nth1( Index, A, Row ),
    findall( X, ( member( X, Indices ), nth1( X, Row, 1 ) ), Nbrs).

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
    (   member(Index, A), B = A
    ;   append( [A, [Index]], B )
    ).
get_min_from_comp( Tables, Comp, MinTable ) :-
    get_values( Tables, Comp, CompTables ),
    min_member( my_lex, MinTable, CompTables ).
%%%%%%

%%% 5. SYMMETRY PREDICATES %%%

make_perm(Roots,Powers, Mat, RowPerm ) :-
    maplist( perm_it(Powers, Mat), Roots, RowPerm ).
perm_it(Powers, Mat, Root, Entry ) :-
    act_mat(Mat, Root, RootOut),
    bin_2_dec(Powers, RootOut, Entry).

permute_rows(Rows, PermIndex, NewRow ) :-
    nth1( PermIndex, Rows, NewRow).

can_permute_dispatcher( N, Roots, Powers, Table1, Table2, SortedRowSums ) :-
    length( Mat, N ),
	maplist(same_length(Mat), Mat),
    once(can_permute( N, Roots, Powers, Table1, Table2, Mat, SortedRowSums ) ).
can_permute( N, Roots, Powers, T1, T2, Mat, SortedRowSums ) :-
    length( Mat, N ),
	append(Mat,Ms), Ms ins 0..1,
    partition_by_row_sums( T1, SortedRowSums, Partition1 ),
    partition_by_row_sums( T2, SortedRowSums, Partition2 ),
    maplist( map_partitions(N, Mat, Powers), Partition1, Partition2 ),
    make_perm( Roots, Powers, Mat, RowPerm ),
    maplist(permute_rows(T2), RowPerm, NewRows ),
    transpose(NewRows, TNewRows),
    maplist(permute_rows(TNewRows), RowPerm, T1 ).
map_partitions( N, Mat, _, L1, L2 ) :-
    length( L1, 1 ),
    Rank is N,
    nth1( 1, L1, N1 ),
    nth1( 1, L2, N2 ),
    dec_2_bin( Rank, N1, B1 ),
    dec_2_bin( Rank, N2, B2 ),
    act_mat( Mat, B1, B2 ).
map_partitions( N, Mat, Powers, L1, L2 ) :-
    length( L1, K ),
    #(K) #> 1,
    Rank is N,
    maplist( dec_2_bin( Rank ), L1, Domain ),
    maplist( set_range( Mat, Powers, L2 ), Domain ).
set_range( Mat, Powers, Range, B1 ) :-
    act_mat( Mat, B1, B2 ),
    bin_2_dec( Powers, B2, D ),
    element( _, Range, D ).
partition_by_row_sums( Mat, SortedRowSums, Partition ) :-
    maplist( has_row_sum( Mat ), SortedRowSums, Partition ).
has_row_sum( Mat, S, L ) :-
    findall( I, ( nth1( I, Mat, R ), sum( R, #=, #(S) ) ), L ).

filter_by_row_sum_helper( RowSums, Table) :-
    full_sorted_row_sums( Table, RowSums ).
sorted_row_sums( M, Sorted ) :-
    maplist( my_sum, M, Sums ),
    sort( Sums, Sorted ).
full_sorted_row_sums( M, Sorted ) :-
    maplist( my_sum, M, Sums ),
    msort( Sums, Sorted ).
%%%%%%

%%% 6. UTILITY PREDICATES %%%
plus(X,Y,Z) :- #(Z) #= #(X) + #(Y).
eq(A,B) :- #(A) #= #(B).
notEqual(A,B) :- #(A) #\= #(B).
equal_to_zero( X ) :- #(X) #= 0.
sum_mod_2( A, B, C ) :- ((#(A) + #(B)) mod 2 ) #= #(C).
times(A,B,C) :- #(C) #= #(A) * #(B).

my_sum( Elems, Tot ) :-
    sum( Elems, #=, #(Tot) ).

my_max( A, B, C ) :-
    #(A) #< #(B),
    #(C) #= #(B).
my_max( A, B, C ) :-
    #(A) #>= #(B),
    #(C) #= #(A).

set_value_to_zero( Index, Row ) :-
    nth1( Index, Row, 0).

get_value( Row, Index, Value ) :-
    nth1( Index, Row, Value).
get_values( Row, Indices, Values ) :-
    maplist( get_value(Row), Indices, Values ).
get_entry( Rows, [RowIndex, ColIndex], Entry ) :-
    nth1( RowIndex, Rows, Row),
    nth1( ColIndex, Row, Entry).
get_entries( Rows, Indices, Entries ) :-
    maplist( get_entry(Rows), Indices, Entries ).

make_powers(N, Powers) :-
    make_powers0(N, Roots),
    reverse(Roots, Powers).
make_powers0(N, Roots) :-
    numlist(N, Indices),
    maplist(make_powers_helper, Indices, Roots).  
make_powers_helper(Ind, Root) :-
    Val is 2^(Ind - 1),
    #(Root) #= #(Val).

dec_2_bin(Rank,N,L) :-
    dec2bin(N, L0),
    length(L0,K),
    length(L,Rank),
    M is Rank - K,
	findall(0, between(1, M, _), Zs),
    append(Zs, L0, L).
dec2bin(0,[0]).
dec2bin(1,[1]).
dec2bin(N,L):- 
    N > 1,
    X is N mod 2,
    Y is N // 2,  
    dec2bin(Y,L1), 
    append(L1, [X], L).
bin_2_dec(Powers, L, N) :-
    maplist(times, Powers, L, P),
    sum(P,#=,#(N)).

member_( L, E ) :- 
    member( E, L ).

get_roots(N, Roots) :-
    findall( L, ( length( L, N ), L ins 0..1, label(L) ), RootsZ ),
	RootsZ = [ _ | Roots ].
get_gln(N,Roots,GLN) :-
	length(Mat,N),
	maplist(same_length(Mat),Mat),
	append(Mat,Vs),
	Vs ins 0..1,
	findall(Mat,(mat_in_gln(Mat,Roots),label(Vs)),GLN).
mat_in_gln(Mat,Roots) :-
	maplist(vec_not_in_ker_mat(Mat),Roots).
vec_not_in_ker_mat(Mat,VecIn) :-
	same_length(VecIn,VecOut), 
	VecOut ins 0..1,
	act_mat(Mat,VecIn,VecOut),
	sum(VecOut,#>,0).
act_mat(Mat, VecIn, VecOut) :- % NB VecIn cannot have variables
	maplist(my_scalar_prod(VecIn),Mat,VecOut).
my_scalar_prod(V1,M1,X) :- 
    same_length(V1,Prods),
    maplist(times,V1,M1,Prods),
    sum(Prods,#=,#(Y)), 
    (#(Y) mod 2) #= #(X).

make_kth_row( Indices, K, KthRow ) :-
    maplist( set_kth_row( K ), Indices, KthRow ).
set_kth_row(  K, K, Entry ) :- 
   #(Entry) #= 1.
set_kth_row(  K, Index, Entry ) :- 
    #(Index) #\= K, 
    #(Entry) #= 0. 
row_of_n_zeros( N, Row ) :-
    length( Row, N ),
    maplist( equal_to_zero, Row ).
place_entry( Ind, Entry, X, Y ) :- 
    L is Ind - 1,
    length( A, L ),
    append( A, B, X ),
    append( [ A, [Entry], B ], Y ).

first_sol(Goal, List, Sol) :-
    first_sol_(List, Goal, Sol).
first_sol_([], _, []).
first_sol_([X1|Xs1], P, Sol) :-
    (   call(P, X1) ->  Sol = X1
    ;   first_sol_(Xs1, P, Sol )
    ).

subset_set([], _).
subset_set([X|Xs], S) :-
    append(_, [X|S1], S),
    subset_set(Xs, S1).

numlist( N, Xs ) :-
    numlist( 1, N, Xs ).
%%%%%%

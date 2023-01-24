:-use_module(library(clpfd) ).
:-use_module(library(lists)).
:-use_module(library(samsort)).
:-use_module(library(ordsets)).
:-use_module(library(ugraphs)).
:-use_module(library(between)).

% The following predicate reduced_thin_search is our main predicate for searching for simple thin Lie algebras.
% The parameter N is inputted by the users. The output is ThinTables which is a list of NxN arrays. Each of which represents a thin Lie algebra of dimension 2^N - 1
% For N = 2,3,4,5 each member of ThinTables represents a simple Lie algebra. We confirm this using graph
% For N >= 4 there are different members of ThinTables that represent the same Lie algebra. See the main body of the paper for does_not_centralise
% reduced_thin_search consists of the following 4 main parts

% 1. INITIAL THIN SEARCH

% The predicate thin_search generates FirstTables which consists of a list of tables each representing a thin Lie algebra
% thin_search itself consists of three main componenets:
% a. Implement the Lie bracket as constraints so that each table produced represents a valid Lie algebra
% b. Constraints which are necessary for simplicity of the represented Lie algebras via the predicates
% stop_certain_ideals and act_faithfully. See the paper for the theoretical underpinning of these constraints.
% c. Symmetry breaking constraints via the predicate break_gl2_symmetries. These constraints removes some tables
% which represent the same Lie algebra. Not all possible symmetries can be added as constraints due to times
% and memory issues.

% Note that the order of the predicates inside thin_search do not follow the order listed above.
% The order constraints are added impact the run time. We have optimised the ordering.

% 2. POST SEARCH SIMPLICTY CHECK
% The predicate remove_non_simple_tables takes in the tables FirstTables and removes certain tables representing
% non simple Lie algebras. See the paper for a description of what ideals are checked for .
% The tables which pass this check are represented by SimpleTables.
% In theory this condition could have been converted to a constraint and added to thin_search.
% However doing this is significantly slower than performing them as a post process.

% 3. LEX REDUCE TABLES

% As mentioned in 1. the predicate break_gl2_symmetries does not implement all possible symmetries as constraints.
% We now implement the rest of these symmetries on the tables SimpleTables and output the results to ReducedTables.
% At this stage no two tables in ReducedTables can be transformed in to each other via permutations of roots.

% 4. TORAL SWITCHING

% We now remove further tables from ReducedTables representing the same Lie alegbra.
% For each table in ReducedTables we perform one toral switch for each nilpotent basis element in that table.
% A graph is then constructed with vertex set represented by the elements of ReducedTables
% and an edge between two vertices if a toral switch transformed the tables represented by the two vertices in to one another.
% For each connected componenet of this graph we take one table from it and output these to ThinTables.
% In addition to the above sections we have the following two sections that collect shared predicates used throughout the code

% 5. SYMMETRY PREDICATES

% These are a collection of predicates used throughout the code that deal with permuting roots.

% 6. UTILITY PREDICATES

% These are a collection of generic predicates used throughout the code.
% An example prompt to run the main predicate is
% ['ThinSymmetrySicstus.pl'].
% reduced_thin_search(4, ThinTables), maplist( writeln, ThinTables).

%%% 0. THE MAIN PREDICATE %%%

reduced_thin_search( N, ThinTables ) :-
        preprocess(N),
        statistics(runtime, _),
        findall( Rows, (thin_search( Vs, N, Rows), labeling( [], Vs) ), FirstTables ),
        statistics(runtime, [_,T1]),
        length(FirstTables, N1), print_message(informational, format('~w FirstTables in ~w ms',[N1,T1])),
        remove_non_simple_tables( FirstTables, SimpleTables ),
        statistics(runtime, [_,T2]),
        length(SimpleTables, N2), print_message(informational, format('~w SimpleTables in ~w ms',[N2,T2])),
        lex_reduce_tables( N, SimpleTables, ReducedTables ),
        statistics(runtime, [_,T3]),
        length(ReducedTables, N3), print_message(informational, format('~w ReducedTables in ~w ms',[N3,T3])),
        once(perform_toral_switchings( N, ReducedTables, ThinTables )),
        statistics(runtime, [_,T4]),
        length(ThinTables, N4), print_message(informational, format('~w ThinTables in ~w ms',[N4,T4])),
        findall(Nones, (member(Th,ThinTables), member(R,Th), sumlist(R,Nones)), Noness),
        sort(Noness, NonesSet),
        print_message(informational, format('ThinTable #1s in ~w',[NonesSet])).
%%%%%%

%%% 1. INITIAL THIN SEARCH %%%

thin_search( Vs, N, Rows) :-
        M is 2^N-1,
        length(Rows, M),
        numlist(M, Indices),
        maplist(same_length(Rows),Rows),
        append(Rows, Vs),
        domain( Vs, 0, 1),
        transpose(Rows, Rows),  % Lie Bracket constraint
        maplist( set_value_to_zero, Indices, Rows), % Lie Bracket constraint
        stop_certain_ideals(Rows,Indices), % Simplicity constraints
        act_faithfully(Rows,Indices),      % Simplicity constraints
        jacobi_identity_full( Indices, Rows), % Lie Bracket constraint
        break_gl2_symmetries( Vs, Rows, N ), % Symmetry breaking constraints
        maplist(number_of_ones(N), Rows),    % Implied constraint
        maplist(lemma_2_12(N, Indices), Indices, Rows), % Implied constraint
        true.

number_of_ones(N, Row) :-
        (   N = 3 -> Dom = {3,4,5}
        ;   N = 4 -> Dom = {4,6,7,8,10,11}
        ;   N = 5 -> Dom = {5,8,9,12,14,15,16,20,23}
        ;   true  -> Max is 2^(N-1) + 2^(N-2) - 1,
                     Dom = (1..Max)
        ),
        S in Dom,
        sum(Row, #=, S).

lemma_2_12(N, Indices, I, Row) :-
        Pow1 is 2^(N-1),
        (   foreach(J,Indices),
            foreach(MJ,Row),
            fromto(A2,A3,A4,[]),
            param(I,Row)
        do  (   I = J -> A3 = A4
            ;   IJ is xor(I,J),
                fast_nth1(IJ, Row, MIJ),
                X #<=> MJ #/\ MIJ,
                A3 = [X|A4]
            )
        ),
        sum(A2, #=, S),
        (N =< 5 -> S in {0,Pow1} ; S in {0} \/ (18..Pow1)).

%% The Jacobi Identity
jacobi_identity_full( Indices, Rows) :-
        jacobi_triples(Indices, Triples, []),
        maplist( jacobi_identity( Rows ), Triples, Tuples ),
        gen_jacobi_extension(Extension),
        table(Tuples, Extension).
% jacobi_identity_full( Indices, Rows) :-
%         jacobi_triples(Indices, Triples, []),
%         maplist( jacobi_identity( Rows ), Triples, Tuples ),
%         maplist( jacobi_subtuple, Tuples ).

jacobi_triples(Indices) -->
        (   foreach(A,Indices),
            param(Indices)
        do  (   foreach(B,Indices),
                param(A,Indices)
            do  (   {A < B}
                ->  (   foreach(C,Indices),
                        param(A,B)
                    do  ({B < C, A =\= xor(B,C)} -> [[A,B,C]] ; [])
                    )
                ;   []
                )
            )
        ).

jacobi_identity( Rows, [I1,I2,I3], [A,B,C,D,E,F]) :-
        I4 is xor(I1, I2),
        I5 is xor(I1, I3),
        I6 is xor(I2, I3),
        get_entry( Rows, [I1, I2], A ),
        get_entry( Rows, [I3, I4], B ),
        get_entry( Rows, [I1, I3], C ),
        get_entry( Rows, [I2, I5], D ),
        get_entry( Rows, [I2, I3], E ),
        get_entry( Rows, [I1, I6], F ).

gen_jacobi_extension(Extension) :-
        jacobi_subtuple(SubTuple),
        findall(SubTuple, labeling([], SubTuple), Extension).

% jacobi_subtuple([A,B,C,D,E,F]) :-
%         Tuple = [A,B,C,D,E,F,G,H,I],
%         domain(Tuple, 0, 1),
%         G #>= A + B - 1,
%         G #=< A,
%         G #=< B,
%         H #>= C + D - 1,
%         H #=< C,
%         H #=< D,
%         I #>= E + F - 1,
%         I #=< E,
%         I #=< F,
%         G + H + I #\= 1,
%         G + H + I #\= 3.
jacobi_subtuple([A,B,C,D,E,F]) :-
        (A #/\ B) #\ (C #/\ D) #\ (E #/\ F) #\ 1.

%% Simplicity conditions
stop_certain_ideals(Rows,Indices) :-
        make_L1_inds( Indices, L1s),
        maplist( check_L1_makes_L0(Rows, Indices), L1s ).

make_L1_inds( Indices, L1s) :-
        maplist( root_to_L1(Indices), Indices, L1s ).

root_to_L1(Indices, Root, L1 ) :-
        (   foreach(A,Indices),
            fromto(L1,L2,L3,[]),
            param(Root)
        do  B is Root /\ A,
            (dec_is_odd_bin(B) -> L2 = [A|L3] ; L2 = L3)
        ).

check_L1_makes_L0(Rows, Indices, L1) :-
        ord_subtract(Indices, L1, L0),
        maplist(is_made_check(Rows, L1), L0).

is_made_check( Rows, L1, A ) :-
        maplist( is_made_check_helper(Rows, A), L1, Entries ),
        at_least_one( Entries ).

is_made_check_helper( Rows, A, B, Entry ) :-
        C is xor(A, B),
        get_entry( Rows, [B,C], Entry ).

act_faithfully( Rows, Indices ) :-
        make_L1_inds( Indices, L1s ),
        maplist( check_L0_acts_faithfully( Rows, Indices ), L1s ).

check_L0_acts_faithfully( Rows, Indices, L1 ) :-
        ord_subtract(Indices, L1, L0),
        maplist(does_not_centralise(Rows, L1), L0).

does_not_centralise( Rows, L1, X ) :-
        maplist( does_not_centralise_helper( Rows, X ), L1, Entries ),
        at_least_one( Entries ).

does_not_centralise_helper( Rows, X, A, Entry ) :-
        get_entry( Rows, [A,X], Entry ).

%%% Symmetry breaking code %%%

%% gl_2 is hardcoded due to its small size
get_gl2( GL2 ) :-
        GL2 = [ [[1,0],[1,1]],[[1,1],[0,1]],[[1,1],[1,0]],[[0,1],[1,1]],[[0,1],[1,0]] ].

%% For each pair of simple roots and each element of gl_2
%% create a symmetry breaking constrint
break_gl2_symmetries( Vs, Rows, N ) :-
        get_gl2( GL2 ),
        all_pairs_le_n(N, Pairs, []),
        maplist( break_gl2_symmetry( Vs, Rows, N, GL2), Pairs ).

all_pairs_le_n(N) -->
        (   for(I,1,N),
            param(N)
        do  (   for(J,I+1,N),
                param(I)
            do  [[I,J]]
            )
        ).

break_gl2_symmetry( Vs, Rows, N, GL2, [J,K] ) :-
        maplist( add_to_gln_small( N, [J, K] ), GL2, SmolGLN ),
        get_roots(N,Roots),
        make_powers(N,Powers),
        maplist( make_perm(Roots,Powers), SmolGLN, RowPerms ),
        maplist( break_symmetry( Vs, Rows), RowPerms ).

%% Create the subset of gl_n we create constraints for
add_to_gln_small( N, [J,K], Mat1, NewMat ) :-
        M is N - 2,
        row_of_n_zeros( M, ZeroRow ),
        Mat1 = [Row1,Row2|_],
        Row1 = [A,B|_],
        Row2 = [C,D|_],
        place_entry( J, A, ZeroRow, Row3 ),
        place_entry( K, B, Row3, Row4 ), % Place this at pos J
        place_entry( J, C, ZeroRow, Row5 ),
        place_entry( K, D, Row5, Row6 ), % Place this at pos K
        numlist( N, Indices ),
        ord_subtract(Indices, [J,K], IdInds),
        maplist( make_kth_row( Indices ), IdInds, Mat2 ),
        place_entry( J, Row4, Mat2, Mat3 ),
        place_entry( K, Row6, Mat3, NewMat ).




%% Create the symmetry breaking constraint
%% RowPerm is a permutation generated by an element of gl_n
%% RowPerm is applied to the rows and columns of Row to obtain NewerRows
%% Add the constraint that Rows is lexicographically lower than NewerRows
break_symmetry( Vs, Rows, RowPerm ) :-
        maplist(permute_rows(Rows), RowPerm, NewRows ),
        transpose(NewRows, TNewRows),
        maplist(permute_rows(TNewRows), RowPerm, NewerRows ),
        same_length( Vs, Ns ),
        append(NewerRows, Ns),
        lex_chain( [ Vs, Ns ] ).
%%%%%%

%%% 2. POST SEARCH SIMPLICTY CHECK %%%

%% Search for certain non-trivial ideals for each table in Tables
%% See paper for explanation
remove_non_simple_tables( Tables, SimpleTables ) :-
        include( simple_check, Tables, SimpleTables ).

simple_check( Rows ) :-
        length( Rows, N ),
        numlist( N, Indices ),
        maplist( sumlist, Rows, RowSums ),
        sort( RowSums, UniqueRowSums ),
        (   foreach(B,UniqueRowSums),
            foreach(A,IdealSizes)
        do  A is B+1
        ),
        maplist( check_for_ideals( Rows, Indices ), IdealSizes ).

check_for_ideals(Rows, Indices, IdealSize ) :-
        (   foreach(A1,Indices),
            fromto(CorrectRankRoots,CRR1,CRR2,[]),
            param(Rows,IdealSize)
        do  fast_nth1(A1, Rows, Row),
            sumlist(Row, S),
            (S is IdealSize-1 -> CRR1 = [A1|CRR2] ; CRR1 = CRR2)
        ),
        length(CorrectRankRoots, NRoots),
        (   IdealSize > NRoots -> PossibleIdeals = []
        ;   IdealSize = NRoots -> PossibleIdeals = [CorrectRankRoots]
        ;   length( A, IdealSize),
            findall( A, subseq0( CorrectRankRoots, A ), PossibleIdeals )
        ),
        maplist( check_ideal( Rows ), PossibleIdeals ).

check_ideal( Rows, PossibleIdeal ) :-
        \+maplist( check_ideal_helper(Rows, PossibleIdeal), PossibleIdeal ).

check_ideal_helper( Rows, PossibleIdeal, X ) :-
        maplist( check_ideal_helper_2( Rows, X), PossibleIdeal ).

check_ideal_helper_2( Rows, X, Y ) :-
        (   X = Y -> true
        ;   I is xor(X,Y),
            get_entry( Rows, [I,X], 1)
        ).
%%%%%%

%%% 3. LEX REDUCE TABLES %%%

%% Remove all tables from SimpleTables that are not in their lexicographically min form
lex_reduce_tables( N, SimpleTables, ReducedTables ) :-
        get_roots( N, Roots ),
        make_powers( N, Powers ),
                                % For each table calculate its row sums and partition SimpleTables based on this
        populate_row_sum_tables_list( SimpleTables, TablesList ),
                                % For each list of tables remove tables not in lexicographically min form
        maplist( lex_reduce(N, Roots, Powers), TablesList, ReducedTablesList ),
                                % Combine ReducedTablesList in to ReducedTables
        append( ReducedTablesList, ReducedTables ).

%% Recursively generate ReducedList from List
%% 1. Add the element of List with min lexicographical order to ReducedList, call this MinTable
%% 2. Remove all elements equivalement to MinTable via row permutations from List
%% 3. Repeat 1. and 2. until List is empty
lex_reduce( N, Roots, Powers, List, ReducedList ) :-
        lex_reduce( N, Roots, Powers, List, [], ReducedList).

lex_reduce( _, _, _, [], Mins, ReducedList) :- !,
        ReducedList = Mins.
lex_reduce( _, _, _, List, Mins, ReducedList) :-
        length( List, 1 ), !,
        append( Mins, List, ReducedList ).
lex_reduce( N, Roots, Powers, List, Mins, ReducedList) :-
        min_member(MinTable, List ),
        sorted_row_sums( MinTable, SortedRowSums ),
        exclude( can_permute_dispatcher( N, Roots, Powers, SortedRowSums, MinTable), List, NewList ),
        append( Mins, [MinTable], NewMins ),
        lex_reduce( N, Roots, Powers, NewList, NewMins, ReducedList).

%% Calculate row sums and partition with respect to row sums
populate_row_sum_tables_list( SimpleTables, TablesList ) :-
        maplist( full_sorted_row_sums, SimpleTables, TooManyRowSums ),
        list_to_ord_set( TooManyRowSums, RowSumsList ),
        maplist( filter_by_row_sum(SimpleTables), RowSumsList, TablesList ).

filter_by_row_sum( SimpleTables, RowSums, Tables ) :-
        (   foreach(Table,SimpleTables),
            fromto(Tables,T1,T2,[]),
            param(RowSums)
        do  (   full_sorted_row_sums( Table, RowSums ) -> T1 = [Table|T2] ; T1 = T2   )
        ).
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
        all_ordered_pairs(Indices, Pairs, []),
                                % Make a torus switch for each nilpotent basis element
        maplist( make_torus_switches( Indices, Pairs, Roots, BaseTorus ), Tables,
                 NilpIndicesList, SwitchedTablesList ),
                                % Lexicographically reduce each switched table
        once(canonical_order_tables_list( N, Roots, Powers, Tables, SwitchedTablesList,
                                          OrderedTablesList )),
                                % Make the graph based on toral switchings. See paper for details
        once(make_adjacency_mat( Tables, OrderedTablesList, AdjacencyMat )),
        adjacency_mat_to_ugraph( AdjacencyMat, SwitchingGraph ),
        conn_comps( SwitchingGraph, Comps ),
                                % Return one table per connected componenet of the graph
        maplist( get_min_from_comp( Tables ), Comps, SwitchedTables ).

all_ordered_pairs(Indices) -->
        (   fromto(Indices,[A|Tail],Tail,[])
        do  (   foreach(B,Tail),
                param(A)
            do  [[A,B]]
            )
        ).

%% Finds nilpotent basis elements
locate_basis_nilps( Indices, K, Rows, NilpIndices ) :-
        include( locate_basis_nilps_helper( Rows, K ), Indices, NilpIndices ).

locate_basis_nilps_helper( Rows, K, I ) :-
        fast_nth1( I, Rows, Row ),
        sumlist(Row, Sum),
        Sum < K.

%% Makes standard torus to be used in all switchings
make_base_torus( BaseTorus, N, Indices ) :-
        length( BaseTorus, N ),
        numlist( N, SmolIndices ),
        maplist( make_base_torus_row( Indices ), SmolIndices, BaseTorus ).

make_base_torus_row( Indices, RowIndex, BaseTorusRow ) :-
        RootIndex is 2^(RowIndex - 1),
        maplist( make_base_torus_entry( RootIndex ), Indices, BaseTorusRow ).

make_base_torus_entry( RootIndex, ColIndex, Entry ) :-
        (RootIndex /\ ColIndex =:= 0 -> Entry = 0 ; Entry = 1).

%% Main toral switching code
make_torus_switches( _, _, _, _, _, [], [] ) :- !. % no nilpotent basis elements to switch with respect to
make_torus_switches( Indices, Pairs, Roots, BaseTorus, Table, NilpIndices, SwitchedTables ) :-
        maplist( switch_torus( Indices, Pairs, Table, BaseTorus, Roots), NilpIndices, SwitchedTables ).

switch_torus( Indices, Pairs, Table, BaseTorus, Roots, NilpIndex, SwitchedTable ) :-
        maplist( modify_toral_element_checker( NilpIndex ), BaseTorus,
                 ModifyToralElementChecker ),
        maplist( make_new_basis( Indices, Table, BaseTorus, NilpIndex,
                                 ModifyToralElementChecker), Roots, NewBasis ),
        make_new_table( Indices, Pairs, Table, NewBasis, SwitchedTable ).

%% Checks wether the toral element in the switched torus has been modified
modify_toral_element_checker( NilpIndex, ToralRow, ModifyToralElement ) :-
        fast_nth1( NilpIndex, ToralRow, ModifyToralElement ).


%% NewBasisElement is the basis element in the rootspace with respect to Root after the toral switch
%% It is expressed as a list in terms of the original thin basis
make_new_basis( Indices, Table, BaseTorus, NilpIndex, ModifyToralElementChecker, Root,
                NewBasisElement ) :-
        same_length( Table, NewBasisElement ),
        domain( NewBasisElement, 0, 1),
        once( make_new_basis_helper( Indices, Table, BaseTorus, NilpIndex,
                                     ModifyToralElementChecker, Root, NewBasisElement ) ),
        labeling( [], NewBasisElement ). % FIXME: what about multiple solutions?

make_new_basis_helper( Indices, Table, BaseTorus, NilpIndex, ModifyToralElementChecker
                     , Root, NewBasisElement ) :-
        at_least_one( NewBasisElement ),
        maplist( apply_root_value( Indices, Table, NilpIndex, NewBasisElement), BaseTorus,
                 ModifyToralElementChecker, Root, Tuples ),
        append(Tuples, AllTuples),
        root_value_extension(Extension),
        table(AllTuples, Extension).

%% Apply a new toral element on NewBasisElement and kill or stabalise it depending on RootVal
%% NewBasisElement is determined by the constraints created here
apply_root_value( Indices, Table, NilpIndex, NewBasisElement, ToralRow,
                  ModifyToralElement, RootVal, Tuples ) :- % COMMENT: ModifyToralElement, RootVal are 0/1
        fast_nth1( NilpIndex, Table, NilpRow ),
        maplist( nilp_on_element(NilpRow, NewBasisElement, NilpIndex), Indices,
                 NilpOnElement ),
        (   foreach(NOE,NilpOnElement),
            foreach(NBE,NewBasisElement),
            foreach(TR,ToralRow),
            foreach([ModifyToralElement,RootVal,NOE,NBE,TR], Tuples),
            param(ModifyToralElement,RootVal)
        do  true
        ).

root_value_extension(Extension) :-
        Tuple = [ModifyToralElement,RootVal,NOE,NBE,TR],
        SNOE #<=> ModifyToralElement #/\ NOE,
        SNBE #<=> RootVal #/\ NBE,
        SNBE #<=> (TR #/\ NBE) #\ SNOE,
        findall(Tuple, labeling([],Tuple), Extension).

nilp_on_element(_, _, NilpIndex, Index, NilpOnElementEntry ) :-
        NilpIndex = Index, !,
        NilpOnElementEntry = 0.
nilp_on_element(NilpRow, NewBasisElement, NilpIndex, Index, NilpOnElementEntry ) :-
        % NilpRow can be nonground
        % NewBasisElement can be nonground
        NewIndex is xor(NilpIndex, Index),
        fast_nth1( NewIndex, NewBasisElement, V),
        fast_nth1( NewIndex, NilpRow, NilpOnElementEntry0 ),
        NilpOnElementEntry #<=> NilpOnElementEntry0 #/\ V.

%% Given the new thin basis NewBasis calculate its thin table
make_new_table( Indices, Pairs, Table, NewBasis, NewTable ) :-
        maplist( set_diagonal( NewTable ), Indices ),
        maplist( intify_basis(Indices), NewBasis, IntBasis ),
        same_length( Table, NewTable ),
        maplist( same_length(NewTable), NewTable ),
        maplist( make_new_table_entry( Indices, Table, IntBasis, NewTable ), Pairs ).

make_new_table_entry( _Indices, Table, IntBasis, NewTable, [I1, I2] ) :-
        I3 is xor( I1, I2 ),
        fast_nth1( I1, IntBasis, Ints1 ),
        fast_nth1( I2, IntBasis, Ints2 ),
        fast_nth1( I3, IntBasis, Ints3 ),
        filtered_pairs(Ints1, Ints2, Ints3, FilteredPairs, []),
        get_entries( Table, FilteredPairs, Entries ),
        sumlist(Entries, Tot),
        Val is Tot mod 2,
        get_entry( NewTable, [I1, I2], Val ),
        get_entry( NewTable, [I2, I1], Val ).

filtered_pairs(Ints1, Ints2, [MainInt|_]) -->
        (   foreach(X,Ints1),
            param(Ints2,MainInt)
        do  (   foreach(Y,Ints2),
                param(X,MainInt)
            do  ({X is xor(Y,MainInt)} -> [[Y,X]] ; [])
            )
        ).

intify_basis( Indices, BasisRow, Ints ) :-
        include( intify_basis_helper(BasisRow), Indices, Ints ).

intify_basis_helper( BasisRow, I ) :-
        fast_nth1( I, BasisRow, 1 ).

set_diagonal( NewTable, I ) :-
        get_entry( NewTable, [I,I], 0 ).

%% Lexicographically reduce switched tables. Similar methods to 3. LEX REDUCE TABLES
canonical_order_tables_list( N, Roots, Powers, Tables, SwitchedTablesList,
                             OrderedTablesList) :-
        maplist( make_table_row_sum_pair, Tables, TablesWithSums ),
        maplist( canonical_order_rows0( N, Roots, Powers, TablesWithSums ),
                 SwitchedTablesList, OrderedTablesList ).

make_table_row_sum_pair( Table, [X, Y] ) :-
        X = Table,
        full_sorted_row_sums( Table, Y ).

canonical_order_rows0( _, _, _, _, [], []) :- !.
canonical_order_rows0( N, Roots, Powers, SimpleTablesWithSums, Tables, OrderedTables) :-
        maplist(canonical_order_rows( N, Roots, Powers, SimpleTablesWithSums ), Tables,
                OrderedTables).

canonical_order_rows( N, Roots, Powers, SimpleTablesWithSums, Rows, OrderedRows) :-
        full_sorted_row_sums( Rows, RowSums),
        sort( RowSums, SortedRowSums),
        (   foreach(TableWithSums, SimpleTablesWithSums),
            fromto(SimpleTables,SimpleTables1,SimpleTables2,[]),
            param(RowSums)
        do  (TableWithSums = [Table, RowSums]
            ->  SimpleTables1 = [Table|SimpleTables2]
            ;   SimpleTables1 = SimpleTables2
            )
        ),
        first_sol( lex_reduce_to_simple( N, Roots, Powers, Rows, SortedRowSums ),
                   SimpleTables, OrderedRows ).

lex_reduce_to_simple( N, Roots, Powers, Rows, SortedRowSums, Table ) :-
        can_permute_dispatcher( N, Roots, Powers, SortedRowSums, Rows, Table).

%% Make the toral switching graph
%% If a table T1 switches to T2 then T2 might not have switched to T1
%% Thus we calculate a directed graph first
%% We then remove the directions on edges
make_adjacency_mat( Tables, OrderedTablesList, AdjacencyMat ) :-
        length( Tables, M ),
        numlist( M, Indices ),
        maplist( make_adjacency_row( Tables, OrderedTablesList, Indices ), Indices, Mat ),
        transpose( Mat, TMat),
        maplist(maplist( my_max ), Mat, TMat, AdjacencyMat).

make_adjacency_row( Tables, OrderedTablesList, Indices, RowIndex, AdjacencyRow ) :-
        maplist( make_adjacency_entry( Tables, OrderedTablesList, RowIndex ), Indices,
                 AdjacencyRow ).

make_adjacency_entry( _, _, RowIndex ,RowIndex, 0 ) :- !.
make_adjacency_entry( Tables, OrderedTablesList, RowIndex ,ColIndex, AdjacencyEntry ) :-
        nth1( RowIndex, Tables, Table ),
        nth1( ColIndex, OrderedTablesList, TableList ),
        (member( Table, TableList ) -> AdjacencyEntry = 1 ; AdjacencyEntry = 0).

%% Convert an adjacency matrix to a ugraph
adjacency_mat_to_ugraph( A, G ) :-
        length( A, N ),
        numlist(N, Indices),
        maplist( collect_nbrs(A,Indices), Indices, NbrsList ),
        maplist( make_vertex, Indices, NbrsList, G ).

make_vertex( Index, Nbrs, V ) :-
        V = Index-Nbrs. % This is the ugraph notation for defining a vertex and its neighbours

%% Find the neighbours (Nbrs) of a vertex (Index)
collect_nbrs(A, Indices, Index, Nbrs ) :-
        nth1( Index, A, Row ),
        (   foreach(Nbr,Indices),
            fromto(Nbrs,Nbrs1,Nbrs2,[]),
            param(Row)
        do  (nth1( Nbr, Row, 1 ) -> Nbrs1 = [Nbr|Nbrs2] ; Nbrs1 = Nbrs2)
        ).

%% Calculate the connected componenets of a graph.
conn_comps( G, Comps ) :-
        reduce(G, R),
        vertices(R, Comps).

get_min_from_comp( Tables, Comp, MinTable ) :-
        get_values( Tables, Comp, CompTables ),
        min_member(MinTable, CompTables ).
%%%%%%

%%% 5. SYMMETRY PREDICATES %%%

%% Code used in symmetry breaking and lexicographically reducing tables
%% Make a permutation of rows based on an element of gl_n acting on the simple roots
make_perm(Roots,Powers, Mat, RowPerm ) :-
        maplist( perm_it(Powers, Mat), Roots, RowPerm ).

perm_it(Powers, Mat, Root, Entry ) :-
        act_mat(Mat, Root, RootOut),
        bin_2_dec(Powers, RootOut, Entry).

%% Apply a permutation
permute_rows(Rows, PermIndex, NewRow ) :-
        nth1( PermIndex, Rows, NewRow).

%% The predicate can_permute_dispatcher checks if Table1 can be permuted in to Table2
%% This is used in both lex reducing and toral switching
can_permute_dispatcher( N, Roots, Powers, SortedRowSums, Table1, Table2 ) :-
        length( Mat, N ),
        maplist(same_length(Mat), Mat),
        once(can_permute( N, Roots, Powers, Table1, Table2, Mat, SortedRowSums ) ).

can_permute( N, Roots, Powers, T1, T2, Mat, SortedRowSums ) :-
        length( Mat, N ),
        append( Mat, Ms),
        domain( Ms, 0, 1),
                                % Use the row sums of T1 and T2 to crete constraints on which rows of T1 are
                                % mapped to which rows of T2
        partition_by_row_sums( T1, SortedRowSums, Partition1 ),
        partition_by_row_sums( T2, SortedRowSums, Partition2 ),
        maplist( map_partitions(N, Mat, Powers), Partition1, Partition2 ),
        make_perm( Roots, Powers, Mat, RowPerm ),
        maplist(permute_rows(T2), RowPerm, NewRows ),
        transpose(NewRows, TNewRows),
        maplist(permute_rows(TNewRows), RowPerm, T1 ).

map_partitions( Rank, Mat, _, [N1], [N2] ) :- !,
        dec_2_bin( Rank, N1, B1 ),
        dec_2_bin( Rank, N2, B2 ),
        act_mat( Mat, B1, B2 ).
map_partitions( Rank, Mat, Powers, L1, L2 ) :-
        maplist( dec_2_bin( Rank ), L1, Domain ),
        maplist( set_range( Mat, Powers, L2 ), Domain ).

set_range( Mat, Powers, Range, B1 ) :-
        act_mat( Mat, B1, B2 ),
        bin_2_dec( Powers, B2, D ),
        element(Range, D ).

partition_by_row_sums( Mat, SortedRowSums, Partition ) :-
        maplist( has_row_sum(Mat), SortedRowSums, Partition ).

has_row_sum( Mat, S, L ) :-
        (   foreach(R,Mat),
            count(I,1,_),
            fromto(L,L1,L2,[]),
            param(S)
        do  (sumlist(R, S) -> L1 = [I|L2] ; L1 = L2)
        ).

%% row sums with no repeats
sorted_row_sums( M, Sorted ) :-
        maplist( sumlist, M, Sums ),
        sort( Sums, Sorted ).

%% row sums including repeats. Sicstus needs samsort importing
full_sorted_row_sums( M, Sorted ) :-
        maplist( sumlist, M, Sums ),
        samsort( Sums, Sorted ).
%%%%%%
%%%%%%

%%% 6. UTILITY PREDICATES %%%

at_least_one(Xs) :-
        bool_or(Xs, 1).


%% generic predicates used throughout
%% Basic computations

%% C is the max of A and B
my_max( A, B, C ) :-
        C is max(A,B).

%% Get entries from lists and arrays
preprocess(N) :-
        abolish(fast_nth1/3, [force(true)]),
        tell('/tmp/fast_nth1.pl'),
        M is 2^N,
        portray_clause((fast_nth1(J,_,_) :- integer(J), J>M, throw(out_of_range(J)))),
        (   for(I,1,M)
        do  (nth1(I, Pat, X) -> true),
            portray_clause(fast_nth1(I, Pat, X))
        ),
        told,
        compile('/tmp/fast_nth1.pl').

get_value( Row, Index, Value ) :-
        nth1( Index, Row, Value).

get_values( Row, Indices, Values ) :-
        maplist( get_value(Row), Indices, Values ).

get_entry( Rows, [RowIndex, ColIndex], Entry ) :-
        fast_nth1( RowIndex, Rows, Row),
        fast_nth1( ColIndex, Row, Entry).

get_entries( Rows, Indices, Entries ) :-
        maplist( get_entry(Rows), Indices, Entries ).

%% set an element of a list to be 0
set_value_to_zero( Index, Row ) :-
        fast_nth1( Index, Row, 0).

%% Powers is a list of powers of 2
make_powers(N, Powers) :-
        (   for(I,1,N),
            foreach(P,Powers),
            param(N)
        do  P is 1 << (N-I)
        ).

%% binary and decimal conversion
dec_2_bin(Rank, N, L) :-
        (   for(I,1,Rank),
            foreach(B,L),
            param(N,Rank)
        do  B is (N >> (Rank-I)) /\ 1
        ).

dec_is_odd_bin(N) :-
        (   fromto(N,N1,N2,0),
            fromto(0,Par1,Par2,Par3)
        do  N2 is N1 >> 1,
            Par2 is Par1 \ (N1 /\ 1)
        ),
        Par3 = 1.

bin_2_dec(Powers, L, N) :-
        scalar_product(Powers, L, #=, N). % L can be nonground

%% generate roots as elements of GF(2)^N
get_roots(N, Roots) :-
        (   for(I,1,2^N-1),
            foreach(Root,Roots),
            param(N)
        do  dec_2_bin(N, I, Root)
        ).

%% Mat acting on VecIn gives VecOut
act_mat(Mat, VecIn, VecOut) :- % NB VecIn cannot have variables, but Mat can
        maplist( my_scalar_prod( VecIn ), Mat, VecOut).

my_scalar_prod( V1, M1, X) :-   % M1 can be nonground
        scalar_product(V1, M1, #=, Y),
        (Y mod 2) #= X.

%% make a list of all zeroes
row_of_n_zeros( N, Row ) :-
        length(Row, N),
        (   foreach(0,Row)
        do  true
        ).

%% KthRow has the same length as Indices, a 1 in position K, and zeroes elsewhere
make_kth_row( Indices, K, KthRow ) :-
        length(Indices, N),
        (   for(I,1,N),
            foreach(X,KthRow),
            param(K)
        do  (I=K -> X=1 ; X=0)
        ).

%% adding Entry to X at position I obtains Y
place_entry( Ind, Entry, X, Y ) :-
        L is Ind - 1,
        length( A, L ),
        append( A, B, X ),
        append( [ A, [Entry], B ], Y ).

%% Sol is the first element of List to satisfy Goal
first_sol(Goal, List, Sol) :-
        first_sol_(List, Goal, Sol).

first_sol_([], _, []).
first_sol_([X1|Xs1], P, Sol) :-
        ( call(P, X1) -> Sol = X1
        ; first_sol_(Xs1, P, Sol )
        ).

%% Sictus does not have writeln and one of the authors is fond of it
writeln( Stream ) :-
        write( Stream ),
        write('\n').

%% Sicstus needs maplist/4 defining manually
maplist(Pred, Ws, Xs, Ys, Zs) :-
        ( foreach(W,Ws),
            foreach(X,Xs),
            foreach(Y,Ys),
            foreach(Z,Zs),
            param(Pred)
        do call(Pred, W, X, Y, Z)
        ).


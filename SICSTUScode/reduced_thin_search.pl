:-use_module(library(clpfd) ).
:-use_module(library(lists)).
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
        fd_statistics(backtracks, _),
        statistics(runtime, _),
        findall( Rows, thin_table(N,Rows), FirstTables ),
        statistics(runtime, [_,T1]),
        fd_statistics(backtracks, B1),
        length(FirstTables, N1), print_message(informational, format('~w FirstTables in ~w ms, ~w backtracks',[N1,T1,B1])),
        remove_non_simple_tables( FirstTables, SimpleTables ),
        statistics(runtime, [_,T2]),
        length(SimpleTables, N2), print_message(informational, format('~w SimpleTables in ~w ms',[N2,T2])),
        lex_reduce_tables( N, SimpleTables, ReducedTables ),
        statistics(runtime, [_,T3]),
        length(ReducedTables, N3), print_message(informational, format('~w ReducedTables in ~w ms',[N3,T3])),
        once(perform_toral_switchings( N, ReducedTables, ThinTables )),
        statistics(runtime, [_,T4]),
        length(ThinTables, N4), print_message(informational, format('~w ThinTables in ~w ms',[N4,T4])).

%%%%%%

%%% 1. INITIAL THIN SEARCH %%%

thin_table(N, Rows) :-
        thin_search( N, Rows, Part1, Part2, _Sums, _NPairs),
        mylabeling(Part1, Part2).

%% The idea:
%% 1. Partition each Ith row into two parts:
%%    part 1 corresponds to indices J such that J < xor(I,J)
%%    part 2 corresponds to indices xor(I,J) such that J < xor(I,J)
%% 2. For each row, label first part 1, then part 2.
mylabeling(Part1, Part2) :-
        (   foreach(Row1,Part1),
            foreach(Row2,Part2),
            foreach(Row12,Part12)
        do  append(Row1, Row2, Row12)
        ),
        append(Part12, Vs),
        labeling([], Vs).

thin_search( N, Rows, Part1, Part2, Sums, NPairs) :-
        thin_search_essential( N, Rows, Part1, Part2, Sums, NPairs, Indices, Vs),
        stop_certain_ideals(Rows, Indices), % Simplicity constraints ESSENTIAL
        act_faithfully(Rows, Indices),      % Simplicity constraints QUESTIONABLE, 2.5% fewer backtracks
        jacobi_identity_full( Indices, Rows), % Lie Bracket constraint PAYS OFF
        break_gl2_symmetries( Vs, Rows, N ), % Symmetry breaking constraints PAYS OFF
        Rows = [R1|R2etc],
        (   foreach(R2,R2etc),
            param(R1)
        do  lex_chain([R1, R2])
        ).

thin_search_essential( N, Rows, Part1, Part2, Sums, NPairs, Indices, Vs) :-
        M is 2^N-1,
        length(Rows, M),
        numlist(M, Indices),
        maplist(lambda_21(length, M), Rows),
        part_matrix(Rows, Part1, Part2),
        maplist( set_value_to_zero, Indices, Rows), % Lie Bracket constraint
        fast_transpose(Rows, Rows),  % Lie Bracket constraint
        append(Rows, Vs),
        domain( Vs, 0, 1),
        maplist(number_of_ones(N), Rows, Sums), % Implied constraint
        maplist(lemma_2_12(N), Part1, Part2, Sums, NPairs). % Implied constraint PAYS OFF

part_matrix(Mat1, Mat2, Mat3) :-
        (   foreach(Row1,Mat1),
            foreach(Row2,Mat2),
            foreach(Row3,Mat3),
            count(I,1,_)
        do  (   foreach(_,Row1),
                fromto(KL1,KL2,KL3,[]),
                count(J,1,_),
                param(I)
            do  (   I = J -> KL2 = KL3
                ;   J > xor(I,J) -> KL2 = KL3
                ;   K is xor(I,J),
                    KL2 = [J-K|KL3]
                )
            ),
            (   foreach(J2-K2,KL1),
                foreach(X,Row2),
                foreach(Y,Row3),
                param(Row1)
            do  fast_nth1(J2, Row1, X),
                fast_nth1(K2, Row1, Y)
            )
        ).

number_of_ones(N, Row, S) :-
        (   N = 3 -> Dom = {3,4,5} % verified
        ;   N = 4 -> Dom = {4,6,7,8,10,11} % verified
        ;   N = 5 -> Dom = {5,8,9,12,14,15,16,20,23} % verified
      % ;   N = 6 -> Dom = {6}\/(10..11)\/{16}\/{18}\/{24}\/{28}\/(31..32)\/{40}\/{47} % conjecture
        ;   true  -> Max is 2^(N-1) + 2^(N-2) - 1,
                     Dom = (N..Max)
        ),
        S in Dom,
        sum(Row, #=, S).

lemma_2_12(N, Part1, Part2, Sum, NPair) :-
        (   foreach(P1,Part1),
            foreach(P2,Part2),
            foreach(P3,Part3)
        do  P3 #= P1 * P2
        ),
        Pow1 is 2^(N-2),
        (N =< 5 -> NPair in {0,Pow1} ; NPair in {0} \/ (9..Pow1)),
        sum(Part3, #=, NPair),
        sum(Part1, #>=, NPair),
        sum(Part2, #>=, NPair),
        2*NPair #=< Sum.

%% The Jacobi Identity
jacobi_identity_full( Indices, Rows) :-
        jacobi_triples(Indices, Triples, []),
        maplist( jacobi_identity( Rows ), Triples, Tuples ),
        gen_jacobi_extension(Extension),
        table(Tuples, Extension).

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
        get_roots(N, Roots),
        make_powers(N, Powers),
        maplist( break_gl2_symmetry_rowperms(N, GL2, Roots, Powers), Pairs, RowPermss ),
        append(RowPermss, RowPerms),
        maplist( break_symmetry( Vs, Rows ), RowPerms ).

break_gl2_symmetry_rowperms( N, GL2, Roots, Powers, [J,K], RowPerms ) :-
        maplist( add_to_gln_small( N, [J, K] ), GL2, SmolGLN ),
        maplist( fast_make_perm(Roots,Powers), SmolGLN, RowPerms ).

all_pairs_le_n(N) -->
        (   for(I,1,N),
            param(N)
        do  (   for(J,I+1,N),
                param(I)
            do  [[I,J]]
            )
        ).

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
        fast_transpose(NewRows, TNewRows),
        permute_matrix(RowPerm, Rows, NewRows, TNewRows, NewerRows),
        append(NewerRows, Ns),
        lex_chain( [ Vs, Ns ] ).

%% NewerRows = Rows | permute(RowPerm) | inverse | permute(RowPerm)
%% N.B. NewRows and TNewRows=inverse(NewRows) must be supplied pre-allocated
permute_matrix(RowPerm, Rows, NewRows, TNewRows, NewerRows) :-
        (   foreach(Key,RowPerm),
            foreach(Row,Rows),
            foreach(_-Row,KeyRows),
            foreach(NewRow,NewRows),
            foreach(Key-NewRow,KeyNewRows),
            foreach(TNewRow,TNewRows),
            foreach(_-TNewRow,KeyTNewRows),
            foreach(NewerRow,NewerRows),
            foreach(Key-NewerRow,KeyNewerRows)
        do  true
        ),
        keysort(KeyNewRows, KeyRows),
        keysort(KeyNewerRows, KeyTNewRows).

%%%%%%

%%% 2. POST SEARCH SIMPLICTY CHECK %%%

%% Search for certain non-trivial ideals for each table in Tables
%% See paper for explanation
remove_non_simple_tables( Tables, SimpleTables ) :-
        include( simple_check, Tables, SimpleTables ).

% A graph-oriented way of detecting ideals.
% 
% Let G = (V,E) be the digraph where V = the "elements" (e.g. 1..15) and E is the set of edges (i,i xor j) for which M[i,j] = 1.
% 
% Now if G has a strongly connected component C that is a clique, then C is an ideal.
% 
% The code implements this idea it without actually constructing G, because the graph algorithms are a bit slow.
% 
simple_check(Rows) :-
        \+ rows_ideal(Rows, _).

rows_ideal(Rows, Ideal) :-
        (   foreach(Row,Rows),
            foreach(Signature-I,SRows1),
            count(I,1,_)
        do  row_signature(Row, I, Signature)
        ),
        keysort(SRows1, SRows2),
        keyclumped(SRows2, SRows3),
        member(Ideal-Ideal, SRows3).

row_signature(Row, I, Signature) :-
        (   foreach(X,Row),
            fromto(S1,S2,S3,[]),
            count(J,1,_),
            param(I)
        do  (   X = 0 -> S2 = S3
            ;   IJ is xor(I,J),
                S2 = [IJ|S3]
            )
        ),
        sort([I|S1], Signature).

% rows_ideal(Rows, Ideal) :-
%         rows_edges(Rows, Vertices, Edges, []),
%         vertices_edges_to_ugraph(Vertices, Edges, Graph),
%         reduce(Graph, R),
%         member(Ideal-[], R),
%         ord_subtract(Vertices, Ideal, Rest),
%         del_vertices(Graph, Rest, Clique),        
%         length(Clique, Len),
%         Len1 is Len-1,
%         (   foreach(_-Ns,Clique),
%             param(Len1)
%         do  length(Ns, Len1)
%         ).

% rows_edges(Rows, Vertices) -->
%         (   foreach(Row,Rows),
%             foreach(I,Vertices),
%             count(I,1,_)
%         do  (   foreach(X,Row),
%                 count(J,1,_),
%                 param(I)
%                 do  (   {X = 1}
%                     ->  {IJ is xor(I,J)},
%                         [I-IJ]
%                     ;   []
%                     )
%             )
%         ).

% simple_check( Rows ) :-
%         length( Rows, N ),
%         numlist( N, Indices ),
%         maplist( sumlist, Rows, RowSums ),
%         sort( RowSums, UniqueRowSums ),
%         (   foreach(B,UniqueRowSums),
%             foreach(A,IdealSizes)
%         do  A is B+1
%         ),
%         maplist( check_for_ideals( Rows, Indices ), IdealSizes ).

% check_for_ideals(Rows, Indices, IdealSize ) :-
%         (   foreach(A1,Indices),
%             fromto(CorrectRankRoots,CRR1,CRR2,[]),
%             param(Rows,IdealSize)
%         do  fast_nth1(A1, Rows, Row),
%             sumlist(Row, S),
%             (S is IdealSize-1 -> CRR1 = [A1|CRR2] ; CRR1 = CRR2)
%         ),
%         length(CorrectRankRoots, NRoots),
%         (   IdealSize > NRoots -> PossibleIdeals = []
%         ;   IdealSize = NRoots -> PossibleIdeals = [CorrectRankRoots]
%         ;   length( A, IdealSize),
%             findall( A, subseq0( CorrectRankRoots, A ), PossibleIdeals )
%         ),
%         maplist( check_ideal( Rows ), PossibleIdeals ).

% check_ideal( Rows, PossibleIdeal ) :-
%         \+maplist( check_ideal_helper(Rows, PossibleIdeal), PossibleIdeal ).

% check_ideal_helper( Rows, PossibleIdeal, X ) :-
%         maplist( check_ideal_helper_2( Rows, X), PossibleIdeal ).

% check_ideal_helper_2( Rows, X, Y ) :-
%         (   X = Y -> true
%         ;   I is xor(X,Y),
%             get_entry( Rows, [I,X], 1)
%         ).
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
        exclude( can_permute_dispatcher( N, Roots, Powers, MinTable), List, NewList ),
        append( Mins, [MinTable], NewMins ),
        lex_reduce( N, Roots, Powers, NewList, NewMins, ReducedList).

%% Calculate row sums and partition with respect to row sums
populate_row_sum_tables_list( SimpleTables, TablesList ) :-
        (   foreach(SimpleTable,SimpleTables),
            foreach(MS-SimpleTable,KL1)
        do  multiset_of_row_sums(SimpleTable, MS)
        ),
        keysort(KL1, KL2),
        keyclumped(KL2, KL3),
        keys_and_values(KL3, _, TablesList).
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

make_new_basis_helper( Indices, Table, BaseTorus, NilpIndex, ModifyToralElementChecker,
                       Root, NewBasisElement ) :-
        at_least_one( NewBasisElement ),
        maplist( apply_root_value( Indices, Table, NilpIndex, NewBasisElement), BaseTorus,
                 ModifyToralElementChecker, Root ).

%% Apply a new toral element on NewBasisElement and kill or stabalise it depending on RootVal
%% NewBasisElement is determined by the constraints created here
apply_root_value( Indices, Table, NilpIndex, NewBasisElement, ToralRow,
                  ModifyToralElement, RootVal ) :- % COMMENT: ModifyToralElement, RootVal, TotalRow are 0/1
        fast_nth1( NilpIndex, Table, NilpRow ),
        maplist( nilp_on_element(NilpRow, NewBasisElement, NilpIndex), Indices,
                 NilpOnElement ),
        (   foreach(NOE,NilpOnElement),
            foreach(NBE,NewBasisElement),
            foreach(TR,ToralRow),
            param(ModifyToralElement,RootVal)
        do  Key = [ModifyToralElement,RootVal,TR],
            (   Key = [0,0,0] ->  true
            ;   Key = [0,0,1] ->  NBE = 0
            ;   Key = [0,1,0] ->  NBE = 0
            ;   Key = [0,1,1] ->  true
            ;   Key = [1,0,0] ->  NOE = 0
            ;   Key = [1,0,1] ->  NBE #= NOE
            ;   Key = [1,1,0] ->  NBE #= NOE
            ;   Key = [1,1,1] ->  NOE = 0
            )
        ).

%% The above case analysis is based on the following constraints.
% root_value_extension(Extension) :-
%         Tuple = [ModifyToralElement,RootVal,NOE,NBE,TR],
%         SNOE #<=> ModifyToralElement #/\ NOE,
%         SNBE #<=> RootVal #/\ NBE,
%         SNBE #<=> (TR #/\ NBE) #\ SNOE,
%         findall(Tuple, labeling([],Tuple), Extension).

nilp_on_element(_, _, NilpIndex, Index, NilpOnElementEntry ) :-
        NilpIndex = Index, !,
        NilpOnElementEntry = 0.
nilp_on_element(NilpRow, NewBasisElement, NilpIndex, Index, NilpOnElementEntry ) :-
        % NilpRow is ALWAYS ground
        % NewBasisElement can be nonground
        NewIndex is xor(NilpIndex, Index),
        fast_nth1( NewIndex, NewBasisElement, V),
        fast_nth1( NewIndex, NilpRow, NilpOnElementEntry0 ),
        (NilpOnElementEntry0 = 0 -> NilpOnElementEntry = 0 ; NilpOnElementEntry = V).

%% Given the new thin basis NewBasis calculate its thin table
make_new_table( Indices, Pairs, Table, NewBasis, NewTable ) :-
        maplist( set_diagonal( NewTable ), Indices ),
        maplist( intify_basis(Indices), NewBasis, IntBasis ),
        length(Table, M),
        length(NewTable, M),
        maplist(lambda_21(length, M), NewTable),
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
        include(lambda_312(fast_nth1, BasisRow, 1), Indices, Ints).

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
        multiset_of_row_sums( Table, Y ).

canonical_order_rows0( _, _, _, _, [], []) :- !.
canonical_order_rows0( N, Roots, Powers, SimpleTablesWithSums, Tables, OrderedTables) :-
        maplist(canonical_order_rows( N, Roots, Powers, SimpleTablesWithSums ), Tables,
                OrderedTables).

canonical_order_rows( N, Roots, Powers, SimpleTablesWithSums, Rows, OrderedRows) :-
        multiset_of_row_sums( Rows, RowSums),
        (   foreach(TableWithSums, SimpleTablesWithSums),
            fromto(SimpleTables,SimpleTables1,SimpleTables2,[]),
            param(RowSums)
        do  (TableWithSums = [Table, RowSums]
            ->  SimpleTables1 = [Table|SimpleTables2]
            ;   SimpleTables1 = SimpleTables2
            )
        ),
        first_sol( lex_reduce_to_simple( N, Roots, Powers, Rows ),
                   SimpleTables, OrderedRows ).

lex_reduce_to_simple( N, Roots, Powers, Rows, Table ) :-
        can_permute_dispatcher( N, Roots, Powers, Rows, Table).

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
fast_make_perm(Roots,Powers, Mat, RowPerm ) :-
        (   foreach(Root,Roots),
            foreach(Perm,RowPerm),
            param(Powers,Mat)
        do  (   foreach(Power,Powers),
                foreach(Row,Mat),
                fromto(0,Perm1,Perm2,Perm),
                param(Root)
            do  (   foreach(Elt,Row),
                    foreach(Roo,Root),
                    fromto(0,Mod0,Mod1,Mod2)
                do  Mod1 is xor(Mod0,Elt/\Roo)
                ),
                Perm2 is Perm1 + Power*Mod2
            )
        ).


%% The predicate can_permute_dispatcher checks if Table1 can be permuted in to Table2
%% This is used in both lex reducing and toral switching
can_permute_dispatcher( _, _, _, Table1, Table2 ) :-
        Table1 = Table2, !.
can_permute_dispatcher( N, Roots, Powers, Table1, Table2 ) :-
        length( Mat, N ),
        maplist(lambda_21(length, N), Mat),
        once(can_permute( N, Roots, Powers, Table1, Table2, Mat ) ).

can_permute( N, Roots, Powers, T1, T2, Mat ) :-
        length( Mat, N ),
        append( Mat, Ms),
        domain( Ms, 0, 1),
        fast_transpose(NewRows, TNewRows),
                                % Use the row sums of T1 and T2 to create constraints on which rows of T1 are
                                % mapped to which rows of T2
        partition_by_row_sums( T1, Partition1 ),
        partition_by_row_sums( T2, Partition2 ),
        maplist( map_partitions(N, Mat, Powers), Partition1, Partition2 ),
        labeling([], Ms),
        fast_make_perm( Roots, Powers, Mat, RowPerm ),
        permute_matrix(RowPerm, T2, NewRows, TNewRows, T1).

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

partition_by_row_sums( Mat, Partition ) :-
        (   foreach(Row,Mat),
            foreach(Sum-I,KL1),
            count(I,1,_)
        do  sumlist(Row, Sum)
        ),
        keysort(KL1, KL2),
        keyclumped(KL2, KL3),
        keys_and_values(KL3, _, Partition).

multiset_of_row_sums( M, Sorted ) :-
        (   foreach(Row,M),
            foreach(Sum1-1,KL1),
            foreach(Sum2-1,KL2),
            foreach(Sum2,Sorted)
        do  sumlist(Row, Sum1)
        ),
        keysort(KL1, KL2).
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
        M is 2^N-1,
        % portray_clause((fast_nth1(J,_,_) :- integer(J), J>M, throw(out_of_range(J)))),
        (   for(I,1,M)
        do  (nth1(I, Pat, X) -> true),
            portray_clause(fast_nth1(I, Pat, X))
        ),
        told,
        compile('/tmp/fast_nth1.pl'),
        length(Rows, M),
        maplist(lambda_21(length, M), Rows),
        transpose(Rows, Transpose),
        abolish(fast_transpose/2, [force(true)]),
        assertz(fast_transpose(Rows, Transpose)).

get_values( Row, Indices, Values ) :-
        maplist(lambda_213(nth1, Row), Indices, Values).

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
% This version is too slow.
% act_mat(Mat, VecIn, VecOut) :-
%         (   foreach(Mi,Mat),
%             foreach(X,VecOut),
%             param(VecIn)
%         do  (   foreach(Vj,VecIn),
%                 foreach(Mij,Mi),
%                 fromto(0,X1,X2,X)
%             do  X2 #<=> (Vj #/\ Mij) #\ X1
%             )
%         ).
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

lambda_21(F, X, Y) :-
        call(F, Y, X).

lambda_213(F, X, Y, Z) :-
        call(F, Y, X, Z).

lambda_312(F, X, Y, Z) :-
        call(F, Z, X, Y).


pp(Table) :-
        maplist(sumlist, Table, Sums),
        format('Primary table, rowsums = ~w:\n\n', [Sums]),
        pp_table(Table).
        % warp_table(Table, XTable),
        % maplist(sumlist, XTable, XSums),
        % format('Warped table, rowsums = ~w:\n\n', [XSums]),
        % pp_table(XTable).
        % rows_edges(Table, Vertices, Edges, []),
        % vertices_edges_to_ugraph(Vertices, Edges, Digraph),
        % reduce(Digraph, Reduced),
        % write('Digraph:\n\n'),
        % pp_table(Digraph),
        % write('Reduced digraph:\n\n'),
        % pp_table(Reduced).

warp_table(Table, XTable) :-
        (   foreach(Row,Table),
            foreach(XRow,XTable),
            count(I,1,_)
        do  warp_row(Row, I, XRow)
        ).

warp_row(Row, I, XRow) :-
        (   foreach(E,Row),
            foreach(IJ-E,KL1),
            foreach(_-X,KL2),
            foreach(X,XRow),
            count(J,1,_),
            param(I)
        do  (I = J -> IJ = I ; IJ is xor(I,J))
        ),
        keysort(KL1, KL2).

pp_table(Rows) :-
        (   foreach(Row,Rows),
            fromto('   [ ',Prefix,'   , ',_)
        do  format('~w~w\n', [Prefix,Row])
        ),
        format('   ]\n\n', []).

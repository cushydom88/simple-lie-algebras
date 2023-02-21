include "globals.mzn";

%-----------------------------------------------------------------------------%
% Requires that the array 'x' is lexicographically less than or equal to
% array 'y'.  Compares them from first to last element, regardless of indices
%-----------------------------------------------------------------------------%

predicate ortools_lex_lesseq(array[int] of var int: x ::promise_ctx_antitone,
                             array[int] of var int: y ::promise_ctx_monotone) =
    let { int: lx = min(index_set(x)),
          int: ux = max(index_set(x)),
          int: ly = min(index_set(y)),
          int: uy = max(index_set(y)),
          int: size = min(ux - lx, uy - ly) + 1,
          array[0..size] of var bool: unk,
          % unk[i] is true while constraint is not yet entailed
        }
    in
    unk[0] /\
    forall(i in 0..size-1) (
        if not unk[i] then
            not unk[i+1]
        elseif x[lx + i] = y[ly + i] then
            unk[i+1]
        else
            not unk[i+1] /\
            x[lx + i] < y[ly + i]
        endif
    ) /\
    (unk[size] -> (ux - lx <= uy - ly));

%-----------------------------------------------------------------------------%

int: N;
int: M = 2^N-1;
array[int] of int: powers = [2^(N-i) | i in 1..N];
set of int: feasSums =
            if N=3 then {3,4,5}
            elseif N=4 then {4,6,7,8,10,11}
            elseif N=5 then {5,8,9,12,14,15,16,20,23}
            else            N..(2^(N-1) + 2^(N-2) - 1)
            endif;


array[1..5, 1..2, 1..2] of 0..1: gl2 =
[| | 1, 0 |
     1, 1 |,

   | 1, 1 |
     0, 1 |,

   | 1, 1 |
     1, 0 |,

   | 0, 1 |
     1, 1 |,

   | 0, 1 |
     1, 0 | |];

array[1..M, 1..M] of var bool: matrix;
array[1..M, 1..2, 1..M div 2] of var bool: wmatrix = warped(matrix);
array[1..M] of var {0,2^(N-2)}: nbpairs;

array[1..M] of var feasSums: rowsum = [sum(matrix[i,..]) | i in 1..M];

int: nbits(int: x) =
  sum(b in 0..N-1)(
    let {int: bitb0 = 2^(b+0),
         int: bitb1 = 2^(b+1)}
    in x mod bitb1 >= bitb0
  );

int: iand(int: x, int: y) =
  sum(b in 0..N-1)(
    let {int: bitb0 = 2^(b+0),
         int: bitb1 = 2^(b+1)}
    in bitb0 * (x mod bitb1 >= bitb0 /\ y mod bitb1 >= bitb0)
  );

int: ior(int: x, int: y) =
  sum(b in 0..N-1)(
    let {int: bitb0 = 2^(b+0),
         int: bitb1 = 2^(b+1)}
    in bitb0 * (x mod bitb1 >= bitb0 \/ y mod bitb1 >= bitb0)
  );

int: ixor(int: x, int: y) =
  sum(b in 0..N-1)(
    let {int: bitb0 = 2^(b+0),
         int: bitb1 = 2^(b+1)}
    in bitb0 * (x mod bitb1 >= bitb0 xor y mod bitb1 >= bitb0)
  );

constraint :: "symmetric, zero main diagonal"
    forall(i in 1..M)(not matrix[i,i]) /\
    forall(i, j in 1..M where i<j)(matrix[i,j] = matrix[j,i]);

constraint :: "lemma 2.12"
    lemma_2_12(matrix, nbpairs);

array[1..M, 1..2, 1..M div 2] of var bool: warped(array[1..M,1..M] of var bool: mat) =
    array3d(1..M, 1..2, 1..M div 2,
            [ if p=1 then mat[i,j] else mat[i,ixor(i,j)] endif
            | i in 1..M, p in 1..2, j in 1..M where i != j /\ j < ixor(i,j)
            ]);
            
predicate lemma_2_12(array[1..M,1..M] of var bool: mat, array[1..M] of var {0,2^(N-2)}: np) =
    let {array[1..M, 1..2, 1..M div 2] of var bool: wmat = warped(mat)} in
    forall(i in 1..M)(
        let {array[int] of var 0..1: part1 = wmat[i,1,..],
             array[int] of var 0..1: part2 = wmat[i,2,..],
             array[int] of var 0..1: pairs = [part1[j] * part2[j] | j in 1..M div 2],
        } in np[i] = sum(pairs) /\
             sum(part1) >= np[i] /\
             sum(part2) >= np[i]
    );

constraint :: "stop certain ideals"
    stop_certain_ideals(matrix);

predicate stop_certain_ideals(array[1..M,1..M] of var bool: mat) =
    forall(i in 1..M)(
        let {set of int: L1 = {j | j in 1..M where nbits(iand(i,j)) mod 2 = 1},
             set of int: L0 = 1..M diff L1}
        in forall(a in L0)(exists(b in L1)(mat[b,ixor(a,b)]))
    );

constraint :: "act faithfully"
    act_faithfully(matrix);

predicate act_faithfully(array[1..M,1..M] of var bool: mat) =
    forall(i in 1..M)(
        let {set of int: L1 = {j | j in 1..M where nbits(iand(i,j)) mod 2 = 1},
             set of int: L0 = 1..M diff L1}
        in forall(a in L0)(exists(b in L1)(mat[b,a]))
    );

constraint :: "Jacobi identity"
    jacobi_identity(matrix);

predicate jacobi_identity(array[1..M,1..M] of var bool: mat) =
    forall(i1, i2, i3 in 1..M where i1 < i2 /\ i2 < i3 /\ i1 != ixor(i2,i3))(
        let {int: i4  = ixor(i1, i2),
             int: i5  = ixor(i1, i3),
             int: i6  = ixor(i2, i3),
             var bool: a = mat[i1, i2],
             var bool: b = mat[i3, i4],
             var bool: c = mat[i1, i3],
             var bool: d = mat[i2, i5],
             var bool: e = mat[i2, i3],
             var bool: f = mat[i1, i6]}
        in not xorall([(a /\ b), (c /\ d), (e /\ f)])
    );

constraint :: "break gl_2 symmetries"
    forall(I, J in 1..N where I < J, k in 1..5)(
        let {array[1..N, 1..N] of 0..1: NbyN =
                 addToGlnSmall(I, J, gl2[k,1,1], gl2[k,1,2], gl2[k,2,1], gl2[k,2,2])}
        in breakSymmetry(makePerm(NbyN))
    );

constraint :: "first row lex_le all other rows"
    forall(i in 2..M)(ortools_lex_lesseq(matrix[1,..], matrix[i,..]));

array[1..N, 1..N] of 0..1: addToGlnSmall(int: I, int: J, 0..1: A, 0..1: B, 0..1: C, 0..1: D) =
    array2d(1..N, 1..N, [     if i = I /\ j = I then A
                          elseif i = I /\ j = J then B
                          elseif i = J /\ j = I then C
                          elseif i = J /\ j = J then D
                          elseif i = j          then 1
                          else                       0
                          endif
                        | i, j in 1..N
                        ]);

array[1..M] of 1..M: makePerm(array[1..N, 1..N] of 0..1: NbyN) =
    [makePerm(NbyN, k) | k in 1..M];

1..M: makePerm(array[1..N, 1..N] of 0..1: NbyN, 1..M: k) =
    let {array[1..N, 1..N] of 0..1: masked =
             array2d(1..N, 1..N, [if iand(powers[j],k)>0 then NbyN[i,j] else 0 endif | i, j in 1..N]),
         array[1..N] of 0..1: xored = [iand(1,sum(masked[i,..])) | i in 1..N]}
    in sum(i in 1..N)(powers[i] * xored[i]);
    
predicate breakSymmetry(array[1..M] of 1..M: p) =
    let { array[1..M, 1..M] of var bool: permuted =
              array2d(1..M, 1..M, [matrix[p[i], p[j]] | i, j in 1..M]) }
    in  ortools_lex_lesseq(array1d(matrix), array1d(permuted));

% solve
%     :: int_search(matrix, input_order, indomain_min)
%     satisfy;

% test canonical(int: r1, int: r2) =
%     let {int: a = min({M+1} union {j | j in 1..M where fix(matrix[r1,j]) != fix(matrix[r2,j])})}
%     in a > M \/ fix(matrix[r1,a]) < fix(matrix[r2,a]);

% test can_swap(int: r1, int: r2) =
%     let {array[1..M] of 1..M: p = [if i=r1 then r2 elseif i=r2 then r1 else i endif | i in 1..M],
%          array[1..M, 1..M] of bool: permuted =
%               array2d(1..M, 1..M, [fix(matrix[p[i], p[j]]) | i, j in 1..M])}
%     in fix(  lemma_2_12(permuted)
%           /\ stop_certain_ideals(permuted)
%           /\ act_faithfully(permuted)
%           /\ jacobi_identity(permuted)
%           );

solve
  :: bool_search(wmatrix, input_order, indomain_min)
  satisfy;

output ["np = \(nbpairs)\n"];
output ["matrix =\n", show2d(matrix), "\n"];

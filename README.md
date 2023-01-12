# Simple Lie Algebras
This repository is a supplement to the article https://arxiv.org/abs/2207.01094.

It contains computer code to search for simple Lie algebras over the field
$\mathbb{F}_2=\mathrm{GF}(2)$ of two elements and also contains a library of
all known simple Lie algebras over $\mathrm{GF}(2)$ (to the best of our
knowledge).

If you find any of this repository useful then please cite the above article.

## Prolog Code
In our search for new simple Lie algebras over $\mathrm{GF}(2)$ we specifically
look for those with a thin decomposition. In `SICSTUScode` and `SWIcode` you
will find programs that give an exhaustive search of thin Lie algebras in
dimensions 3, 7, 15 and 31.

## Thin Tables
In
['A Prolog assisted search for new simple Lie algebras'](https://arxiv.org/abs/2207.01094)
we classified the simple thin Lie algebras up to dimension 31. The directory
`ThinTables` contains a thin table for every such Lie algebra.

## GAP Code
The `GAPcode` directory contains the following programs:
1) After our Prolog search for simple Lie algebras is complete we must verify
   that the outputted Lie algebras are indeed simple. `MeataxeIsSimple.gap`
   contains code to do this.
2) `LieAlgebraFromThinTable.gap` contains code that turns a thin table in to the
   thin Lie algebra it represents.
3) In order to show some Lie algebras were not isomorphic we counted the number
   of 2-nilpotents and toral elements and used this as in invariant. We used
   Prolog to do this counting, however we used GAP code to generate the
   constraints for Prolog. This can be found in
   `nilps_and_torals_for_prolog.gap`.

## Simple Lie Algebra Library
The `SimpleLieAlgebraBases` directory contains an adjoint basis for each simple
Lie algebra over $\mathrm{GF}(2)$ up to dimension 31. Note that we do not
include Lie algebras that are a tensor product of a lower dimension algebra.

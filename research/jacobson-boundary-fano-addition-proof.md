---
rg: 2
id: jacobson-boundary-fano-addition-proof
kind: route
title: Transport one boundary cell across the seven-point finite orbit and reconstruct all root sums
target: jacobson-boundary-cell-reconstructs-finite-root-packet
requires:
  - jacobson-ts-cell-is-independent-after-first-raw-commutation
  - jacobson-joint-cells-are-two-braids
artifacts:
  - research/artifacts/jacobson-shifted-gl3-and-boundary-gl5-packets-2026-09-08.md
  - research/artifacts/jacobson-boundary-packet-relative-rounding-2026-09-08.md
---

The prerequisites fix the finite packet, the TS word, and the faithful
literal head model. The artifact identifies the additional shifted
finite group on disjoint staggered coordinate triples.

Since `u` is now an involution, the three head-overlap conjugates of
the TS cell give dihedral pairs whose central elements are `a_i r`.
Their products show that `u` centralizes the head row four-group and
`r`. Shifted finite-group conjugation gives the other row centralizers
and the redundancy of `[h c h,r]=1`.

The resulting shifted point stabilizer fixes each chosen head root.
Its seven conjugates are therefore indexed by nonzero vectors. The
new boundary cell gives addition for one independent pair. Its product
is an involution, so that pair commutes. Transitivity on ordered
distinct pairs gives all additions and commutations. The product law
between the three original head row roots then gives cross-source
commutation and the six-dimensional elementary abelian normal subgroup.

The two finite linear factors normalize this root group as stated.
The explicit literal boundary action distinguishes all six root
coordinates, the head source factor, and the shifted far-tail factor;
it proves injectivity of the claimed semidirect product. Counting rank
zero, one, and two matrices in the character group gives the three
complex character-orbit sizes. No inference of matrix-gap positivity
is made from this finite reconstruction.

For approximate cells, choose seven deterministic shifted orbit
representatives and form all root matrices as words in the same given
operators. Their multiplication and covariance errors produce a map
from the entire finite group with uniform defect at most
`D=10 ell+128 w`. Its restriction to `P_Q x K_P` is exactly the
given original representation. Averaging the approximate range
projection over this finite group, taking its spectral projection, and
using its polar isometry gives a representation on the original
dimension within `17D`. The polar factor of the subgroup-averaged
intertwiner fixes the common subgroup exactly, with total correction
at most `85D`. Defining `H'` from this single corrected representation
preserves every shared word. Telescoping the remaining relators gives
the claimed errors. All averaging groups in this argument are finite;
there is no uniform invariant-vector assertion about the infinite
candidate group.

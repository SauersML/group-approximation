---
rg: 2
id: jacobson-165-seed-stabilizer-trace-proof
kind: route
title: Match the full head-parabolic profile and distinguish its larger intersection by one stabilizer trace
target: jacobson-165-seed-fails-full-root-intersection
requires:
  - jacobson-first-root-packet-admits-coherent-relative-correction
  - jacobson-double-rank-one-root-orbit-cannot-extend
  - binary-jacobson-gl3-k-branching-has-regular-counterprofile
artifacts:
  - research/artifacts/jacobson-165-seed-full-intersection-obstruction-2026-09-08.md
---

The prerequisites specify the two finite root packets, their actual
intersection, and the elementary branching data. For a nonzero
`A_Q` character, the boundary rank-one orbit contributes four
copies of each selected source-stabilizer sign. On the rank-two
orbit, the source involution acts freely on the twelve lifts,
contributing six copies of each sign. This proves the two head-type
multiplicity formulas and the preliminary parity exclusion.

The 165-dimensional seed has head-type multiplicities 24 and zero.
Consequently every matching boundary representation has only its
rank-one orbit, with a six-dimensional target stabilizer fiber and
trivial source sign. Splitting its target covectors according to
`f(e_2)=0` gives the two explicit branching maps `A` and `B`
in the artifact. The full smaller-overlap equations admit exactly
four target fibers:

```text
1+s+2*t_2,     s+t_2+S,     1+t_2+S',     S+S'.
```

The first fails positivity on the remaining fixed multiplicity
space. The other three give exact character matches on the whole
smaller overlap, with explicit `E`-trivial summands. Thus the
exclusion does not rest on a missing smaller-overlap construction.

Choose the displayed nonzero `N_0` character. Its four lifts in
the `P` rank-one orbit have three-dimensional fibers; its two
lifts in the `J` orbit have six-dimensional fibers. The element
`x_31,P` fixes these lifts. In the two target covector stabilizers
it is, respectively, a normal-four-group involution and a
transposition. Their character sums are zero or four for the two
possible `P` fibers, but six, two, two, or minus two for the four
possible `J` fibers. A representation isomorphism on `I` must
preserve this spectral subspace and its stabilizer character, which
is impossible. Root-trivial spectators have no contribution on
the chosen nonzero spectral subspace.

This completes only the stated seed exclusion. No mixed-relator
solution, general higher-dimensional exclusion, or uniform
operator-norm gap is deduced.

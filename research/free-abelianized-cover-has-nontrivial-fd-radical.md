---
rg: 2
id: free-abelianized-cover-has-nontrivial-fd-radical
kind: claim
title: The free abelianized cover of a non-residually-finite group has a nontrivial exact finite-dimensional radical
distinct_from:
  free-abelianized-cover-is-torsion-free: that is the group theory of the same cover -- torsion-freeness and freeness of the abelian kernel -- and mentions no representation; this computes what exact finite-dimensional unitary representations of the cover can see, and its hypothesis is a residual property of the base.
  free-abelianized-cover-reflects-mf: that is the open analytic transfer, about the MF radical, which is the smaller radical; this is an established statement about the finite-dimensional radical, which is the larger one, so it does not bear on that implication in either direction.
  abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center: that exhibits one finitely presented solvable group whose central prime mark is finite-dimensionally invisible; this produces an invisible mark over an arbitrary non-residually-finite base by a canonical construction, and its mark is a commutator of infinite order rather than central torsion.
artifacts:
  - research/artifacts/torsion-free-cover-fd-radical-and-heisenberg-2026-09-08.md
---

**ESTABLISHED.**  Let `G` be countable, let `X` generate `G`, adjoin one
dummy generator `z` mapping to the identity, and form the free abelianized
cover of `free-abelianized-cover-is-torsion-free` for that presentation:

```text
F = F(X u {z}),   q : F ->> G,   q(z) = 1,   R = ker q,
E = F/[R,R],      A = R/[R,R].
```

Write `Rad_fd(K)` for the intersection of the kernels of all exact
finite-dimensional unitary representations of `K`, as in
`fd-mark-stability-forces-mf-invisibility`.  Then for every `f in F` whose
image `g = q(f)` lies in the finite residual `Res_fin(G)`,

```text
[fbar, zbar] != 1  in E   whenever g != 1,                            (FDR1)
[fbar, zbar] in Rad_fd(E)  always.                                    (FDR2)
```

Consequently

```text
G not residually finite   ==>   Rad_fd(E) != 1.                       (FDR3)
```

Residually finite groups are MF (`mf-positive-controls`), so `(FDR3)` applies
in particular to every non-MF `G`: the canonical torsion-free cover of a
non-MF group always has a nontrivial exact finite-dimensional radical, and an
explicit nontrivial element of it is named.

The dummy generator is what makes `(FDR1)` independent of the presentation
chosen for `G`; without it the detector has to be built from the relators of
the given presentation and can be empty.

**What this is not.**  `Rad_fd` is the *larger* of the two radicals: a
finite-dimensional unitary representation is a constant-sequence corona
representation, so `Rad_MF <= Rad_fd` for every group
(`five-radicals-from-residually-finite-target`).  `(FDR3)` therefore says
nothing about `Rad_MF(E)`, and in particular nothing about whether `E` is MF.
The stronger collapse available under a full MF radical downstairs is
`free-abelianized-cover-fd-radical-is-commutator`, and the reason even that
stronger conclusion is not a non-MF criterion is
`rational-heisenberg-fd-radical-is-commutator-and-mf`.

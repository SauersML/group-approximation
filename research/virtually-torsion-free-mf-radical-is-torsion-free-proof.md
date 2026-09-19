---
rg: 2
id: virtually-torsion-free-mf-radical-is-torsion-free-proof
kind: route
title: Finite quotients are MF, and the regular representation of a finite quotient traces every corner that survives in it
target: virtually-torsion-free-mf-radical-is-torsion-free
requires:
  - mf-radical-functoriality
  - mf-positive-controls
  - universal-mf-quotient
  - nonhyperlinear-finite-augmentation-corner-kills-mf
  - virtually-torsion-free-infinite-mf-radical-gives-seed
artifacts:
  - research/mf-radical-functoriality.md
  - research/mf-positive-controls.md
---

## Why sufficient

**Part 1.**  Let `M` be normal of finite index in `H`.  The finite group
`H/M` is countable and residually finite, so it is MF by
`mf-positive-controls`.  By `mf-radical-functoriality` (every homomorphism
to an MF group kills the radical), the quotient map `H -> H/M` kills
`Rad_MF(H)`.  So `Rad_MF(H) <= M`.  Every finite-index subgroup contains its
normal core, which is normal of finite index, so `Rad_MF(H) <= Res(H)`.

**Part 2.**  Let `E <= H` be torsion-free of finite index `m`.  Its core
`N = Core_H(E)` is the kernel of the action of `H` on the `m` cosets.  So it
is normal of index at most `m!`, and it is torsion-free because `N <= E`.
By Part 1, `Rad_MF(H) <= N`.  So `Rad_MF(H)` is torsion-free.  `W(H)` is a
union of finite subgroups, so `Rad_MF(H) intersect W(H)` is a torsion
subgroup of a torsion-free group, hence trivial.

**Part 3.**  Let `Q = H/M`, `d = |Q|`, and let
`lambda : C[H] -> C[Q] -> End(C[Q]) = M_d` be the left regular
representation of `Q`, pulled back to `H`.  It is a unital star
homomorphism, since group elements go to permutation matrices.

- `K` meets `M` trivially, so `K` embeds in `Q`.  It acts freely on `Q` by
  left multiplication.  Hence `p = lambda(|K|^-1 sum_(k in K) k)` is the
  orthogonal projection onto the `K`-invariant vectors, whose dimension is
  the number of `K`-orbits, `d/|K|`.
- So `lambda(q_K) = 1 - p` is a projection of rank `r = d(1 - 1/|K|)`.  This
  is at least `d/2 > 0` because `|K| >= 2`.
- Suppose `Phi : B -> q_K C[H] q_K` is a unital star homomorphism.  Then
  `lambda o Phi` is a unital star homomorphism
  `B -> lambda(q_K) M_d lambda(q_K)`, and the target is isomorphic to `M_r`.
- The normalized trace `tau = tr_r o lambda o Phi` is a tracial state on
  `B`.  It is positive because it is a trace composed with a star
  homomorphism.  It factors through the matrix algebra `M_r`, which embeds
  unitally and trace-preservingly in `R^omega`.  So `tau` is
  Connes-embeddable.
- This contradicts the hypothesis on `B`, so there is no such `Phi`.

A second proof uses only Parts 1 and 2 when `H` is virtually torsion-free.
Suppose such a `Phi` exists.  `nonhyperlinear-finite-augmentation-corner-kills-mf`
gives `K <= Rad_MF(H)`.  `Rad_MF(H)` is torsion-free by Part 2, so `K = 1`.

## Corollaries

**(a) The hole is refuted.**  In `virtually-torsion-free-host-no-ce-augmentation-corner`
we have:

- `E` torsion-free of finite index;
- `K` finite, with infinite normal closure and hence `K != 1`;
- `K intersect Core_H(E) <= K intersect E = 1`, since `E` is torsion-free.

So `M = Core_H(E)` meets the hypotheses of Part 3, and no `Phi` exists.  The
recursive presentation, finite generation and choice of host are never used.
So the refutation covers every candidate family, including finite extensions
of Burger--Mozes and Wise lattices.

**(b) The corner corollary is vacuous and (c) the dichotomy collapses.**
Both follow from Part 2 applied to `virtually-torsion-free-infinite-mf-radical-gives-seed`.

- `Rad_MF(H) <= W(H)` together with `Rad_MF(H) intersect W(H) = 1` gives
  `Rad_MF(H) = 1`.  By `universal-mf-quotient`, `H` is MF.
- Conversely, if `H` is not MF, then `Rad_MF(H) != 1` is torsion-free, so it
  is not contained in the finite `W(H)`, and case 2 applies.
- The converse clause of that lemma already shows that a seed is such an
  `H`.

**(d)** This is Part 1 combined with
`nonhyperlinear-finite-augmentation-corner-kills-mf`.

## Property-T audit

The route uses the following, and nothing else:

- residual finiteness of finite groups;
- forward functoriality of the radical;
- the regular representation of a finite group;
- the corner theorem, which is used only for the second proof.

No Kazhdan input appears.

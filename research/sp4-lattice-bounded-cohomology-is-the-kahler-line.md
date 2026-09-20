---
rg: 2
id: sp4-lattice-bounded-cohomology-is-the-kahler-line
kind: claim
title: Every finite-index subgroup of Sp4(Z) has one-dimensional second real bounded cohomology, spanned by the Maslov class, with injective comparison map and a genuine Gromov norm
distinct_from:
  sp4-winding-ratio-sharp-constant-is-gromov-dual: that computes the l1 seminorm of relator cycles of Sp_4(Z) itself and uses no bounded-cohomology computation; this imports the dimension of H^2_b on every finite-index subgroup, which that node never needs.
  deligne-parameter-group-is-a-virtual-invariant: that computes the integral divisibility of the Maslov class on finite-index subgroups; this is the real bounded cohomology of the same subgroups, which that node does not touch.
  sp2g-central-commutators-of-universal-lifts-are-torsion: that uses the Guichardet--Wigner quasimorphism on commuting pairs; this uses it only to see that the covering class is bounded, and adds the Monod and Burger--Monod computation of all of H^2_b.
---

**ESTABLISHED by citation** (`sp4-lattice-bounded-cohomology-is-the-kahler-line-citation`).

`Gamma = Sp_4(Z)`, `b` the normalized integral covering cocycle of `deligne-sep7-norm-parameter-closed-subgroup`,
`H^2_b(-) = H^2_b(-;R)` real bounded cohomology of a discrete group, `||.||` the Gromov (sup-quotient) seminorm.
For every finite-index `Lambda <= Gamma`:

1. **(BK1) Dimension.** `dim H^2_b(Lambda) <= 1`.
2. **(BK2) Norm.** The Gromov seminorm on `H^2_b(Lambda)` is a norm.
3. **(BK3) The Maslov class is bounded.** There is a bounded integral cocycle `b'` with `b' - b = delta k` for an
   integer-valued normalized `k`, on all of `Gamma`. Its bounded class `[b']_b` restricts to a nonzero class on
   every `Lambda`.
4. **(BK4) Hence** `H^2_b(Lambda) = R [b']_b`, and `||[b']_b||_Lambda = ||[b']_b||_Gamma =: nu_b`, with
   `0 < nu_b < infinity`. The number is independent of the choice of `b'`: the comparison map
   `H^2_b(Gamma) -> H^2(Gamma;R)` is injective, so `[b']_b` is determined by `[b]_R`.

Inputs: Monod, Corollary 1.4 (restriction `H^n_cb(G) -> H^n_b(Lattice)` is an isomorphism for `n < 2 rank G`);
Burger--Monod GAFA 2002, proof of Corollary 24 (`H^2_cb(G) -> H^2_c(G)` is injective, and the target is
one-dimensional for Hermitian `G`), Corollary 9 (Banach) and Theorem 21 (injective comparison for all lattices of
higher-rank simply connected almost simple groups); and the Guichardet--Wigner homogeneous quasimorphism as recorded
verbatim in `sp2g-central-commutators-of-universal-lifts-are-torsion-proof`.

**Consumer.** `deligne-uniform-scalar-models-have-a-level-free-third-floor`, which closes the uniform conditional
remark of `deligne-maslov-tensor-functors-are-asymptotically-regular-proof`. That remark said the needed input was
only known for cocompact lattices. Monod's Corollary 1.4 has no cocompactness hypothesis.

---
rg: 2
id: steinberg-hs-stability-equals-nonhyperlinearity-proof
kind: route
title: Close both converses of the fork using quasisimplicity
target: steinberg-hs-stability-equals-nonhyperlinearity
requires: [leavitt-steinberg-hs-stability-fork, pointwise-hs-stability-from-no-hyperlinear-quotient]
artifacts:
  - notes/NOTEPAD.md
---

Write `U=St_5(L_(F_2)(1,2))`, `Q=EL_4(L)=U/Z(U)`.  Three inputs are carried
by `leavitt-steinberg-hs-stability-fork`: `U` is quasisimple, every
finite-dimensional unitary representation of `U` is trivial, and Thom's
central-quotient permanence (hyperlinearity passes from a group to its
quotient by a central subgroup).

**3 implies 2.**  Let `U/N` be a nontrivial hyperlinear quotient.  Then `N`
is a proper normal subgroup of the quasisimple group `U`, so `N <= Z(U)`,
and `U/N` surjects onto `Q` with central kernel `Z(U)/N`.  Central-quotient
permanence makes `Q` hyperlinear, contradicting 3.

**2 implies 1.**  This is `pointwise-hs-stability-from-no-hyperlinear-quotient`
applied to `U`.  It yields pointwise stability witnessed by the trivial
representations; since every genuine finite-dimensional unitary
representation of `U` is trivial anyway, the witnesses live in the same
dimensions as the almost-representation, so the conclusion is stability in
the strict same-dimension sense and not merely a flexible one.

**1 implies 3.**  Suppose `Q` is hyperlinear, so there is an injective
`Q -> U(prod_omega M_(d_n))`.  Compose with `U ->> Q` to get a nontrivial
homomorphism from `U`, and represent it by maps `phi_n:U -> U(d_n)` whose
multiplicative defects vanish in `‖.‖_(2,d_n)` and for which some `g` has
`liminf ‖phi_n(g)-1‖_(2,d_n) > 0`.  Every genuine finite-dimensional
representation of `U` is trivial, so no sequence of genuine representations
is asymptotically close to this family, and `U` is not HS-stable.

The cycle `3 => 2 => 1 => 3` closes.

**External corroboration of one consequence.**  Becker--Lubotzky, *Group
stability and Property (T)*, arXiv:1809.00632, J. Funct. Anal. 278 (2020)
108298, Theorem 1.3(ii), verified from the paper text on 2026-08-14: "If
`Gamma` is hyperlinear and has Property (T), then it is not HS-stable,
unless it is finite."  Their `d_n^HS` is described in the paper as "the
normalized Hilbert-Schmidt metric", `‖T‖_HS = (Tr((1/n)T^*T))^(1/2)`, and
the correcting homomorphisms are required to land in the **same** dimension
`n_k`, so this is the strict metric of the claim above.  `U` is infinite and
Kazhdan (Ershov--Jaikin-Zapirain, arXiv:0809.4095, Theorem 6.2, for `n>=3`
over any finitely generated associative unital ring), so their theorem gives
`1 => U nonhyperlinear`.  That is strictly weaker than `1 => 3` proved above
and is recorded only as an independent check.  Their Theorem 1.4 -- Kazhdan
plus HS-stable implies finitely many finite-index subgroups -- is vacuous
here, since `U` has exactly one: a proper finite-index subgroup would have a
normal core with nontrivial finite quotient, hence a nontrivial
finite-dimensional unitary representation.

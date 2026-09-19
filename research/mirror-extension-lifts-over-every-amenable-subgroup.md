---
rg: 2
id: mirror-extension-lifts-over-every-amenable-subgroup
kind: claim
title: Every homomorphism from a countable amenable group into Q lifts to the mirror normalizer N_-, so (HS) holds over every amenable subgroup of SL_n(F_2[x,x^-1])
distinct_from:
  mirror-extension-splits-over-free-finite-by-free-subgroups: that lifts graphs of finite groups and locally finite groups given liftable finite subgroups; this proves every finite and every amenable subgroup lifts, by cocycle vanishing, including the torus Z^2 left open there.
  mirror-lift-untwists-only-through-a-mirror-splitting: that reduces untwisting the mirror lift to a splitting of the symbol; this constructs such splittings over every amenable subgroup and says nothing about Q itself.
  jacobson-symbol-sequence-does-not-virtually-split: that concerns the algebraic symbol sequence of EL_n(J), which has no virtual section; this concerns the measurable extension N_- over [T_-], whose amenable restrictions all split.
  outer-covering-lifts-are-virtual-sections: that identifies outer covering lifts with virtual sections; this is a vanishing theorem for the [T]-valued 2-cocycle on amenable subgroups.
artifacts:
  - research/mirror-extension-lifts-over-every-amenable-subgroup-proof.md
---

**Setting.** The notation is that of `bilateral-lift-at-coordinate-projection-is-mirror-cocycle-lift`.
* `A = F_2[x,x^-1]`, `Q = SL_n(A)` with `n >= 3`, and `J` is the Jacobson (Toeplitz) algebra.
* `X_- = (F_2^n)^N` carries Haar measure `mu_-`, and `T_-` is the tail relation (ergodic, hyperfinite).
* `N_- = Ê_-[T_-]`, and `1 -> [T_-] -> N_- --pi_-> Q -> 1` is exact.
* **(HS) over `Lambda`** means: for a homomorphism `rho: Lambda -> Q` there is a homomorphism `rho~: Lambda -> N_-`
  with `pi_- ∘ rho~ = rho`.

**Theorem.**
1. **(General lifting.)** Let `T` be an ergodic p.m.p. countable Borel equivalence relation, and let `N` be any group
   with `[T] <= N <= N[T]`. Every homomorphism `rho: Lambda -> N/[T]` from a countable amenable group lifts to a
   homomorphism `Lambda -> N`.
2. **(Finite groups, elementary.)** When `Lambda` is finite, part 1 has a self-contained proof. It uses only a
   fundamental-domain partition and the partial-isomorphism lemma (Kechris--Miller, Lemma 7.10). It needs neither
   hyperfiniteness nor any outerness hypothesis.
3. **(Consequence for the hole.)** (HS) holds over every amenable subgroup of `Q`. In particular it holds over:
   * every finite subgroup, which settles survivor (FL) of w16;
   * the diagonal torus `Z^(n-1)`, and so `Z^2`, which settles survivor (Z2);
   * the Borel, unipotent and all solvable subgroups, which settles survivor (AM).
4. **(Combined with w16.)** Together with `mirror-extension-splits-over-free-finite-by-free-subgroups`, (HS) holds
   unconditionally over every f.g. virtually free subgroup, every locally finite subgroup, and every amenable subgroup.

**Class-kill.**
* *Named invariant:* the `[T_-]`-valued 2-cocycle `c(g,h) = sigma(g) sigma(h) sigma(gh)^-1` of a set-theoretic lift
  `sigma`.
* *Death step:* for amenable `Lambda` this class vanishes. That is the cocycle-vanishing theorem of Popa--Shlyakhtenko--Vaes
  (Theorem 5.2), extending Feldman--Sutherland--Zimmer (Theorem 3.4).
* *Consequence:* any refutation of (HS) for `Q` must use a non-amenable, non-virtually-free subgroup of `Q`. That is,
  it must use relations that property (T) forces. Every obstruction localized on an amenable subgroup is dead.

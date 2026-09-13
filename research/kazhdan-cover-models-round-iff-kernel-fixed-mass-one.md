---
rg: 2
id: kazhdan-cover-models-round-iff-kernel-fixed-mass-one
kind: claim
title: Models pulled back from a Kazhdan cover round exactly when the kernel's fixed subspace has asymptotically full dimension
distinct_from:
  flexible-hs-stability-passes-to-kazhdan-kernel-quotients: that assumes the kernel has property (T) and transports stability to the quotient; this assumes the cover has property (T), allows an arbitrary kernel, and decides rounding of each pulled-back model by the kernel's fixed-subspace dimension.
  rf-kazhdan-group-not-flexibly-hs-stable: that is the central-kernel instance, where the fixed subspace is zero; this is the general criterion together with its corollary for infinitely presented Kazhdan groups.
  hyperlinear-flexibly-hs-stable-group-is-residually-finite: that derives residual finiteness from flexible stability of a hyperlinear group; this derives, for an infinitely presented Kazhdan group, that the finite-dimensional representations of all large finitely presented covers factor through the group.
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `Γ~` is a finitely generated Kazhdan group, `N` a normal subgroup, `q : Γ~ -> Γ = Γ~/N` the
  quotient map, and `s : Γ -> Γ~` a set-theoretic section with `s(e) = e`.
- `ρ_k : Γ~ -> U(d_k)` are unitary representations with

  ```text
  ||ρ_k(m) - 1||_(2,d_k) -> 0     for every m ∈ N.                              (KC1)
  ```

- `E_k` is the projection onto `Fix_N(ρ_k) = {v : ρ_k(m)v = v for all m ∈ N}`, and
  `α_k = ρ_k∘s`.

**Theorem.**
1. `α_k` is an asymptotic representation of `Γ`.
2. Along any subsequence the following are equivalent:
   - (a) `α_k` rounds flexibly: there are genuine `π_k : Γ -> U(D_k)` with `D_k >= d_k`,
     `D_k/d_k -> 1` and `||α_k(g) - P_kπ_k(g)P_k*||_(2,d_k) -> 0` for all `g`;
   - (b) `α_k` rounds strictly: the same with `D_k = d_k`;
   - (c) `tr_(d_k)(E_k) -> 1`.
3. **Quantitative form.** If `(K,κ)` is a Kazhdan pair for `Γ~` and `δ_k` is the largest
   displacement of the corner vector over `K` in the bimodule representation of the proof,
   then `1 - tr E_k <= δ_k^2/κ^2`.

**Corollary (infinitely presented Kazhdan groups).**
- **Setup.** Let `Γ` be a Kazhdan group that is not finitely presented. By Shalom's theorem
  (`fpbs-shalom-property-t-is-open`) there is a finitely presented Kazhdan `Γ~` with
  `Γ ≅ Γ~/N`. Enumerate `N = {n_1, n_2, ...}` and put `Γ_L = Γ~/⟨⟨n_1, ..., n_L⟩⟩` (finitely
  presented) and `K_L = ker(Γ_L -> Γ)`.
- **Statement.** Suppose that for infinitely many `L` some finite-dimensional unitary
  representation of `Γ_L` is nontrivial on `K_L`. Then `Γ` is not flexibly HS-stable.
- **Sufficient conditions.** For example, it suffices that `Γ_L` has a finite quotient in which
  `K_L` survives. The hypothesis holds for all large `L` whenever the profinite completion of
  `Γ` is not finitely presented as a profinite group.

Derivation: `kazhdan-cover-models-round-iff-kernel-fixed-mass-one-proof`.

**Reading.**
- **Contrapositive.** If an infinitely presented Kazhdan group is flexibly HS-stable, then for
  all large `L` every finite-dimensional representation of its finitely presented cover `Γ_L`
  factors through `Γ`.
- **Relation to Dogon.** This is the finite-dimensional counterpart of Dogon's Theorem 1.10
  (arXiv:2211.10492v3): "Let Γ be an infinitely presented property (T) group. If Γ is weakly
  ucp-stable, then there exists a non-hyperlinear group."
  - Dogon's proof embeds the group von Neumann algebras of the covers in a matrix ultraproduct.
    He says it "proceeds along the lines of the proof of Theorem G" of Ioana--Spaas--Wiersma.
  - Using finite-dimensional representations instead turns the disjunction "or some group is
    not hyperlinear" into a concrete profinite condition on the covers.
- **What rounding means at a Kazhdan cover.** For models pulled back from a Kazhdan cover,
  rounding is a statement about fixed vectors of the kernel alone. Instability at `Γ` is
  therefore the existence of representations of a Kazhdan cover that are pointwise almost trivial
  on `N`, while `N` has fixed subspace of normalized dimension bounded away from 1.
- **Model tests.**
  - *Trivial model.* Representations trivial on `N` satisfy (c) and round.
  - *Real object.* `rf-kazhdan-group-not-flexibly-hs-stable` satisfies (KC1) with `Fix_N = 0`.
  - *Corollary hypothesis.* Finitely presented Kazhdan groups fail it, since `K_L = 1` for large
    `L`. No explicit infinitely presented Kazhdan group has been checked to satisfy it yet. For
    `SL_3(F_q[t])`, and hence for the rank-3 Kun--Thom vertex through its retract, this is the
    open crux.

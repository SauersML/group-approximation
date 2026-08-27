---
rg: 2
id: compressor-coset-two-point-exact
kind: claim
title: The compressor coset is residually visible — exact two-point approximation at (Γ, tΓ)
distinct_from:
  two-point-orbit-approximation: that claim (after the 2026-08-15 pair correction) asks for approximate models separating the marked pair (Γ, hΓ), whose collapse in every finite quotient is provable; this proves the compressor pair (Γ, tΓ) — the pair that node stated before the correction — is separated by exact congruence quotients, so nothing approximate is ever needed there.
  finite-quotient-blindness: that says the image of Γ is normal in every finite quotient, so the compression data tΓt⁻¹ ⊊ Γ dies; this shows normality of the image does not identify the coset tΓ with Γ — the coset, unlike the compression, survives reduction.
  marked-double-coset-infinite-degree: that computes an infinite index in the infinite group G and constrains invariant graphs on G/Γ; this is a statement about finite congruence shadows of G/Γ and computes there exactly.
artifacts:
  - GroupApproximation/Sofic/ProfiniteClosure.lean
---

Let `Γ = EL_r(R_+) < G = EL_r(R) ⋊ SL_d(ℤ)` be the Kun--Thom Theorem E pair
(`r,d ≥ 3`, `R_+ = F_q[x_1,…,x_d]`, `R = F_q[x_1^{±1},…,x_d^{±1}]`), and let
`g ∈ G` have **nontrivial `SL_d(ℤ)`-component** — in particular let `g = t` be
any strict compressor lying in `SL_d(ℤ)` (a nonnegative non-permutation matrix
of determinant 1).  Then:

1. **Residual visibility.**  For every `M` exceeding twice the largest entry
   of the `SL_d(ℤ)`-component of `g`, the congruence quotient

   ```text
   π_M : G → Q_M := EL_r(F_q[(ℤ/M)^d]) ⋊ SL_d(ℤ/M)
   ```

   (reduce exponents mod `Mℤ^d`, reduce the acting matrix mod `M`) satisfies
   `π_M(g) ∉ π_M(Γ)`; equivalently the cosets `Γ` and `gΓ` have **distinct
   images** in `Q_M/π_M(Γ)`.

2. **Exact two-point approximation.**  Consequently the two-point
   approximation of `two-point-orbit-approximation` holds at the pair
   `(p,q) = (Γ, gΓ)` in the strongest possible form: a single finite model
   works for **every** finite window `F ⊆ G` simultaneously, with an exact
   homomorphism `φ`, with `S = A` (no deleted states), and with the
   equivariance identity holding exactly for all `g' ∈ G`, not only on a
   window.

3. **Identification of the label space.**  `π_M(Γ) = EL_r(F_q[(ℤ/M)^d])` is
   the full elementary part, because `x̄_i` has multiplicative order dividing
   `M`, so every negative monomial exponent is realized by a positive one:
   `x̄^{-a} = x̄^{(M-1)a}`.  Hence `Q_M/π_M(Γ) ≅ SL_d(ℤ/M)` and the separating
   label of the coset `gΓ` is exactly the congruence shadow of the monomial
   part of `g`.

## What this settles, and what it re-opens

Before 2026-08-15, `two-point-orbit-approximation` stated its pair as
`(Γ, tΓ)` with `t` a strict compressor and argued its liveness from
`finite-quotient-blindness`.  This claim shows that statement was **trivially
true and was never the live question**: blindness makes `π(Γ)` normal, which
kills the *compression* `tΓt⁻¹ ⊊ Γ`, but it does not touch the *coset* `tΓ`
when `t` carries a nontrivial monomial substitution — item 1 separates it
exactly.  The pair on which every finite quotient genuinely collapses is
`(Γ, hΓ)` with `h = e_12((x_1⋯x_d)^{-1})` the marked element of the wreath
mark `w = a_Γ a_{hΓ}`: there `h` is a `G`-conjugate of an element of `Γ`
(`h = u e_12(x_1) u^{-1}` for a suitable monomial substitution `u`), so
normality of `π(Γ)` forces `π(h) ∈ π(Γ)` in **every** finite quotient.  The
corrected `two-point-orbit-approximation` now carries that pair, and the open
content of the lane lives there.

The moral for the witness search: the obstruction was never the compression
semigroup as such — congruence quotients see it — but the marked element's
membership in the conjugacy closure of `Γ`, which no finite quotient can
break.

**Kernel-checked surface.**  Both halves of the dichotomy are formalized in
`GroupApproximation/Sofic/ProfiniteClosure.lean`: `not_mem_profiniteClosure`
(and its split-pair form `not_mem_profiniteClosure_of_kills`) is the
criterion behind item 1 — a single separating finite quotient certifies
`t ∉ Γ*` — and the closure-swallows-normal-closure theorem there is the
mechanism behind the contrast pair, since `h ∈ ⟨⟨Γ⟩⟩ ≤ Γ*`.  What this node
adds on top of the formalized criterion is the two-point *model*: the coset
labeling that turns the separating quotient into exact approximation data,
and the identification of the label space as `SL_d(ℤ/M)`.

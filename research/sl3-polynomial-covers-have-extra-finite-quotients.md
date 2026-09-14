---
rg: 2
id: sl3-polynomial-covers-have-extra-finite-quotients
kind: claim
title: Finitely presented covers of SL_3(F_q[t]) have finite quotients that do not factor through SL_3(F_q[t])
distinct_from:
  kazhdan-cover-models-round-iff-kernel-fixed-mass-one: that is the general criterion and its corollary for infinitely presented Kazhdan groups; this is the profinite hypothesis of the corollary at the one group SL_3(F_q[t]).
  fp-quotient-iff-kernel-finitely-normally-generated: that characterizes finite presentation of a quotient by finite normal generation of the kernel; this asks whether the kernels of the finitely presented covers stay visible in finite quotients, a profinite strengthening of non-finite-presentation.
---

**OPEN.**
- **Setting.** `Γ = SL_3(F_q[t])` is a Kazhdan group that is not finitely presented. By
  `fpbs-shalom-property-t-is-open` there is a finitely presented Kazhdan `Γ~` with
  `Γ ≅ Γ~/N`.
- **Claim.** For some such `Γ~` and some enumeration `N = {n_1, n_2, ...}`, put
  `Γ_L = Γ~/⟨⟨n_1, ..., n_L⟩⟩` and `K_L = ker(Γ_L -> Γ)`. Then for infinitely many `L`, `Γ_L`
  has a finite quotient in which `K_L` survives.

**Consequence if true.** By `kazhdan-cover-models-round-iff-kernel-fixed-mass-one`,
`SL_3(F_q[t])` is not flexibly HS-stable. Through the retract, neither is the rank-3 Kun--Thom
vertex (`el-r-vertex-instability-via-rank-three-covers`).

## Attempts

- **Profinite criterion: false for `q >= 4` (2026-09-13, lane `hl-hyperlinear-vs-sofic`).**
  - The sufficient condition "the profinite completion of `Γ` is not finitely presented" fails:
    `sl3-fq-t-profinite-completion-is-finitely-presented` proves
    `Γ^ ≅ SL_3(F_q[[t]]) × SL_3(F_q[t,t^-1])^`, a product of two finitely presented profinite
    groups, from the congruence subgroup property with trivial kernel, strong approximation,
    Capdeboscq's bounded presentations of `SL_3(F_q[t,t^-1])` and the Capdeboscq--Lubotzky--Rémy
    transfer to `F_q[[t]]` (`clr-profinite-presentations-and-csp-over-fq-t`).
  - As expected above, Behr's obstruction at `∞` is invisible profinitely. `q in {2,3}` is not
    covered.
  - **What is left, exactly** (`fp-cover-truncations-see-kernel-iff-profinite-closures-differ`):
    the claim holds for a given cover and enumeration iff for every `L` the truncation `Γ_L` has a
    different profinite completion from `Γ`, i.e. `cl(N_L) ≠ cl(N)` in `Γ~^`. Surviving at
    infinitely many `L` is the same as surviving at every `L`. Since `Γ^` is finitely presented,
    `cl(N)` is finitely normally generated as a closed normal subgroup, so the survivors cannot come
    from counting profinite relations; they must come from the specific truncation kernels
    (sector colimits, Krstić--McCool witnesses).
- **Ring-induced quotients are useless (elementary).** Suppose a quotient of `Γ_L` comes from
  `EL_3(B)` via a ring map `F_q[t] -> B`. Its image is a commutative ring, so the quotient factors
  through `Γ`. Extra quotients, if they exist, are not elementary groups over rings receiving
  `F_q[t]`.
- **Sector colimits (not attempted concretely).**
  - Soulé's picture: `Γ` acts on the Bruhat--Tits building of `SL_3(F_q((1/t)))` with a sector as
    strict fundamental domain, and `Γ` is the colimit of the finite vertex stabilizers over it.
  - Truncating the sector gives finitely presented covers.
  - An extra finite quotient would be a compatible family of maps of the finite vertex stabilizers
    over a truncated sector that does not extend to the whole sector.
- **Krstić--McCool (not read).** Their proof that `E_3` and `St_3` are not finitely presented over
  rings onto `F[t]` is recorded in the rank warning of `approximate-collapse-for-kt-compressor`. If
  its witnesses for nontriviality of the truncation kernels are finite or linear groups, they
  settle this claim.
- **Scope (2026-09-13).** The consequence is instability of the infinitely presented vertex
  `SL_3(F_q[t])`. It says nothing about the Laurent host `SL_3(F_q[t,1/t])`. The host is finitely
  presented: by the Bux--Köhl--Witzel rank theorem its local ranks add to `2+2`. So the
  infinitely-presented corollary of `kazhdan-cover-models-round-iff-kernel-fixed-mass-one` has no
  input there. See `sl3-laurent-f2-is-flexibly-hs-stable`.

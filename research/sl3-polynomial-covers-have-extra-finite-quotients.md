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

- **Profinite criterion (sufficient, undecided).**
  - It suffices that the profinite completion of `Γ` is not finitely presented as a profinite
    group.
  - Expected shape: up to the finite congruence kernel, this completion is the congruence
    completion `∏_(v≠∞) SL_3(O_v)`, a product over the finite places of `F_q(t)`. Neither the
    congruence subgroup property nor the kernel's value was verified here.
  - Whether such characteristic-`p` adelic groups are finitely presented was not checked. The arXiv
    API query from MSI returned nothing on 2026-09-13.
  - Behr's failure of finite presentation comes from the place `∞`, which the congruence completion
    does not see. So the criterion may well fail even though `Γ` is infinitely presented.
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

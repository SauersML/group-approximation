---
rg: 2
id: jacobson-image-of-five-transvection-group-is-sofic
kind: claim
title: The half-line image of the five-transvection group in GL_2 of the ternary Jacobson algebra is sofic
distinct_from:
  jacobson-elementary-subgroups-are-locally-finite-by-linear: that shows every subgroup of EL_n over a finite-field Jacobson algebra is locally finite by residually finite linear; this asks for soficity of one explicit subgroup of GL_2 over F_3, which that shape does not decide.
  five-transvection-group-acts-on-jacobson-half-line: that constructs the homomorphism onto this group and proves the eight defect elements stay distinct; this is the approximation property that would turn it into a weakly finite model.
---

**OPEN.** Let `J = F_3<S, T | TS = 1>` act on `F_3[N]`, `e = 1 - ST`, and
`Γ_V = <E_01(1), E_10(1), E_10(T), E_01(S), diag(1, 1 + S e)> <= GL_2(J)`. Claim: `Γ_V` is sofic.

**Payoff.** With `five-transvection-group-acts-on-jacobson-half-line` it gives
`five-transvection-group-has-weakly-finite-nonzero-defect` (route `weakly-finite-nonzero-defect-via-sofic-jacobson-image`),
which refutes `four-transvections-and-x23-force-defect-vanishing`. That closes the four-transvection lead of the
anti-central refutation program on `L_(F_3)(1,2)^x`, while leaving Gottschalk's conjecture itself open.

**Shape.** `Γ_V ∩ (I + M_2(M_∞(F_3)))` is a locally finite normal subgroup, and the quotient is a subgroup of
`SL_2(F_3[ζ, ζ^(-1)])`, which is residually finite and has the Haagerup property (it acts properly on the product of
the Bruhat–Tits trees at `ζ = 0` and `ζ = ∞`). Amenable-by-sofic groups are not known to be sofic in general
(`research/artifacts/four-transvection-escape-set-2026-09-12.md`, Section 5 item 2).

## Attempts

- 2026-09-14 `gk3-transvections`: opened as the concrete soficity refuter.
  - **Boundary compressions.** Compressing each generator to `[0, M)` in both copies gives unipotent matrices in
    `GL_(2M)(F_3)`. These realize `Γ_V` exactly on vectors far from `M`. Near `M` they realize the opposite boundary
    convention (`ST = 1`, `TS = 1 - E_(M-1,M-1)`), so they are not known to respect the relations of `Γ_V` on balls. Not
    tested, and no LEF or sofic model found.
  - **Rank compressions see only the symbol.** Compressions are rank-approximate homomorphisms, but every finitary
    element, `x_23(1)` included, has bounded rank defect. So they approximate the quotient
    `SL_2(F_3[ζ, ζ^(-1)])`, not `Γ_V`.
- 2026-09-14 `gk3-transvections`: structure (`jacobson-half-line-group-contains-finitary-sl`).
  - **The finitary part.** `Γ_V` contains every elementary transvection, so it contains the infinite simple group
    `SL_fin(F_3)`, and `x_23(1)` lies in it. So no finite quotient and no finite-dimensional model of `Γ_V` separates
    the defect, and `Γ_V` is not residually finite.
  - **Intrinsic form.** `[𝒯 : Γ_V] <= 2` for `𝒯 = π^(-1)(SL_2(F_3[ζ, ζ^(-1)])) <= GL_2(J)`. So this claim is
    equivalent to soficity of the symbol preimage `𝒯`, an extension of `SL_2(F_3[ζ, ζ^(-1)])` by `GL_fin(F_3)`.
  - **What a proof needs.** Sofic approximations in which finitary elements move a positive proportion of points,
    for example boundary-rich models with many independent half-line boundaries per window. Such an approximation
    must be sofic but not LEF-by-compression.

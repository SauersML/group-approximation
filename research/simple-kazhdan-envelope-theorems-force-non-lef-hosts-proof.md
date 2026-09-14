---
rg: 2
id: simple-kazhdan-envelope-theorems-force-non-lef-hosts-proof
kind: route
title: The Abels–Prüfer quotient is amenable, finitely presented and not residually finite, so no LEF group contains it
target: simple-kazhdan-envelope-theorems-force-non-lef-hosts
requires: [abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center, finitely-presented-lef-groups-are-residually-finite, amenable-implies-operator-mf]
---

1. **`Γ_p` is amenable, finitely presented and not residually finite.** Amenability and finite presentation are part of
   `abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center`. That node also gives a central `c_p ≠ 1` killed by
   every finite-dimensional unitary representation. A residually finite group has a finite quotient in which `c_p`
   survives, and the regular representation of that quotient would not kill `c_p`. So `Γ_p` is not residually finite.
2. **`Γ_p` is not LEF.** A finitely presented LEF group is residually finite
   (`finitely-presented-lef-groups-are-residually-finite`).
3. **`Γ_p` lies in every listed class.** Amenable groups are sofic (Weiss; Elek–Szabó), and sofic groups are
   hyperlinear and weakly sofic. They are linear sofic over any field, because permutation matrices satisfy
   `|{x : σx ≠ τx}|/2 ≤ rank(P_σ − P_τ) ≤ |{x : σx ≠ τx}|`: the rank of `I − P_π` is the number of points minus the
   number of cycles. Amenable groups are initially subamenable by definition, and operator-MF by
   `amenable-implies-operator-mf`.
4. **Conclusion.** Suppose `Γ_p ≤ H` with `H` an infinite finitely generated simple Kazhdan group in `P`. If `H` were
   LEF, its subgroup `Γ_p` would be LEF, contradicting step 2.

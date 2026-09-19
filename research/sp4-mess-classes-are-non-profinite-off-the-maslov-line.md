---
rg: 2
id: sp4-mess-classes-are-non-profinite-off-the-maslov-line
kind: claim
title: On normal congruence subgroups of Sp4(Z) the Torelli transgression classes carry non-profinite Q/Z-directions off the Maslov line, so Deligne's kernel is not the only non-profinite obstruction
distinct_from:
  deligne-covers-of-sp2g-z-have-finite-residual-2z: that is Deligne's theorem on the Maslov line itself (q times the universal-cover class is profinite only for q in (1/2)Z); this shows that on Gamma(3) and deeper normal subgroups the non-profinite part of H^2 with Q/Z coefficients is strictly larger than that line.
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that is the gap claim (B); this is an obstruction to one class of proofs of (B) for Torelli-abelian models and a divisibility constraint a | 20 on the untwisting constant.
---

**ESTABLISHED** through `sp4-mess-classes-non-profinite-off-maslov-line-proof`. Unreviewed; no novelty claimed.

**Setting.** `M = Mod(S_2)`, `pi : M -> Gamma = Sp_4(Z)`, `K = ker pi`, `b`, `f`, `r = a/10`, `sigma = f|_K / r`
as in `mod-s2-real-untwisting-identifies-deligne-norm-parameters` (U1). `Gamma_s = Stab_Gamma` of one
symplectic splitting of `Z^4`; splittings are `Gamma / Gamma_s`. For `Gamma' <= Gamma` of finite index put
`M' = pi^{-1}(Gamma')`, and let `D` run over the finitely many `Gamma'`-orbits of splittings, `m(Gamma')` their number.

- `chi_D : K -> Z` is the homomorphism equal to `1` on separating twists whose splitting lies in `D`, and `0` on
  the other separating twists. It is well defined and `M'`-conjugation invariant, and `sum_D chi_D = sigma`.
- `v_D in H^2(Gamma'; Z)` is the class of the pushout of `1 -> K -> M' -> Gamma' -> 1` along `chi_D`.
- `H^2_fin(Gamma'; Q/Z)` is the subgroup of classes inflated from finite quotients of `Gamma'`.
- `iota : H^2(Gamma'; Q) -> H^2(Gamma'; Q/Z)` is the coefficient map, and `beta(q) = iota(q res b)`.

**Statement.**

1. **(NP0) Transgression identity.** `sum_D v_D = -(10/a) res b` in `H^2(Gamma'; Q)`.
2. **(NP1) Divisibility.** `a` divides `20`. Together with `3 ∤ a` this gives `a in {±1, ±2, ±4, ±5, ±10, ±20}`.
3. **(NP2) Non-profinite Mess directions.** Let `Gamma'` be normal in `Gamma` with `m = m(Gamma')` not dividing
   `20/a`. Then for every orbit `D` the class `x_D = iota(v_D / m)`, of order dividing `m`, satisfies
   `x_D notin beta(Q) + H^2_fin(Gamma'; Q/Z)`.
4. **(NP3) Instances.** `m(Gamma(3)) = 45` and `m(Gamma(2)) = 10`. So (NP2) applies to `Gamma(3)` and to every
   normal subgroup of `Gamma` contained in `Gamma(3)`, where `m >= 45`. For a prime `p`,
   `m(Gamma(p)) = |Sp_4(F_p)| / (2 |SL_2(F_p)|^2) = p^2 (p^2 + 1) / 2`, which is `10` at `p = 2`, `45` at `p = 3`,
   and grows like `p^4 / 2`. At `Gamma(2)` there is no conflict when `a = ±2`, since `10 | 10`.

**Reading.** On a Torelli-abelian finite-image model the multiplier class is a real combination of `res b` and the
`v_D`. A hoped-for uniform floor says: modulo profinite classes only the Maslov line survives, with Deligne's kernel
`(1/2)Z`, so the Maslov coordinate is pinned up to the size of `h`. (NP2) refutes the premise. At `Gamma(3)`, and at
every deeper normal level with `h = 1/m -> 0`, the Mess classes carry non-profinite directions that are not on the
Maslov line. So a proof of the gap cannot read a single Maslov coordinate modulo profinite classes; it must control
the whole non-profinite quotient `H^2(Gamma'; Q/Z) / (beta(Q) + H^2_fin)`, which is nonzero at `Gamma(3)`.

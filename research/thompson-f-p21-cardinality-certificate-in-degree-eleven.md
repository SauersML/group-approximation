---
rg: 2
id: thompson-f-p21-cardinality-certificate-in-degree-eleven
kind: claim
title: Every pair in Guba's Problem P_(2,1) for Thompson's F has a common right multiple of degree eleven, certified by one explicit finite set
distinct_from:
  thompson-f-monomial-doubling-ratio-is-a-finite-computation: that reduces expansion ratios to finite universes; this exhibits one explicit certificate in degree eleven and the resulting degree bound for P_(2,1) and Q_2.
  thompson-f-one-bump-binomials-have-common-multiples: that settles twisted binomials against every element; this settles all pairs of degree-two combinations of five monomials, which are generally not products of binomials.
artifacts:
  - research/artifacts/thompson-f-monomial-doubling-2026-09-13.md
  - research/artifacts/thompson-f-monomial-doubling-2026-09-13-certificates/S21_11_13.txt.gz
  - research/artifacts/thompson-f-monomial-doubling-2026-09-13-certificates/X2_11_13.txt.gz
---

**ESTABLISHED** through `thompson-f-p21-cardinality-certificate-in-degree-eleven-proof` (explicit
certificate, checked by two independent programs; not independently reviewed).

Let `M` be the positive monoid of `F`. `S_(2,4) = {x_0^2, x_0x_1, x_0x_2, x_1^2, x_1x_2}` is the set of
Guba's Problem `P_(2,1)`, and `A = X_2 = {x_0, x_1, x_2}`.

1. **Degree eleven for `P_(2,1)`.** There is an explicit `Y ⊆ M_(11,13)` with `|Y| = 160430` and
   `|S_(2,4) Y| = 318148 < 2|Y|`. So over every field `K`, every pair of nonzero
   `a, b ∈ K[S_(2,4)]` has nonzero homogeneous `u, v` of degree `11` with `a u = b v`.
2. **No cardinality certificate below degree eleven.** `Λ_(S_(2,4))(10) = 148838/73690 ≈ 2.0198`,
   and `Λ` is nonincreasing, so no finite `Y` of degree `<= 10` has `|S_(2,4) Y| < 2|Y|`.
3. **Degree eleven for `Q_2`.** There is an explicit `Y' ⊆ M_(11,13)` with `|Y'| = 196488` and
   `|A Y'| = 293376 < (3/2)|Y'|`. So every system
   `(α_0x_0+β_0x_1+γ_0x_2)u_0 = (α_1x_0+β_1x_1+γ_1x_2)u_1 = (α_2x_0+β_2x_1+γ_2x_2)u_2`
   has a solution with all `u_i` nonzero and homogeneous of degree `11`. No such `Y'` exists in
   degree `<= 10`: `Λ_A(10) = 111264/73690 ≈ 1.5099`.

**Comparison with the survey** (V. Guba, arXiv:2305.07113v4). Theorem `s24` gives `P_(2,1)`
solutions with `deg u, v <= 41`. For `Q_2` the survey says "The estimate there will be also
$n\ge45$", and it obtains the stronger `|AY| < (4/3)|Y|` with a set whose "size ... is really huge".
Items 1 and 3 lower these recorded degrees to `11`. The source of `s24`, Guba arXiv:2101.01848
(`grringf.tex`, l.395), says: "Notice that we do not know what is the minimum degree of $u$, $v$ for
solutions of this equation. A rough computer search can show that $n > 10$, but we do not even know
whether the minimum value of $n$ is close to $10$ or $40$." There, `Y ⊆ S_(4,n)` consists of
monomials of degree `n - 4`. For the cardinality method, item 2 settles where the minimum lies:
degree `11`, i.e. `n = 15`, over all finite `Y ⊆ M`. That question for arbitrary solutions stays open. Item 2 concerns cardinality certificates only; individual pairs can have
solutions of lower degree.

Certificates: `research/artifacts/thompson-f-monomial-doubling-2026-09-13-certificates/`.

---
rg: 2
id: sl3-polynomial-congruence-subgroups-have-large-b2
kind: claim
title: Given Soulé's strict fundamental domain, the congruence subgroups of SL_3(F_q[t]) computed at q = 2, 3 and level degree 2 or 3 have large second Betti number
distinct_from:
  sl3-polynomial-finite-index-z-extension-center-survives: that is the open premise, asking for a central Z-extension of a finite-index subgroup with the centre visible in finite quotients; this establishes only its necessary first step, nonzero real H^2, at explicit congruence levels.
  finite-multiplier-projective-models-round-strictly: that voids scalar-cocycle instability at groups with finite H_1 and H_2; this shows that the congruence subgroups of the one-variable retract of the Kun--Thom vertex are not such groups.
---

**ESTABLISHED, conditional on the named hypothesis (S).**

Reviewed in `research/artifacts/ex-review2-dynamics-2026-09-13-part1.md`, §1.6. Verdict: PASS as a
conditional statement, with the `D = 2` rows re-derived by hand. The title was corrected on 2026-09-13
because it asserted every level of degree at least 2 and did not name (S).

**Setting.**
- `X` is the Bruhat--Tits building of `SL_3(F_q((1/t)))`, and `Q` the sector of the standard
  apartment with vertices `(a,b)`, `a >= b >= 0`, where `(a,b)` is the lattice class of
  `diag(t^a, t^b, 1)`.
- `Γ = SL_3(F_q[t])`. For `f ∈ F_q[t]` of degree `D >= 1`, put `A = F_q[t]/(f)` and
  `Γ(f) = ker(Γ -> SL_3(A))`.

**Hypothesis (S), Soulé.** `Q` is a strict fundamental domain for the action of `Γ` on `X`.
This is not source-verified in this lane.

**Theorem.**
1. **Stabilizers.** `Γ_(a,b)` consists of the matrices in `Γ` whose entry `g_ij` has degree at
   most `a_i - a_j`, with `(a_1,a_2,a_3) = (a,b,0)` and entries of negative bound equal to 0.
   The stabilizer of a cell is the intersection of its vertex stabilizers.
2. **Cell counts.** The quotient complex `Y = Γ(f)\X` has exactly
   `N(σ) = |SL_3(A)| / |π(Γ_σ)|` cells over each cell `σ` of `Q`. Here `π(Γ_σ)` is the reduction
   of `Γ_σ`: block upper triangular matrices with Levi entries in `F_q` and upper entries in the
   image `V_d ⊂ A` of polynomials of degree `<= d`, where `dim V_d = min(d+1, D)`.
3. **Cohomology.** `H^i(Γ(f);R) = H^i(Y;R)`, which vanishes for `i >= 3`. With `Y_R` the
   preimage of the truncation `{a <= R}` of `Q`, the inclusion `Y_R ⊂ Y_(R+1)` is a sequence of
   elementary collapses once `R >= max(1, 2D-2)`. Hence

   ```text
   b_2(Γ(f)) = χ(Y_(R_0)) - 1 + b_1(Γ(f)),     R_0 = max(1, 2D-2),
   χ(Y_R) = Σ_(σ ⊂ Q, a <= R) (-1)^(dim σ) N(σ).
   ```

   So `b_2 >= χ(Y_(R_0)) - 1`, with equality because `Γ(f)` is Kazhdan (finite index in the
   Kazhdan group `SL_3(F_q[t])`).
4. **Values** (MSI computation, stable from `R = 2D-2` through `R = 12`):

   | q | level f | χ(Y) | b_2(Γ(f)) |
   | --- | --- | --- | --- |
   | 2 | t (D=1) | 1 | 0 |
   | 2 | t^2 | 928 | 927 |
   | 2 | t(t+1) | 609 | 608 |
   | 2 | irreducible quadratic | 1305 | 1304 |
   | 2 | t^3 | 431104 | 431103 |
   | 3 | t | 1 | 0 |
   | 3 | t^2 | 132921 | 132920 |
   | 3 | t(t+1) | 113776 | 113775 |
   | 3 | irreducible quadratic | 153160 | 153159 |
   | 3 | t^3 | 1123879617 | 1123879616 |

   - At level `t` the quotient is the cone over the spherical building of `SL_3(F_q)`. It is
     contractible and `χ = 1`, which is the calibration.
   - At every computed level of degree `>= 2`, `H^2(Γ(f);R) ≠ 0`, and integral classes with
     nonzero real image exist.

Derivation: `sl3-polynomial-congruence-subgroups-have-large-b2-proof`. Script and raw output:
`research/artifacts/sl3-congruence-b2-euler-2026-09-13.md`.

**Reading for the instability routes.**
- Scalar-cocycle instability is void at the Kun--Thom vertex whenever its multiplier is finite
  (`finite-multiplier-projective-models-round-strictly`). It is not void at these congruence
  subgroups of the one-variable retract, which carry thousands of real degree-two classes. So the
  first requirement of `sl3-polynomial-finite-index-z-extension-center-survives` holds at the
  computed levels.
- What remains open is whether some such class has a central `Z`-extension whose centre survives
  at unbounded orders in finite quotients.
- Positivity for all `(q,f)` with `D >= 2` is not proved. It is observed at the ten listed cases
  only.

---
rg: 2
id: harder-function-field-s-arithmetic-cohomology-vanishing
kind: claim
title: Harder 1977 - congruence subgroups of split simply connected groups over function-field S-integers have rational cohomology only in degrees 0 and r|S|
distinct_from:
  sl3-polynomial-congruence-subgroups-have-large-b2: that computes the top-degree Betti number b_2 of congruence subgroups of SL_3(F_q[t]) from cell counts; this is the general vanishing theorem below the top degree, for every nonempty S, together with the identification of the top degree with Steinberg multiplicities.
---

**ESTABLISHED (import).** Let `K/F_q` be a function field of transcendence degree 1,
`S` a nonempty finite set of places of `K`, `O_S` the ring of elements of `K` integral outside
`S`, `G_0/F_q` a simply connected simple Chevalley group of rank `r`, and `Γ` a congruence
subgroup of `G_0(O_S)`. Then:

1. `H^ν(Γ;Q) = 0` for `ν ≠ 0, r|S|`.
2. For `d = r|S|`, `dim H^d(Γ;Q)` is finite and equals the multiplicity of the special
   (Steinberg) representation `⊗_(v∈S) π_(v,sp)` of `∏_(v∈S) G(K_v)` in the discrete spectrum of
   `L^2(∏_(v∈S) G(K_v)/Γ)`.

Source: G. Harder, *Die Kohomologie S-arithmetischer Gruppen über Funktionenkörpern*,
Invent. Math. 42 (1977) 135--175, doi:10.1007/BF01389786. The main result is stated in the
Einleitung, pp. 135--136. Route: `harder-function-field-s-arithmetic-cohomology-vanishing-citation`.

**Instances used in the graph.**
- `SL_3(F_q[t])`, `S = {∞}`: rational cohomology of congruence subgroups lives in degrees 0 and
  2. This agrees with `sl3-polynomial-congruence-subgroups-have-large-b2`, which found `b_1 = 0`
  and large `b_2`.
- `SL_3(F_q[t,1/t])`, `S = {0,∞}`, `r|S| = 4`: every congruence subgroup has `H^1 = H^2 = H^3 = 0`
  with rational coefficients. See `laurent-sl3-real-cohomology-from-chamber-quotient` and
  `laurent-sl3-central-covers-never-witness-instability`.
- `SL_2(F_q[t,1/t])`: degrees 0 and 2.

**Reading.** Harder describes the result as a function-field extension of Garland's vanishing
theorem, which is for cocompact lattices in `p`-adic groups, with Casselman's removal of Garland's
restriction on the residue field. Here the groups are not cocompact.

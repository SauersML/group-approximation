---
rg: 2
id: f-unit-fields-are-characterized-by-isolated-sign-units
kind: claim
title: A real number field inside Q(β) for an (F) unit β must have a unit whose sign at one real place is opposite to its sign at every other real place; for totally real fields this is also sufficient, and Q(√3) lies in no (F)-unit field
distinct_from:
  every-real-number-field-lies-in-an-f-unit-field: that asked whether every real field lies in some (F)-unit field; this refutes it (Q(√3)) and replaces it by a sign condition that is necessary in general and sufficient for totally real fields.
  pisot-interval-exchange-groups-satisfy-boone-higman: that proves Boone--Higman over (F)-unit fields; this determines which fields those are.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**ESTABLISHED** (lane proof, not reviewed; no priority claimed).

**Inputs read at source:**
- Akiyama, "Pisot numbers and greedy algorithm", Proposition 1: a real algebraic integer `β > 1` with another
  positive real conjugate lacks (F'), which is our (F);
- Frougny--Solomyak's Theorem A, as stated verbatim in Akiyama--Rao--Steiner, J. Number Theory 107 (2004),
  p. 2: the dominant root of `x^d − b_1x^{d−1} − … − b_d` with `b_1 ≥ … ≥ b_d > 0` is Pisot with (F).

Say a unit `η ∈ O_K^×` has an **isolated sign at the real place `v_0`** if
`sign(η_{v_0}) ≠ sign(η_v)` for every real place `v ≠ v_0`. When `K` has one real place this is automatic.

## Statement

Let `K` be a real number field.

1. **Necessary.** Suppose `K ⊆ Q(β)` for an algebraic unit `β > 1` with (F), and let `v_0` be the real place of
   `K` induced by `Q(β) ⊆ R`. Then `N_{Q(β)/K}(β)` is a unit of `K` with an isolated sign at `v_0`.
2. **Totally real fields.** If `K` is totally real, the following are equivalent:
   - `K ⊆ Q(β)` for some unit `β > 1` with (F);
   - `K = Q(β)` for such a `β`;
   - `K` has a unit with an isolated sign at some real place.
3. **A sufficient condition with complex places.** Suppose `K` has a unit with an isolated sign at `v_0`, and
   the arguments at the complex places of the totally positive units are dense in `(S^1)^{r_2}`. Then `K = Q(β)`
   for a unit `β > 1` with (F).

## Consequences

- **Quadratic fields.** `Q(√D)` lies in some (F)-unit field iff it has a unit of norm −1. So `Q(√3)`, `Q(√6)`,
  `Q(√7)`, `Q(√11)`, … lie in none, and `every-real-number-field-lies-in-an-f-unit-field` is **refuted**.
- **Cubic fields.** Every cubic field with one real place is an (F)-unit field.
  - Its units are `±u^k`. The argument `θ` of the complex conjugate `u'` of `u` has `θ/π` irrational: if `u'^N`
    were real, `u^N` would have a repeated conjugate, so `u^N ∈ Q` and `u^N = ±1`.
  - So item 3 applies. This covers, for example, all pure cubic fields `Q(m^{1/3})`.
- **Totally real cubic fields** are (F)-unit fields exactly when some unit has an isolated sign.
- **For Boone--Higman.** `pisot-interval-exchange-groups-satisfy-boone-higman` therefore covers all interval
  exchange groups with parameters in fields of the kinds above. Fields such as `Q(√3)` must be handled by
  other routes, for example bh-free-03's substitutive route for `IET(Z+αZ)`.

## Proof

1. **Necessity.** Put `L = Q(β)`, and use that embeddings of `L` correspond to conjugates of `β`.
   - The real conjugates other than `β` are negative, by Akiyama's Proposition 1.
   - For a real place `v` of `K`, `N_{L/K}(β)_v` is the product of `τ(β)` over the embeddings `τ` of `L` above
     `v`. Complex ones come in conjugate pairs and contribute positive factors. The real ones number `r_v`,
     and `r_v ≡ [L:K] (mod 2)`, since that is the number of real roots of a real polynomial of degree `[L:K]`.
   - Above `v_0` exactly one real `τ` gives `β > 0`. So `sign N_{v_0} = (−1)^{r_{v_0}−1}` and
     `sign N_v = (−1)^{r_v}` for `v ≠ v_0`.
   - These are opposite. The norm is a unit because `β` is.
2. **Sufficiency, totally real.**
   - **Setup.** Let `ε_0 = ±η` have sign `+` at `v_0` and `−` elsewhere.
     - By Dirichlet, pick a unit `u` with `|u_v| < 1` for all `v ≠ v_0`, with the values `|u_v|` pairwise
       distinct. This is an open condition on the log lattice.
     - Put `w = u²`, which is totally positive, and `β_N = ε_0 w^N`.
   - **Large `N`.** For large `N`:
     - `β_N > 2` at `v_0`;
     - the other `n − 1` conjugates are negative, pairwise distinct, and of total absolute value `≤ 1/2`;
     - so `Q(β_N) = K`.
   - **Coefficients.** With `c_v = −β_{N,v} > 0` and `e_k = e_k(c)`, the minimal polynomial is
     `(x−β_N)∏(x + c_v) = x^n − b_1x^{n−1} − … − b_n`, with `b_1 = β_N − e_1`, `b_k = β_N e_{k−1} − e_k` and
     `b_n = β_N e_{n−1} = 1`.
   - **Monotonicity.** From `e_1 ≤ 1/2` and `e_{k−1}e_1 ≥ e_k` we get `e_k ≤ e_{k−1}/2`. Then
     `b_k − b_{k+1} = β_N(e_{k−1} − e_k) − (e_k − e_{k+1}) ≥ e_k − e_k + e_{k+1} ≥ 0`. So
     `b_1 ≥ … ≥ b_n = 1 > 0`, and Frougny--Solomyak's Theorem A gives (F).
3. **Sufficient condition with complex places.**
   - **Positive coefficients.** Suppose all other conjugates lie in the sector `|arg(−z)| ≤ φ` with
     `(n−1)φ ≤ π/3`, and have total modulus `≤ 1/4`. Then the `e_k` of the negated conjugates are positive reals,
     with `e_k ≥ e_k(|z|)/2` and `e_k ≤ e_{k−1}/2`. So the same coefficient computation gives Theorem A's form,
     with `b_n = 1`.
   - **Finding such a unit.** Take units `ε_0 w^N y` with `y` totally positive and `|log y| ≤ R`.
     - For `N` large they are deep in the small cone, with distinct moduli at distinct places.
     - Their arguments `arg ε_0 + arg w^N + arg y` fill a `φ`-dense set of the torus as `R` grows, by the density
       hypothesis. So some has all complex arguments within `φ` of `π`, and none equal to `π`.
   - **Conclusion.** Its conjugates are distinct, so `Q(β) = K`. ∎

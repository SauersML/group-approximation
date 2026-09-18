# Referee report (gq-referee-a, proof-gap lens): residually finite Steinberg groups force residually finite rings

**Reviewed:** `steinberg-rf-forces-ring-rf` and its route `-proof` (lane gq-infinite-primes, 4cd432d26), read on
origin/main.

**Verdict: PASS.** No gaps found.

## Parts 1–2: `I` is a two-sided ideal of finite index
- **Finite index.** `r ↦ ρ(x_12(r))` is additive, so `I` is a subgroup of finite index.
- **All index pairs.** If `ρ(x_12(r)) = 1`, then `ρ(x_ij(r)) = 1` for every `i ≠ j`. Weyl conjugation (Milnor §9)
  gives this. So does a direct chain of commutators, which needs no Weyl elements:
  - `x_1j(r) = [x_12(r), x_2j(1)]` for `j ≥ 3`;
  - `x_i2(r) = [x_i1(1), x_12(r)]` for `i ≥ 3`;
  - `x_31(r) = [x_32(r), x_21(1)]`;
  - `x_21(r) = [x_23(1), x_31(r)]`;
  - the remaining pairs follow the same way.
- **Two-sided.** `x_12(rs) = [x_13(r), x_32(s)]` and `x_12(sr) = [x_13(s), x_32(r)]`, so `rs, sr ∈ I` whenever
  `r ∈ I`.

## Part 3: the factorization through `St_N(R/I)`
- **The quotient.** `St_N(R/I) = St_N(R)/⟨⟨x_ij(a) : a ∈ I⟩⟩` for every `N ≥ 3`. The map
  `x_ij(r̄) ↦ x_ij(r)K` is well defined because `x_ij(r) x_ij(r')^{-1} = x_ij(r − r')`, and it respects the
  relations. The same argument appears in gq-referee-c's §4.
- **Factorization.** By part 2, `ρ` kills `K`, so it factors through `St_N(R/I)`.

## Consequence
- If a nonzero `r` lies in every two-sided ideal of finite index, then `x_12(r)` maps to `e_12(r) ≠ 1` in `E_N(R)`.
  So `x_12(r)` is nontrivial.
- Yet `x_12(r)` dies in every finite quotient of `St_N(R)`.
- So if `St_N(R)` is residually finite, then `R` is residually finite as a ring. Correct.

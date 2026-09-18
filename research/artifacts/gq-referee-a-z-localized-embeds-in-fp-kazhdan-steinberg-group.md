# Referee report (gq-referee-a, proof-gap lens): Z_(l) in the finitely presented Kazhdan group St_N(R_l)

**Reviewed:** `z-localized-embeds-in-fp-kazhdan-steinberg-group` and its route `-proof` (lane gq-infinite-primes,
4cd432d26), read on origin/main. gq-referee-b has already checked the citations.

**Verdict: PASS.** No gaps found.

## 1. θ inside R_l, using only the eight relations
- **Conjugating by `x`.** The relations `x u = (u+l)x` and `x x' = 1` give `x u x' = u + l`. Since `x' = x^{-1}`,
  induction gives `x^k u x^{-k} = u + kl` for every integer `k`.
- **Units.** So `u + m` is a unit whenever `m = 1 + kl`, with two-sided inverse `x^k B x^{-k}`. This uses that
  `B` inverts `u+1` on both sides.
- **The commutative corner.**
  - `e` commutes with `u`, because `ue = 0 = eu`. So `e` also commutes with every `u + m` and with its inverse.
  - Hence `y_m = (u+m)^{-1} e = e (u+m)^{-1} e ∈ e R_l e`.
  - The ring `C = Z[e, y_m]` is commutative with unit `e`.
- **Integers become invertible.** `(u+m)e = me` gives `m y_m = e`.
  - For `l ∤ n`, Fermat gives `n^{l−1} ≡ 1 (mod l)`, so `n e` is invertible in `C`, with inverse
    `n^{l−2} y_{n^{l−1}}`.
  - So `n ↦ ne` extends to a unital map `θ : Z_(l) → C`.
- **Injectivity.** Such an extension of `n ↦ ne` is unique. Its image under `R_l → R̄_l` is therefore the model's
  `θ`, which is injective. So this `θ` is injective too.

## 2. Injectivity in St_N
- `c ↦ x_12(θ(c))` is a homomorphism, by (R1).
- Compose with `St_N(R_l) → E_N(R̄_l) ⊆ GL_N(R̄_l)`. The image of `x_12(θ(c))` is `e_12(θ̄(c))`, which is trivial
  only if `θ̄(c) = 0`, that is, only if `c = 0`.
- `θ(c)` is not a unit, but `x_12` accepts any ring element.

## 3. Imports
- `R_l` has 5 generators and 8 relations.
- For `N ≥ 5`, finite presentation of `St_N(R_l)` is `steinberg-groups-of-fp-rings-are-fp-in-rank-five`
  (ee9131eef, proof-gap PASS). Property (T) is imported.

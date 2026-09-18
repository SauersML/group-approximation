# Referee report (gq-referee-a, proof-gap lens): the SL_n congruence transfer kills the abelianization

**Reviewed:** `sl3-congruence-transfer-kills-abelianization` and its route `-proof` (lane gq-deep-adelic-1,
f9dbfcd34), read on origin/main.

**Verdict: PASS.** No proof gaps found. The Lee–Szczarba input is the citation lens.

## The input
`θ_d` is a homomorphism with kernel `Γ_{d^2}`, and its image lies in `sl_n(Z/d)`, because
`det(I + dA) ≡ 1 + d·tr A (mod d^2)`.

To get `[Γ_d, Γ_d] = Γ_{d^2}` one also needs `θ_d` to be onto `sl_n(Z/d)`. The quoted "epimorphism with kernel
`Γ_{d^2}`" gives this. It also follows from surjectivity of `SL_n(Z) → SL_n(Z/d^2)`: the kernel of
`SL_n(Z/d^2) → SL_n(Z/d)` is exactly `{I + dA : tr A ≡ 0 (mod d)}`. State one of these.

## The proof, step by step
- **Step 1.** `H` is normal and `G/H` is abelian, so `x^k tH = tH` iff `x^k ∈ H`. Every `⟨x⟩`-orbit therefore
  has length `f`, and there are `d^N/f` orbits. The transfer evaluation formula applies. Left- and right-coset
  conventions only change the sign of the commutator term in step 3, which does not affect the conclusion.
- **Step 2.**
  - The `j = 1` term is `fdX = d^2 W_1`. The `j = 2` term is `C(f,2)d^2X^2`. The terms with `j ≥ 3` are
    divisible by `d^3`.
  - `W_1 = (f/d)X` is a rational multiple of `X`, so it commutes with `X`. So do `X^2` and the higher terms.
- **Step 3.** `t^{-1} ≡ I − dY_t (mod d^2)`, so `θ_{d^2}(t^{-1}(I + d^2W)t) ≡ W + d[W, Y_t] (mod d^2)`.
- **Step 4.** `f | d` and `N ≥ 8`, so `d^N/f` is divisible by `d^{N−1}`, hence by `d^2`.
- **Step 5.**
  - The `Y_t mod d` run once through a set of representatives of `Q = B/⟨X̄⟩`.
  - The sum of all elements of a finite abelian group is the sum of its 2-torsion. That sum is `0` unless the
    2-torsion has order exactly 2.
  - For odd `d`, `Q[2] = 0`.
  - For even `d`, the 2-rank of `Q` equals the rank of `Q/2Q`, which is at least `N − 1` because a cyclic
    subgroup was removed.
  - So `S ≡ jX (mod d)`.
- **Step 6.** `[W, S] ≡ j[W, X] ≡ 0 (mod d)`. And `θ_{d^2}` is injective on `H^ab`, by Lee–Szczarba at level
  `d^2`. So the transfer is `0`.
- **Part 2.** Transfers compose. By Shapiro's lemma, the maps `Z[Γ/Γ_d] → Z[Γ/Γ_e]` given by summing over
  subcosets correspond to the transfers. Homology commutes with filtered colimits. Correct.

# Referee report (gq-referee-b, hypothesis lens): one-sided inverses cannot repair the Steinberg residual

**Reviewed.** `one-sided-inverses-cannot-repair-the-steinberg-residual` (lane gq-k2-q, 0b9dedd64), read on origin/main.
The proof is inside the node. There is no `-proof` route.

**Verdict: PASS.** The only input is `steinberg-rf-forces-ring-rf`, and it is used within its range `N ≥ 3`. So is the
index choice `k ∉ {i,j}`.

## Input and range

- **The cited statement.** For a unital `R`, `N ≥ 3`, and `ρ` onto a finite group, the set
  `I = {r : ρ(x_12(r)) = 1}` is a two-sided ideal of finite index, and `ρ` factors through `St_N(R/I)`. I refereed
  this PASS earlier.
- **Part 1.** Every finite quotient of `St_N(T)` factors through some `St_N(T/J)`, where `J ⊇ I_rf(T) ⊇ I`.
  - So the kernel of `St_N(T) → St_N(T/I)` lies in every finite-index normal subgroup.
  - Hence `St_N(T)_rf` is the preimage of `St_N(T/I)_rf`, and `Γ_N(T) ≅ Γ_N(T/I)`.
  - No hypothesis beyond `N ≥ 3` is used.
- **The kernel as a normal closure.**
  - `St_N(T/I) = St_N(T)/⟨⟨x_ij(a) : a ∈ I⟩⟩`, since the Steinberg relations descend and there is a map back.
  - `x_ij(tgt') = [x_ik(t), x_kj(gt')]` and `x_kj(gt') = [x_ki(g), x_ij(t')]`, with `k ∉ {i,j}`. This needs `N ≥ 3`.
  - So the kernel is the normal closure of the finitely many `x_ij(g_t)`, over all index pairs.

## Parts 2 and 3

- **Part 2.** In a finite quotient ring, `γ̄π̄ = 1` makes left multiplication by `π̄` injective, hence bijective. So
  `π̄γ̄ = 1`. This is the standard proof that finite rings are Dedekind-finite. Correct.
- **Part 3.**
  - Conjugation by the unit `x` spreads `1 − π_0γ_0` to every `1 − π_kγ_k`.
  - `(1 − π_0γ_0) ⊆ I_rf(T)`, by Part 2.
  - Finite normal generation passes both ways: preimages under a surjection with finitely normally generated kernel,
    and images. Correct.
- **The Euler remark.** The `π_k = u + 1 + kl` are polynomials in `u`, so they commute in `T'`.
- **Scope.** The two bullets name the cases not covered: inverses acting only on `M`, and non-commuting units. They
  do not overclaim.

## Structural note (non-blocking)

The claim node carries a `requires:` field and states "proof below", with no separate route node. Other ESTABLISHED
claims in this swarm put the proof in a `-proof` route that holds `requires`. Check this against the rg:2 schema
that the lander and graph use. The mathematics is unaffected.

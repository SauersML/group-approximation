# Defect-uniform division criterion, and what it forces over the Hilbert cube (2026-09-13)

Lane `ex2-tw-hilbert-cube-boundary` (EX swarm). Refines Proposition 8.2 and Corollary F of
`research/artifacts/ex-tw-c-space-unit-division-part4-2026-09-13.md` (lane `ex-tw-rotation-gluing`).
Notation and facts (F1)–(F5), Lemma 3 and Section 3 are those of parts 1–2
(`research/artifacts/ex-tw-c-space-unit-division-2026-09-13.md`, `-part2-`). Not reviewed.

**Outcome.**
- **Proposition H.2.** In the summable-division criterion, the trace deficits `δ_i` of the
  division sets need only a uniform bound. Only the matrix sizes have to be summed:
  `Σ_{i : λ ∈ O_i} 1/N_i ≤ κ`.
- **Corollary H.3.** A metric criterion in which the defect is held fixed.
- **Corollary H.4.** Over the Hilbert cube, a strict-comparison algebra with an indivisible
  unit has some `κ_0 > 0` such that division sets of matrix size `N` and fixed defect `κ_0`
  have Lebesgue number at most `16 · 2^{−κ_0 N}`. Confinement driven by the defect cannot
  make a counterexample.

**Setting.** `A` is unital, simple, separable, exact and non-elementary, with strict
comparison and a nonempty Bauer simplex with extreme boundary `K`. A *division set*
`(O, φ, N, δ)` is an open `O ⊆ K` with a c.p.c. order zero `φ: M_N → A` and
`λ(1 − φ(1)) < δ` for every `λ ∈ O`, where `0 < δ ≤ 1`.

## H.1 The staircase defect, charged per piece

**Lemma H.1.** In the setting of Lemma 3 (part 1), for every `λ ∈ K`:
```text
λ(B − B²)  ≤  1/(4N) + δ/N + t h(λ) δ.
```
*Proof.*
- If `h(λ) = 0`, Lemma 3(i) gives `λ(B − B²) = 0`. Suppose `h(λ) > 0`, so `λ ∈ supp h`. Put
  `x = N t h(λ)` and `c_j = clamp(x − j + 1)`.
- As in Lemma 3, `λ(B − B²) = Σ_j (c_j − c_j²) λ(e_j) + Σ_j c_j² λ(e_j − e_j²)`. The first
  sum is at most `1/(4N)`, as there.
- **Per-piece defect.** Let `f(s) = s − s²`. By order zero functional calculus, `f(φ)` is a
  c.p. order zero map `M_N → M` with `f(φ)(e_jj) = e_j − e_j²`. (F4) applied to `f(φ)` makes
  `λ ∘ f(φ)` tracial on `M_N`. So all `λ(e_j − e_j²)` are equal, with sum
  `λ(φ(1) − φ(1)²) ≤ λ(1 − φ(1)) < δ`. Each is therefore below `δ/N`.
- **Count.** `c_j > 0` only for `j < x + 1`, hence for at most `x + 1` indices. The second
  sum is at most `(x + 1)δ/N = t h(λ)δ + δ/N`. ∎

Lemma 3 charged the full `δ` to every active member. Lemma H.1 charges `δ/N` per member and
`t h(λ) δ` in proportion to the profile. Since `Σ_i h_i = 1`, the proportional parts sum to at
most `t · max_i δ_i`.

## H.2 Defect-uniform summable division

**Proposition H.2.** The unit of `A` is tracially `N`-divisible for every `N` iff for every
`κ > 0` some finite family of division sets `(O_i, φ_i, N_i, δ_i)`, `i = 1, …, m`, covers `K`
and satisfies
```text
(a)  Σ_{i : λ ∈ O_i} 1/N_i ≤ κ  for every λ ∈ K,        (b)  δ_i ≤ κ  for every i.
```

*Proof of (⟹).* Given `κ`, take `N ≥ 1/κ` and order zero `φ: M_N → A` with `τ(1 − φ(1)) < κ`
for every trace. The single division set `(K, φ, N, κ)` works.

*Proof of (⟸).* Fix `n ≥ 1`. As in Section 3 put `t = (2n+1)/(2n(n+1))` and
`γ = 1/(2n(n+1))`, and then `ε_0 = γ/2 ≤ 1/8`, `s = ε_0/8` and `κ = ε_0²/384`. Take a family as
in the statement for this `κ`.
- **Staircases.** Choose a partition of unity `h_1, …, h_m` with `supp h_i ⊆ O_i`. Lemma 3 with
  `(φ_i, h_i, t)` gives `B_i`, with defect bounded by Lemma H.1. Put
  `D_i(λ) = 1/(4N_i) + δ_i/N_i + t h_i(λ)δ_i`.
- **Approximants.** Choose `η > 0` with `16mη/s ≤ ε_0/8` and `7mη ≤ ε_0/16`, and (F5) approximants
  `b_i ∈ A` with `‖b_i − B_i‖_{2,u} ≤ η`. Cut at `x_i = (b_i − s)_+`, and run the moves of
  Section 3, Step 5 in the order `i = 1, …, m`. The cut levels satisfy `σ_i ∈ [s, 1/2]`.
- **Per-member bounds** for `σ ∈ [s, 1/2]`. Call member `i` active at `λ` if `h_i(λ) > 0`, which
  forces `λ ∈ O_i`.
  - Upper, active, by (F2) at `s` and monotonicity:
    `μ_{b_i,λ}((σ,1]) ≤ (t h_i(λ) + η)(1 + 2s) + 2(D_i(λ) + 3η)/s`.
  - Upper, inactive, by Lemma 3(i) and (F2): `μ_{b_i,λ}((σ,1]) ≤ 8η/s`.
  - Lower, active, by Lemma 8.1 (part 4):
    `μ_{b_i,λ}((σ,1]) ≥ t h_i(λ)(1 − δ_i) − η − 2(D_i(λ) + 3η)`. Lower, inactive: `≥ 0`.
- **Summing at `λ`.** By (a) and (b), `Σ_{i active} D_i(λ) ≤ 2Σ_{i : λ ∈ O_i} 1/N_i + tκ ≤ 3κ`.
  Using `Σ_i h_i = 1`:
  ```text
  upper:  Σ_i μ_{b_i,λ}((σ_i,1])  ≤  t + 2st + 6κ/s + 16mη/s  ≤  t + ε_0/4 + ε_0/8 + ε_0/8,
  lower:  Σ_i μ_{b_i,λ}((σ_i,1])  ≥  t − tκ − 6κ − 7mη        ≥  t − ε_0/16 − ε_0/16.
  ```
  Here `6κ/s = ε_0/8`, and `7κ ≤ ε_0/16` because `ε_0 ≤ 1/8`.
- **Margins.** Every move of Step 5 needs `d_λ(F_{k−1}) − d_λ(x_k) ≥ 1 − (upper total)`, which is at
  least `1 − t − ε_0/2 ≥ 1 − 3/4 − 1/16 > 1/8`. So strict comparison applies after integrating
  over `μ_τ` (F1).
- **Conclusion.** The orthogonal sum `W` has `|d_λ(W) − t| ≤ ε_0/2 < γ` on `K`, hence at every
  trace, and Step 7 of Section 3 gives `n[W] ≤ [1_A] ≤ (n+1)[W]`. As `n` is arbitrary,
  `strict-comparison-unit-divisibility-equivalences` gives tracial `N`-divisibility. ∎

## H.3 Metric form, and the Hilbert cube

Fix a compatible metric on `K`. For `N ≥ 1` and `0 < δ ≤ 1`, let `𝒟_A(N, δ)` be the family of
open `O ⊆ K` carried by some division set `(O, φ, N', δ')` with `N' ≥ N` and `δ' ≤ δ`. By Lemma 1
(part 1) it covers `K`. Let `ℓ_A(N, δ) ∈ (0, ∞]` be its Lebesgue number, and `ord_K(r)` the least
order of a finite open cover of `K` of mesh `< r` (with `ord_K(∞) = 1`).

**Corollary H.3.** The unit divides iff for every `κ > 0` there are `δ ≤ κ` and `N ≥ 1` with
`ord_K(ℓ_A(N, δ)) ≤ κN`.
- *(⟸).* Take a finite open cover of mesh `< ℓ_A(N, δ)` and order `ord_K(ℓ_A(N, δ))`. Each member
  lies in a member of `𝒟_A(N, δ)`, so it carries a division set with `N_i ≥ N` and `δ_i ≤ δ ≤ κ`.
  At every point `Σ 1/N_i ≤ ord/N ≤ κ`. Apply Proposition H.2.
- *(⟹).* If the unit divides, `K ∈ 𝒟_A(N, δ)` for all `N, δ`. So `ℓ_A = ∞`, `ord = 1`, and
  `N ≥ 1/κ` works. ∎

**Corollary H.4 (Hilbert cube).** Let `K = Q = [0,1]^ℕ` with `ρ(x,y) = Σ_i 2^{−i}|x_i − y_i|`. If
the unit does not divide, there is `κ_0 ∈ (0,1]` with
```text
ℓ_A(N, κ_0)  ≤  16 · 2^{−κ_0 N}      for every N ≥ 1.
```
*Proof.* Negate Corollary H.3 and take `δ = κ_0`: `ord_Q(ℓ_A(N, κ_0)) > κ_0 N` for every `N`. Part 4
shows `ord_Q(r) ≤ log_2(4/r) + 2`, so `log_2(4/ℓ) + 2 > κ_0 N` and `ℓ < 16 · 2^{−κ_0 N}`. ∎

**What H.3 adds to Corollary F.** Corollary F weighs a division set by `1/N + δ`. So it cannot rule
out confinement caused by the defect, for instance `ℓ_A(N, δ) ≈ 2^{−c/δ}` for every `N`. There
`ω · ord ≳ (1/N + δ) · c/δ ≥ c`. Corollary H.3 disposes of it: take `δ = κ` and `N ≥ c/κ²`. A
counterexample must confine divisions of fixed defect exponentially in the matrix size alone.

**Model tests.**
- `C(K)` fails (a): nonzero order zero maps from `M_N` exist only for `N = 1`, so every point
  carries weight `1`. It is not simple.
- A `Z`-stable algebra satisfies (a) and (b) with the single set `K`.

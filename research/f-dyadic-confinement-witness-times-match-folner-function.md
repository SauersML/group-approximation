---
rg: 2
id: f-dyadic-confinement-witness-times-match-folner-function
kind: claim
title: The witness times of rare-event inverted-orbit confinement for Thompson's F and the Følner function of F bound each other, up to one exponential and a polynomial change of scale
distinct_from:
  f-dyadic-inverted-orbit-confinement-needs-tower-times: that is the Moore instance for uniform mu at the root 1/2, a one-sided tower lower bound on the first confinement time; this is a two-sided comparison of the witness times with the Følner function for every symmetric generating mu containing e, with a converse turning Følner sets into witness times.
  thompson-f-dyadic-ea-witnesses-need-tower-size: that bounds the size of approximately invariant measures on finite subsets of D against Moore's constant only; this is a two-sided comparison between the confinement witness times of the open hole and the Følner function itself, with a converse that turns Følner sets into witness times.
  f-dyadic-ea-iff-inverted-orbit-confinement: that is the qualitative equivalence between extensive amenability and confinement; this is a quantitative two-sided comparison of the confinement witness times with the Følner function of F, proved directly without the extensive amenability calculus.
  f-dyadic-inverted-orbit-is-subballistic-on-rare-events: that is the open confinement target; this bounds its witness-time function above and below by the Følner function and decides nothing about whether it is finite.
  thompson-f-folner-function-exceeds-every-tower: that is Moore's lower bound for the Følner function; this transfers any bound on the Følner function, in either direction, to the confinement witness times.
  thompson-f-cnd-certificates-need-near-exponential-ball-growth: that bounds return probabilities of walks on F itself; this compares the lamp return probability E 2^-|O_n| on the configuration space of (Z/2)^(D) ⋊ F with the Følner function of F.
  f-dyadic-endpoint-switch-walk-gaps-are-inverse-square: that compares spectral gaps at the roots 2^-m with no Følner input; this is a finite-time comparison at a fixed root with the Følner function.
---

**ESTABLISHED** by `f-dyadic-confinement-witness-times-match-folner-function-proof` (direct proof; not independently
reviewed; no priority claimed).

**Setting.**
- `D` is the set of dyadic rationals in `(0,1)`, and `x_0 ∈ D`.
- `μ` is a symmetric probability measure on `F` with finite support `Γ = supp μ` that generates `F`. Put
  `w = min_{g∈Γ} μ(g)`.
- `h_i` are i.i.d. `∼ μ`, `g_n = h_n⋯h_1`, and `O_n = {g_k⁻¹ x_0 : 0 ≤ k ≤ n}`. Put `p_n = E 2^{−|O_n|}`.
- **Følner function.** `Føl_Γ(r) = min{ |A| : A ⊂ F finite nonempty, Σ_{γ∈Γ} |Aγ Δ A| < |A|/r }`, or `∞` if no
  such set exists. This is Moore's convention (`thompson-f-folner-function-exceeds-every-tower`).
- **Witness times.** `N_μ(ε)` is the least `N ≥ 2` with `P(|O_N| < εN) > e^{−εN}`, or `∞`. The open hole
  `f-dyadic-inverted-orbit-is-subballistic-on-rare-events` holds iff every `N_μ(ε)` is finite. One direction is
  trivial. For the other: `|O_N| ≥ 1` forces `N_μ(ε') ≥ 1/ε'`, and a witness at `ε' < ε` is a witness at `ε`.
  So finite witness times at all `ε' → 0` give infinitely many witnesses at `ε`.
- **Breakpoint constants.** `B(s)` is the breakpoint set of `s`, `b = Σ_{s∈Γ}|B(s)|`, and
  `L = Σ_{s∈Γ} ‖β(s)‖₁`. `T = max{|g_y|_Γ : y ∈ ∪_s B(s)}`, with `g_y x_0 = y` of least word length.
- **Scale constants.** For `0 < η ≤ 1`:
  - `M_η = ⌈log₂((8b+8)/η) / log₂(4/3)⌉`;
  - `K_η = log₂(4|Γ|) + 2 log₂(4L/η + 3)`;
  - `δ_η = ( wη / (128 |Γ| M_η (2T+1)) )²`.

  So `M_η K_η = O(log²(1/η))` and `δ_η = Θ(η²/log²(1/η))`, with constants depending on `μ` and `x_0`.

**Theorem.**

- **(L) Rate gives Følner sets.** Suppose `e ∈ Γ`, `0 < η ≤ 1`, `n ≥ 1`, and `p_{2n} ≥ e^{−2δn}` with `δ ≤ δ_η`.
  Then `Føl_Γ(1/η) ≤ 2^{n M_η K_η}`.
- **(U) Følner sets give a rate.** If `U ⊂ F` is finite and nonempty with `Σ_{s∈Γ} |Us Δ U| ≤ η|U|` and `η ≤ 2`,
  then `p_{2n} ≥ (1 − η/2)^{2n} / (|U| 2^{|U|})` for every `n ≥ 0`.

**Corollary 1 (sandwich for the witness times).** Let `e ∈ Γ`.
- If `0 < η ≤ 1` and `3ε ≤ δ_η`, then `N_μ(ε) ≥ log₂ Føl_Γ(1/η) / (M_η K_η)`.
- If `0 < ε ≤ 1`, then every even `N ≥ 2⌈4 Føl_Γ(8/ε)/ε⌉` satisfies `P(|O_N| < εN) > e^{−εN}`. In particular
  `N_μ(ε) ≤ 2⌈4 Føl_Γ(8/ε)/ε⌉`.

In short: `log Føl_Γ(1/η) ≲ log²(1/η) · N_μ(η²/polylog(1/η))` and `N_μ(ε) ≲ Føl_Γ(8/ε)/ε`.

**Corollary 2 (the tower rate).** By Moore's theorem, `Føl_Γ(C^m) ≥ exp_m(0)`. So with `η = C^{−m}`, part (L)
gives `n · M_η K_η ≥ exp_{m−1}(0)` whenever `p_{2n} ≥ e^{−2δ_η n}`. This is the tower-time lower bound, also
obtained independently for `μ` uniform on `{e, x_0^{±1}, x_1^{±1}}` at the root `1/2` by swarm-0917-w6-w6-f-last1
(node `f-dyadic-inverted-orbit-confinement-needs-tower-times`, not yet in this worktree). Here it holds for every
`μ` with `e ∈ supp μ` and every root, and it is the Moore instance of part (L).

**Corollary 3 (traps).** Let `e ∈ Γ`, `0 < c ≤ 1`, `λ > 0`, `s ≥ 0`, and `0 < η ≤ 1` with `2λ ≤ δ_η`. Suppose that
for every `N` some event of probability at least `c e^{−λN}` keeps `|O_N| ≤ s`. Then
`(s ln 2 + ln(1/c)) / λ ≥ 2 ( log₂ Føl_Γ(1/η) / (M_η K_η) − 1 )`.

## What this changes

- **The hole is quantitatively the Følner problem.** Any proof of the hole with witness times `N(ε)` produces
  Følner sets with `log₂ Føl_Γ(1/η) ≤ N(δ_η/3) · M_η K_η`. Any construction of Følner sets produces witness times
  `N_μ(ε) ≤ 2⌈4Føl_Γ(8/ε)/ε⌉`. So the rare-event target is never more than one exponential cheaper than exhibiting
  Følner sets of `F`, and never more expensive than exhibiting them.
- **The survivor band is exactly the Følner band.** The Moore rate kill leaves proofs whose witness times are of
  tetration size. Part (U) shows that is not a gap in the method: if `F` is amenable, the witness times are at most
  `Føl_Γ(8/ε)/ε`. So they sit between `log Føl` and `Føl` at polynomially related scales. No witness-time lower bound
  beyond one exponential of the Følner function can ever be proved. And any improvement of Moore's bound transfers
  at once, in either direction.

## Class killed

- *Class.* Approaches that pass to the rare-event confinement hole in order to get a target quantitatively easier
  than Følner sets. Examples are effective probabilistic confinement arguments, trap (Donsker–Varadhan) strategies,
  and spectral rate certificates for the switch-walk-switch chain.
- *Invariant.* The witness-time function `ε ↦ N_μ(ε)`, compared with `η ↦ log₂ Føl_Γ(1/η)`.
- *Where every member dies.* Step 4 of the proof. There the almost invariant vector `P^j δ_0` becomes a
  breakpoint-covering measure on `P_f(D)`, and Step 5 turns it into a Følner set of size `2^{n M_η K_η}`. Every
  certified witness time is therefore a certified Følner bound, one exponential up.
- *Consequence.* For example, witness times `N(ε) ≤ exp_p((1/ε)^d)` along `ε_j → 0` would give
  `Føl_Γ(C^m) ≤ exp_{p+1}(poly(C^m))`, which Moore excludes. Trap families bounded by a fixed tower in `1/λ` die the
  same way (Corollary 3).

The result decides neither the hole nor amenability. Parts (L) and (U) hold unconditionally, and part (U) is vacuous
when `F` is non-amenable.

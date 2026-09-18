---
rg: 2
id: f-ea-endpoint-localization-certificates-stall
kind: claim
title: Certificates that confine the switch-walk to a linear endpoint zone of F and then transport the root to 1/2 by path comparison never certify a gap at 1/2 below 8/225
distinct_from:
  f-ea-calculus-certificates-force-f-prime-to-act-trivially: that kills algebraic calculus certificates (recurrence, finite pieces, extensions) by forcing F' to act trivially; this kills spectral certificates that localize at an endpoint and transport by path comparison, through an exponent balance.
  f-dyadic-action-is-not-recurrent: that is transience of the dyadic Schreier graph; this concerns the switch-walk on finite subsets, where the endpoint zone is used as a linear model and the loss sits in the transport step.
  thompson-f-dyadic-orbit-walks-are-transient: that is transience for every generating measure; this is a quantitative lower bound on what one class of gap certificates can output.
  f-dyadic-endpoint-switch-walk-gaps-are-inverse-square: that proves the gap bounds kappa(m) of order m^-2 and the equivalences; this shows that no confinement event inside an endpoint zone, combined with any system of comparison words, can drive the certified gap at 1/2 to zero.
---

**ESTABLISHED** by `f-ea-endpoint-localization-certificates-stall-proof` (direct proof; not independently
reviewed). Notation as in `f-dyadic-endpoint-switch-walk-gaps-are-inverse-square`: `ν_y`, `P_y`, `E_y`,
`T_y = supp ν_y`, `O_n^y`, `g_k = h_k⋯h_1`.

**The class.** An *endpoint-localization certificate* consists of:
- a root `y` in a zone `Z_0 = (0, 1/4]` or `Z_1 = [7/8, 1)`;
- events `E_n` on which every intermediate point `h_j^{−1}⋯h_k^{−1}y` (`1 ≤ j ≤ k ≤ n`) lies in the same zone;
- the *certified rate* `r = limsup_n E[2^{−|O_n^y|}; E_n]^{1/n}`, which gives `gap(y) ≤ 1 − r` when `r > 4/5`, by (0b) and (0e)
  there (the lower bounds below hold for the number `1 − r` whether or not it is a valid bound);
- a *transport*: for each `u ∈ T_{1/2}` a word `γ_u = t_1⋯t_{ℓ_u}` in `T_y` with product `u`, giving
  `E_{1/2} ≤ A·E_y` with the Diaconis–Saloff-Coste constant
  `A = max_{t ∈ T_y} ν_y(t)^{−1} Σ_u ν_{1/2}(u) ℓ_u N(t, γ_u)`, where `N(t,γ)` counts occurrences of `t` in `γ`.

The certificate outputs `gap(1/2) ≤ A(1 − r)`. By item 3 of the gap claim, a family of certificates with outputs
tending to `0` would prove `F` amenable.

**Theorem.**
1. *Zone `Z_0`.* Put `W = ⌊log_2(1/(4y))⌋`. Then `1 − r ≥ 4/(5(2W+3)²)` and `A ≥ (2/5)(W+1)²`. So the output
   is at least `8(W+1)²/(25(2W+3)²) ≥ 8/225`.
2. *Zone `Z_1`.* Put `W = ⌊log_2(1/(8(1−y)))⌋`. Then `1 − r ≥ 8/(5(2W+3)²)` and `A ≥ (2/5)(W+2)²`. So the
   output is at least `16(W+2)²/(25(2W+3)²) ≥ 4/25`.
3. *Chains.* Transport through intermediate roots `y = y_0, y_1, …, y_k = 1/2`, with one comparison per stage,
   still outputs at least `8/225`, provided each stage moves its root a Schreier distance `d_i ≥ 4`.

So every member of the class stalls at a positive constant, whatever `E_n`, the depth of the root, or the words.

**Invariant and dying step.** The invariant is the exponent pair:
- confinement in a zone of Schreier depth `W` costs rate `≍ W^{−2}` (a reflected lazy walk killed at `W`);
- any comparison word for `δ_{1/2}` must carry `y` to `1/2` and back, so it has length `≥ 2(W+1)`, and the
  constant `A` grows like `W²`.

Every member dies at the transport step: the gain and the loss have the same exponent `2`, so their product is
bounded below. The unconditional strip strategy of the gap claim (item 1 there) is the optimal member, up to
constants.

**Scope.**
- The theorem does not decide amenability. It says an amenability proof through the switch-walk spectrum must
  certify a rate at a root *outside* the linear endpoint zones, or transport by something other than path
  comparison (for instance, a comparison whose words exploit cancellation in `f`, not letter counts).
- Unit-step chains (`d_i < 4`) are not covered by item 3.
- *Remark (motivation, not used).* Among rooted Chabauty limits of `(F·y_k, y_k)`, the recurrent ones are the
  endpoint limits:
  - if `y_k → 0` or `y_k → 1`, the stabilizers converge to the kernel of the slope character at that endpoint, with
    Schreier graph `Z`;
  - if `y_k → t ∈ (0,1)`, every limit stabilizer fixes `t` (for irrational `t`) or the dyadic limit point (from one
    side), so the limit orbit is transient by item 2 of `thompson-f-point-orbits-are-transient`.

  So endpoint localization is the only recurrence-based localization, and this claim removes it.

---
rg: 2
id: thompson-f-copy-marker-coding-balances-without-reiter
kind: claim
title: "Copy-marker coding packs A-Reiter invariance into one measure pair on G×G. For A = {e,a,b} in F_2 that pair balances at rate 4/(3N) with no Reiter measure, but for the ball B_1 of F_2 it is unbalanced at every window by more than 0.0736"
distinct_from:
  thompson-f-ramsey-radius-double-gap-below-reiter-radius: that is RGAP₂, a radius comparison inside F; this is a coding lemma, a counterexample and a free-group test for one proposed way to refute such radius gaps.
  moore-ramsey-criterion-for-amenability: that is Moore's criterion over colorings of balls of G; this is about one measure pair on the product G×G and its push-forward to the two-sided action of G×G on G.
  copy-marker-pair-balance-forces-reiter-for-symmetric-sets: that is the open quantitative transfer this node tests; this node establishes the non-symmetric failure and the free-group certificate for B_1.
---

**ESTABLISHED** by `thompson-f-copy-marker-coding-balances-without-reiter-proof`. Parts A–C are by hand. Part D is
computer-assisted: an LP finds a test function of finite type, and its drift inequality is then checked in exact
rational arithmetic on a finite list that covers every word.

**Setup.** Let `G` be a group, `A ⊆ G` finite with `K = |A|`, and `g` uniform on `A`. The *copy-marker pair* of `A`
is the pair of measures on `G×G`
- `α_A` = the law of `(g, g)`, and
- `β_A` = the law of `(e, g)`.

For `ν` = the law of `(Y, Z)` on `G×G`, with `g` independent of `(Y, Z)`, one has `α_Aν` = the law of `(gY, gZ)` and
`β_Aν` = the law of `(Y, gZ)`. TV is half the ℓ¹ distance.

**Reiter measures balance it.** If `μ` has `(1/K)Σ_{g∈A} TV(gμ, μ) ≤ η`, then `ν = μ ⊗ δ_e` gives
`TV(α_Aν, β_Aν) ≤ η` at the same window. The pair lives in the commuting copy `G×G`. In F this copy embeds
undistorted, since `F×F ≤ F`. Coset restriction then turns a balancing measure for the pair in F into one on the copy.
So the copy-marker pair is a candidate single pair whose balance radius could dominate the Reiter radius. It
escapes the pigeonhole `c_{g′}⁻¹c_g ∈ XX⁻¹` that kills marker coding inside one group, because its markers `(g, g)`
and `(e, g)` differ only in the first coordinate.

**Part A (posterior identity, every group).** Let `μ_Z` be the law of `Z`, `κ_z` the law of `Y` given `Z = z`,
`q = u_Aμ_Z`, and `π_w(g) = μ_Z(g⁻¹w)/(K q(w))` the posterior of `g` given `gZ = w`. Then

`TV(α_Aν, β_Aν) = ½ Σ_w q(w) ‖Σ_{g∈A} π_w(g) (g·κ_{g⁻¹w} − κ_{g⁻¹w})‖₁`.

**Part B (what the pair forces, every group).** Two consequences:
- The first marginals give `TV(u_Aμ_Y, μ_Y) ≤ TV(α_Aν, β_Aν)`, which is a cheap Cesàro-type condition.
- If `Z` is deterministic, the right side of Part A is exactly `(1/K)Σ_g TV(gκ, κ)`, which is the A-Reiter defect.

So the pair forces Reiter only to the extent that the posterior family `{π_w}` fails to split. `Y` must be
stationary under each posterior, not under each `δ_g`.

**Part C (non-symmetric sets: the coding dies).** In `F_2 = ⟨a, b⟩` take `A = {e, a, b}`, `c = b⁻¹a`, and `m = (δ_a+δ_b)/2`.
Let `Y` and `Z` be independent, with
- `μ_Z = (1/N)Σ_{j<N} δ_{c^j}`, and
- `μ_Y = (1/N)Σ_{j<N} m^j`.

Then `ν ∈ P(B_{2N} × B_{2N})` and `TV(α_Aν, β_Aν) ≤ 4/(3N)`. Yet `F_2` has no approximately `{a,b}`-invariant
measure: `inf_μ (‖aμ−μ‖₁ + ‖bμ−μ‖₁) > 0`. The floating-point LP minimum over `P(B_n × B_n)` agrees with `2/(3(n+1))` to six decimals for `n ≤ 4`.

**Part D (the ball B_1 of F_2 passes the free-group test).** Take `A = B_1 = {e, a^{±1}, b^{±1}}` in `F_2`. For every
finitely supported probability `ν` on `F_2 × F_2`,

`TV(α_Aν, β_Aν) ≥ 368419/5000000 > 0.0736`.

The bound already holds after pushing forward by `(x, w) ↦ wx⁻¹`. With `D = ZY⁻¹`, this sends the pair to
`(1/K)Σ_g gμ_Dg⁻¹` (conjugation average) against `(1/K)Σ_g gμ_D` (translation average). The certificate is a
function `φ: F_2 → [−½, ½]`. Its value depends on the whole word when the length is at most 7, and otherwise only on
the first two and last two letters. It satisfies `(1/5)Σ_{g∈B_1}[φ(gDg⁻¹) − φ(gD)] ≥ 0.0736838` for every `D ∈ F_2`.

The numbers match this bound:
- The finite-window LP optima of the full pair are 0.800, 0.450, 0.322, 0.268, 0.239, 0.223 for `n = 0..5`.
- The LP optima of the projection are 0.196, 0.191, 0.188 at `n = 8, 9, 10`.

**Invariant and dying step (the class statement).** The coding certifies only posterior stationarity. It dies
exactly when `u_A` can be written as the average of a posterior family whose pieces fall into classes where joint
stationarity is cheap. That family must also come from a cheaply realised `μ_Z`.

For `{e, a, b}` the pieces lie on the segment `[δ_e, m]`. The realising `μ_Z` then needs invariance only under the
single element `b⁻¹a`.

For a symmetric `A = {e} ∪ T` the analogous segment `[δ_e, u_T]` needs `μ_Z` invariant under `⟨T⁻¹T⟩`. That subgroup
has index at most 2 in `⟨T⟩`, so the segment trick is dead for every symmetric set generating a non-amenable group.
Other splittings of `B_1` in `F_2` run into one of two obstacles:
- the reflection pair `((δ_a+δ_b)/2, (δ_{a⁻¹}+δ_{b⁻¹})/2)`, which is unbalanced in `F_2`;
- invariance under the even subgroup.

Part D shows that for `B_1` no dependent coupling escapes either. So what dies is copy-marker coding over arbitrary
finite sets. Coding over symmetric balls survives the one test available. The quantitative transfer it would need is
`copy-marker-pair-balance-forces-reiter-for-symmetric-sets`.

---
rg: 2
id: thompson-f-copy-marker-coding-balances-without-reiter-proof
kind: route
title: Write the coded pair through the posterior of the marker, balance {e,a,b} with two independent Cesàro averages, and certify B_1 by pushing to the two-sided action and checking a finite-type test function exactly
target: thompson-f-copy-marker-coding-balances-without-reiter
requires: []
artifacts:
  - experiments/copy-marker-coding-2026-09-17/coded_pair_lp.py
  - experiments/copy-marker-coding-2026-09-17/coded_pair_lp_sym.py
  - experiments/copy-marker-coding-2026-09-17/conjugation_projection_lp.py
  - experiments/copy-marker-coding-2026-09-17/conjugation_projection_sym.py
  - experiments/copy-marker-coding-2026-09-17/projection_dual.py
  - experiments/copy-marker-coding-2026-09-17/projection_certificate.py
  - experiments/copy-marker-coding-2026-09-17/verify_certificate.py
  - experiments/copy-marker-coding-2026-09-17/certificate_p2.json
  - experiments/copy-marker-coding-2026-09-17/results.txt
---

Notation is as in the target. All measures are finitely supported. `‖·‖` is ℓ¹, and `TV = ½‖·‖`. For a measure `m`
on `G`, `mκ` is convolution, `(mκ)(x) = Σ_g m(g)κ(g⁻¹x)`.

## Part A (posterior identity)

For `(x, w) ∈ G×G`,

`α_Aν(x, w) = (1/K)Σ_g ν(g⁻¹x, g⁻¹w) = (1/K)Σ_g μ_Z(g⁻¹w) κ_{g⁻¹w}(g⁻¹x) = q(w) Σ_g π_w(g) (gκ_{g⁻¹w})(x)`,

`β_Aν(x, w) = (1/K)Σ_g ν(x, g⁻¹w) = q(w) Σ_g π_w(g) κ_{g⁻¹w}(x)`.

Subtract and sum `|·|` over `x` and `w`. Terms with `q(w) = 0` vanish. ∎

## Part B

*Marginals.* Push-forward contracts TV. The first marginal of `α_Aν` is `u_Aμ_Y`, and that of `β_Aν` is `μ_Y`.

*Deterministic marker.* If `Z = z_0`, then `κ_z = μ_Y`. The points `w = gz_0` are distinct for distinct `g`. So
`q(w) = 1/K` and `π_w = δ_g` there, and Part A reads `TV = (1/K)Σ_g ½‖gμ_Y − μ_Y‖`. ∎

## Part C (A = {e, a, b} in F_2)

Take `c = b⁻¹a`, `m = (δ_a+δ_b)/2`, `μ_Z = (1/N)Σ_{j<N}δ_{c^j}` and `μ_Y = (1/N)Σ_{j<N}m^j`, with `Y` and `Z` independent.
Then `Y ∈ B_{N−1}` and `Z ∈ B_{2N−2}`. Independence gives `κ_z = μ_Y`, so Part A reads
`TV = ½Σ_w q(w)‖π_wμ_Y − μ_Y‖`.

*Symmetrised posterior.* Let `π̃_w` agree with `π_w` at `e` and put mass `(π_w(a)+π_w(b))/2` on each of `a` and `b`.
Then `π̃_w = (1−s_w)δ_e + s_w m` with `s_w ∈ [0,1]`.

*Main term.* `π̃_wμ_Y − μ_Y = s_w(mμ_Y − μ_Y)`. Telescoping gives `‖mμ_Y − μ_Y‖ = (1/N)‖m^N − δ_e‖ ≤ 2/N`. So
`½Σ_w q(w)‖π̃_wμ_Y − μ_Y‖ ≤ 1/N`.

*Error term.* `‖π_wμ_Y − π̃_wμ_Y‖ ≤ ‖π_w − π̃_w‖`. Also `q(w)π_w(g) = μ_Z(g⁻¹w)/3`, so

`Σ_w q(w)‖π_w − π̃_w‖ = (1/3)Σ_w |μ_Z(a⁻¹w) − μ_Z(b⁻¹w)| = (1/3)‖aμ_Z − bμ_Z‖ = (1/3)‖cμ_Z − μ_Z‖`.

That equals `(1/(3N))‖δ_{c^N} − δ_e‖ = 2/(3N)`, and half of it is `1/(3N)`. The total is at most `4/(3N)`.

*No Reiter measure.* Suppose some `μ` had `‖aμ−μ‖, ‖bμ−μ‖ ≤ ε` for every `ε > 0`. Since `‖a⁻¹μ−μ‖ = ‖μ−aμ‖`, the
triangle inequality gives `‖gμ−μ‖ ≤ |g|ε` for every word `g`. That is Reiter's condition for every finite set, which
would make `F_2` amenable. So the infimum is positive. ∎

## Part D (A = B_1 in F_2)

*Step 1 (push-forward).* `Φ(x, w) = wx⁻¹` gives `Φ(gY, gZ) = gDg⁻¹` and `Φ(Y, gZ) = gD`, with `D = ZY⁻¹`. So
`TV(α_Aν, β_Aν) ≥ TV(Cμ_D, Lμ_D)`, where `Cμ = (1/5)Σ_{g∈B_1} gμg⁻¹` and `Lμ = (1/5)Σ_{g∈B_1} gμ`.

*Step 2 (duality).* If `|φ| ≤ ½`, then `TV(P, Q) ≥ ∫φ dP − ∫φ dQ`. Moreover
`∫φ dCμ − ∫φ dLμ = Σ_D μ(D)·dr(D)`, where `dr(D) = (1/5)Σ_{g∈B_1}[φ(gDg⁻¹) − φ(gD)]`. So `inf_D dr(D) ≥ δ` gives
`TV ≥ δ` for every `ν`.

*Step 3 (the function).* The type of a reduced word `w` is `w` itself if `|w| ≤ 7`, and otherwise the pair
(first two letters, last two letters). `φ` is constant on types. It is also invariant under the group `Σ` of 8
automorphisms of `F_2` that permute `{a^{±1}, b^{±1}}` (swap `a ↔ b`, and invert `a` or `b`). The values, rationals
with denominator `10^6` in `[−½, ½]`, are in `certificate_p2.json` (570 types). Each `σ ∈ Σ` permutes `B_1` and is
a homomorphism, so `dr(σD) = dr(D)`.

*Step 4 (covering lemma).* Let `|D| ≥ 10`. Every image `gD` and `gDg⁻¹` with `g ∈ B_1` then has length at least 8,
so its type is its end pairs. Left multiplication by `g` changes at most the first letter of `D`: it deletes it or
prepends `g`. It leaves the last three letters alone. Right multiplication of `gD` by `g⁻¹` likewise changes only the
last letter.

So the first two and last two letters of each image depend only on `g`, on `D`'s first three letters, and on
`D`'s last three letters, and so does `dr(D)`. Any two reduced 3-letter words `P` and `Q` occur as prefix and suffix
of a reduced word of length 10. The 4 middle letters are chosen one at a time, each avoiding at most 2 of the 4
letters. So `inf_{F_2} dr` is the minimum of `dr` over a finite covering list:
- one `Σ`-representative of every `D` with `|D| ≤ 9`;
- one length-10 word for each `Σ`-orbit of pairs `(P, Q)`.

*Step 5 (exact check).* `verify_certificate.py` evaluates `dr` in exact rational arithmetic on the covering list,
which has 5089 words. The minimum is `368419/5000000 = 0.0736838`. As an independent check, it also evaluates `dr` in
floating point on all 1,062,881 reduced words of length at most 12. That check uses neither `Σ` nor Step 4, and it
gives the same minimum. ∎

*Where φ came from.* `projection_certificate.py` maximises `δ` by LP over finite-type `φ`. That LP gives
`δ = 0` for end pairs of length 1, and `0.0736842` for end pairs of length 2. The LP is only a search tool, and the
proof is Step 5. The dual of the finite-window LP (`projection_dual.py`) is close to `φ = 1[D is not cyclically
reduced] − ½`. So the certificate is a refinement of the fact that conjugation by a letter usually makes a word
non-cyclically-reduced, while translation usually does not. As a control, the same search for `A = {e, a, b}` gives
`δ = 0`, as it must by Part C.

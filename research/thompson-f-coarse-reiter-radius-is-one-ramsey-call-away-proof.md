---
rg: 2
id: thompson-f-coarse-reiter-radius-is-one-ramsey-call-away-proof
kind: route
title: Minimax the coarse Reiter radius into certificates with one test function per ball element, code each certificate into one set of the self-wreath (F ≀ Z) × Z ≤ F with a moving window, and balance it with one Ramsey call
target: thompson-f-coarse-reiter-radius-is-one-ramsey-call-away
requires: [moore-ramsey-criterion-for-amenability, coarse-ball-invariance-gives-fine-reiter-measures, thompson-f-word-length-is-comparable-to-caret-count, thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap, thompson-f-ramsey-function-iterates-reach-towers]
---

**Step 0 (notation).** `|·|` is word length in `S ∪ S⁻¹`, `S = {x_0, x_1}`, and `|B_M| ≤ 5^M`. For `ν ∈ P(F)`,
`g ∈ F` and `f : F → [0,1]`, put `gν(E) = ν(g⁻¹E)` and `gν(f) = Σ_y ν(y) f(gy)`; for `μ ∈ P(F)`,
`μν = Σ_g μ(g) gν`. `B_n` is *1/2-Ramsey w.r.t. `B_m`* (Moore) if for every `E ⊆ B_n` there is `ν ∈ P(B_n)` with
`B_m·supp ν ⊆ B_n` and `|μν(E) − μ'ν(E)| ≤ 1/2` for all `μ, μ' ∈ P(B_m)`; `R(m)` is the least such `n`.
`R(m) ≥ m` and `R` is nondecreasing. For `c > 0`, `CR_c(M)` is the least `r` such that some `ν ∈ P(B_r)` has
`‖gν − ν‖₁ ≤ c` for all `g ∈ B_M`; `CR = CR_1`. `κ` is the constant of
`thompson-f-word-length-is-comparable-to-caret-count` for `S`, so `N(f) ≤ κ|f| + κ²` and `|f| ≤ κN(f) + κ`.
We use the convention `x_0(t) = t/2` on `[0,1/2]`, `t − 1/4` on `[1/2,3/4]`, `2t − 1` on `[3/4,1]`, and
`x_1 = ψ_R x_0 ψ_R⁻¹` on `[1/2,1]`, identity on `[0,1/2]`, with `ψ_R(t) = (t+1)/2`, `ψ_L(t) = t/2`.
All three sections below are finite-value statements; if the relevant `R`-value is `∞` there is nothing to prove.

**Step 1 (Lemma S: threshold 3/2 is enough).** *For all `M ≥ 1`, `CR(M) ≤ CR_{3/2}(556M²) + 278M²`.*

Rerun the proof of `coarse-ball-invariance-gives-fine-reiter-measures` with `K' = 278M²` and a witness `ν` of
`r = CR_{3/2}(2K')`. Step 1 there now gives `‖λ_gξ − ξ‖₂² ≤ 3/2`, so `⟨λ_gξ, ξ⟩ ≥ 1/4` for `g ∈ B_{2K'}`. Steps 2–3
give `c_{K'} ≥ 1/4` and `ρ_{K'} ≥ 4^{−1/K'} ≥ 1 − ln 4/K'`. Steps 4–6 then give `μ ∈ P(B_{r+K'−1})` with
`‖sμ − μ‖ ≤ 10√(2 ln 4/K')` for `s ∈ S'`, hence `‖gμ − μ‖ ≤ 10M√(2 ln 4/(278M²)) = 10√(2 ln 4/278) < 0.9988`
for `g ∈ B_M`. Nothing else in that proof uses the threshold.

**Step 2 (the host `V = (F ≀ Z) × Z ≤ F`).**
- *Intervals.* `I_k = x_0^k([1/4,1/2])`, `k ∈ Z`. Then `I_k = [2^{−k−2}, 2^{−k−1}]` for `k ≥ 0` and
  `I_{−k} = [1 − 2^{−k}, 1 − 2^{−k−1}]` for `k ≥ 1`. These are standard dyadic intervals tiling `(0,1)`, and each lies
  inside one linear piece of `x_0`, so `x_0` maps `I_k` affinely onto `I_{k+1}`. Put `J_k = ψ_L(I_k)`, standard dyadic
  intervals tiling `(0,1/2)`, with `J_0 = [1/8,1/4]`.
- *Generators.* `σ = ψ_L x_0 ψ_L⁻¹` on `[0,1/2]`, identity on `[1/2,1]`; `u = x_1`. Both lie in `F`. `σ` maps `J_k`
  affinely onto `J_{k+1}`. Let `α_k : [0,1] → J_k` be the increasing affine bijection and
  `φ_k(y) = α_k y α_k⁻¹` on `J_k`, identity elsewhere. `α_k` has dyadic data, so `φ_k : F → F` is an injective
  homomorphism, and `α_{k+1} = σ α_k` gives `σ φ_k(y) σ⁻¹ = φ_{k+1}(y)`.
- *Structure.* The `φ_k(F)` have disjoint supports, so they commute and generate `⊕_k φ_k(F)`, normalized by `σ`
  with the shift action. `σ^s` has slope `2^{−s}` at `0⁺`, while every element of `⊕_k φ_k(F)` is the identity near
  `0` (finite support), so `W = ⟨φ_0(F), σ⟩ = (⊕_k φ_k(F)) ⋊ ⟨σ⟩ ≅ F ≀ Z`. `u` is supported in `[1/2,1]` and `W`
  in `[0,1/2]`, so `V = W × ⟨u⟩`. Every `v ∈ V` is uniquely `v = z σ^s u^t` with `z = Π_k φ_k(y_k)`, finitely many
  `y_k ≠ e`. Write `y_k(v)`, `s(v)`, `t(v)` for these coordinates.
- *Coordinate identities.* For `h = Π_k φ_k(h_k)`: `y_k(hv) = h_k y_k(v)` (product in `F`). Also
  `y_k(σ^j v) = y_{k−j}(v)`, `u^r v = v u^r` and `t(u^r v) = t(v) + r`.

**Step 3 (coordinates are undistorted).** *There is `A_1` with `|y_k(v)| ≤ A_1|v| + A_1` for all `v ∈ V`, `k ∈ Z`.*
- *Exponents.* The generators have slopes in `{1/2, 1, 2}`, so `v` has one-sided slopes in `[2^{−|v|}, 2^{|v|}]`.
  The right slope of `v` at `0` is `2^{−s}` (`z` and `u` are the identity near `0`). The right slope at `1/2` is
  `2^{−t}` (`z` and `σ` are the identity on `[1/2,1]`, and `x_0` has slope `1/2` at `0`). So `|s|, |t| ≤ |v|`, and
  `|z| = |v u^{−t} σ^{−s}| ≤ (2 + |σ|)|v|`.
- *Restriction lemma.* If `z ∈ F` and `z(J) = J` for a standard dyadic `J` with affine chart `α`, then
  `y = α⁻¹ z|_J α` has `N(y) ≤ N(z)`. Let `(T_−, T_+)` be the reduced pair of `z`. (a) If `J` is a vertex of `T_−`, it
  is a union of consecutive leaves of `T_−`, so `z(J) = J` is a union of consecutive leaves of `T_+`. Standard dyadic
  intervals are nested or disjoint, so these are exactly the leaves of `T_+` inside `J`, and `J` is their common
  ancestor, a vertex of `T_+`. The two subtrees at `J` form a tree pair for `y` with at most `N(z)` carets.
  (b) Otherwise `J` lies strictly inside a leaf `L` of `T_−` and `z` is affine on `L`. An increasing affine map with
  `z(J) = J` fixes both ends of `J`, so it is the identity, and `y = e`.
- *Conclusion.* `z(J_k) = J_k` and `z|_{J_k} = φ_k(y_k)`, so
  `|y_k| ≤ κN(y_k) + κ ≤ κN(z) + κ ≤ κ²|z| + κ³ + κ ≤ κ²(2+|σ|)|v| + κ³ + κ`. Take `A_1 = max(κ²(2+|σ|), κ³+κ)`.

**Step 4 (test elements).** Fix `M ≥ 1`, list `B_M \ {e} = {g_0, …, g_{K−1}}` (so `1 ≤ K ≤ 5^M`), and put `J = 16K`.
For `0 ≤ j < J` let `a_j = Π_{i<K} φ_{i−j}(g_i)`, and let
`P = Π_{i<K} φ_i(g_i) = φ_0(g_0) σ φ_0(g_1) σ ⋯ σ φ_0(g_{K−1}) σ^{−(K−1)}`. Then `σ^j a_j = P σ^j`. With
`β = max(|φ_0(x_0)|, |φ_0(x_1)|)`, we get `|P| ≤ βKM + 2K|σ|`, so for `r < 8`

`|u^r σ^j a_j| ≤ βKM + 18K|σ| + 8 ≤ A_2 K(M+1) =: m`, with `A_2 = β + 18|σ| + 8`,

and `|u^r σ^j| ≤ m` too. Let `μ` (resp. `μ'`) be the uniform probability on the `8J` elements `u^r σ^j a_j`
(resp. `u^r σ^j`), `r < 8`, `j < J`. Both lie in `P(B_m)`.

**Step 5 (one Ramsey call defeats one certificate).** *Let `p_0, …, p_{K−1} ≥ 0` with `Σ p_i ≤ 1` and
`f_0, …, f_{K−1} : F → [0,1]`. Put `n = R(m)` and `n' = 2A_1 n + A_1`. If `n < ∞`, some `ν̄ ∈ P(B_{n'})` has
`Σ_i p_i (g_iν̄(f_i) − ν̄(f_i)) ≤ 3/4`.*
- *The coded set in `V`.* Put `F̃(v) = Σ_i p_i f_i(y_i(v)) ∈ [0,1]`, which depends only on the `W`-part of `v`, and
  `θ(t) = ((t mod 8) + 1/2)/8`. Let `Ẽ_V = {v ∈ V : F̃(v) > θ(t(v))}`.
- *Transfer to `F`.* In each right coset `Vx` pick a representative `c` of minimal length, and write
  `x = v(x) c(x)` with `v(x) ∈ V`. Then `|c(x)| ≤ |x|`, so `|v(x)| ≤ 2|x|`, and `v(hx) = h v(x)` for `h ∈ V`. Let
  `E = {x ∈ B_n : v(x) ∈ Ẽ_V}` and let `ν ∈ P(B_n)` be the Ramsey witness for `E`, with `B_m·supp ν ⊆ B_n`. For
  `h ∈ V ∩ B_m` and `x ∈ supp ν` we have `hx ∈ B_n`, so `hx ∈ E ⟺ h v(x) ∈ Ẽ_V`. With `ν_V = v_*ν`, this gives
  `hν(E) = hν_V(Ẽ_V)`. Also `supp ν_V ⊆ B_{2n}`, so every coordinate `y_k(v)`, `v ∈ supp ν_V`, lies in `B_{n'}` by Step 3.
- *The Ramsey inequality.* Since `μ, μ' ∈ P(B_m)` are supported in `V`,
  `|Σ_{r<8, j<J} (u^rσ^ja_j ν_V(Ẽ_V) − u^rσ^j ν_V(Ẽ_V))| ≤ 8J/2`.
- *Averaging out the threshold (error ≤ 1/8).* By Step 2, `F̃(u^r h v) = F̃(hv)` and `t(u^r h v) = t(v) + r` for
  `h ∈ W`. For `x ∈ [0,1]`, `(1/8)#{r < 8 : x > θ(t + r)} = (1/8)#{s < 8 : x > (s + 1/2)/8}`, and this is within
  `1/16` of `x`. So for `h ∈ W`, `(1/8)Σ_{r<8} 1[u^r h v ∈ Ẽ_V] = F̃(hv) ± 1/16`. Using it for `h = σ^ja_j` and
  `h = σ^j` gives `|(1/J)Σ_{j<J} E_{v∼ν_V}[F̃(σ^ja_jv) − F̃(σ^jv)]| ≤ 1/2 + 1/8`.
- *The shift identity.* By Step 2 and Step 4, `y_i(σ^j a_j v) = g_i y_{i−j}(v)` and `y_i(σ^j v) = y_{i−j}(v)` for
  `0 ≤ i < K`. Hence `F̃(σ^ja_jv) − F̃(σ^jv) = Σ_i p_i [f_i(g_i y_{i−j}(v)) − f_i(y_{i−j}(v))]`.
- *Moving the window (error ≤ 1/8).* Put `d_i(k, v) = f_i(g_i y_k(v)) − f_i(y_k(v)) ∈ [−1,1]`. For fixed `i`, the
  index sets `{i − j : j < J}` and `{−j : j < J}` differ in at most `2i ≤ 2K` elements. So
  `|(1/J)Σ_j Σ_i p_i d_i(i−j, v) − (1/J)Σ_j Σ_i p_i d_i(−j, v)| ≤ 2K/J = 1/8` for every `v`.
- *The common marginal.* Let `ν̄ = (1/J)Σ_{j<J} (y_{−j})_*ν_V ∈ P(B_{n'})`. Then
  `E_{v∼ν_V}(1/J)Σ_j Σ_i p_i d_i(−j, v) = Σ_i p_i (g_iν̄(f_i) − ν̄(f_i))`. Combining the three displays,
  `Σ_i p_i (g_iν̄(f_i) − ν̄(f_i)) ≤ 1/2 + 1/8 + 1/8 = 3/4`.

**Step 6 (minimax: `CR_{3/2}(M) ≤ 2A_1 R(m) + A_1`).** Let `n' = 2A_1R(m) + A_1 < ∞` and `B' = B_{M+n'}`. Consider
the finite zero-sum game in which the minimizer picks `x ∈ B_{n'}`, the maximizer picks `(g, E)` with `g ∈ B_M` and
`E ⊆ B'`, and the payoff is `1_E(gx) − 1_E(x)`. For a mixed maximizer strategy `π`, put `p_g = Σ_E π(g,E)` and, when
`p_g > 0`, `f_g = p_g⁻¹ Σ_E π(g,E) 1_E : F → [0,1]`. The payoff against `ν ∈ P(B_{n'})` is
`Σ_{g ≠ e} p_g (gν(f_g) − ν(f_g))`, since the `g = e` terms vanish. So Step 5, applied with `p_i = p_{g_i}` and
`f_i = f_{g_i}`, gives a reply `ν̄` with payoff `≤ 3/4`. By von Neumann's minimax theorem some `ν ∈ P(B_{n'})` has
`gν(E) − ν(E) ≤ 3/4` for every pure `(g, E)`. Since `supp gν ⊆ B'` for `g ∈ B_M`, taking `E = {gν > ν} ∩ B'` gives
`‖gν − ν‖₁ = 2 max_E (gν(E) − ν(E)) ≤ 3/2`. So `CR_{3/2}(M) ≤ n'`.

The certificate has only `K ≤ 5^M` functions, whatever `n'` is. This is why the coded set has a bounded number of
coordinates, and why one Ramsey call at window `m = A_2K(M+1)` suffices.

**Step 7 (the theorem).** Apply Step 6 at `M' = 556M²` and then Step 1:
`CR(M) ≤ 2A_1 R(A_2 K'(M'+1)) + A_1 + 278M²`, with `K' ≤ 5^{M'}`. For `x = M' ≥ 556`, `(6/5)^x ≥ x + 1`, so
`A_2K'(M'+1) ≤ A_2 6^{556M²}`. Since `R` is nondecreasing, the theorem holds with `A = max(2A_1, A_2, A_1 + 278)`.

**Step 8 (Corollary 1, CRE(E)).** Write `A ≤ 2^a` and choose `E ≥ 3` with `2^{E−3} ≥ 1668 + a`. Here
`exp_0(x) = x` and `exp_{k+1}(x) = 2^{exp_k(x)}`. We have `exp_k(x) ≥ x + k`. Also `2^N ≥ N²/2` for `N ≥ 1`.
- *Inner argument.* `exp_{E−1}(N) ≥ 2^{N+E−2} = 2·2^{E−3}·2^N ≥ 2^{E−3}N² ≥ 1668N² + a`, so
  `exp_E(N) ≥ 2^{1668N²+a} ≥ A·6^{556N²}`, since `6 < 2³`.
- *Outer argument.* Let `y = R(exp_E(N))`. If `y = ∞` there is nothing to prove. Otherwise `y ≥ exp_E(N) ≥ N ≥ 1`,
  and by the theorem and monotonicity `CR(N) ≤ Ay + AN² ≤ 2Ay² ≤ 2^{a+1+2y}`. Since `E ≥ 2`,
  `exp_E(y) ≥ 2^{2^{y+E−2}}`, and `2^{y+E−2} ≥ 2^{E−2}(1+y) ≥ (a+1) + 2y`, using `2^{E−2} ≥ a+1` and `2^{E−2} ≥ 2`.
  So `CR(N) ≤ exp_E(R(exp_E(N)))` for all `N ≥ 1`.

**Step 9 (Corollaries 2–4).** Corollary 1 of `thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap` turns CRE(E)
into AMP(E+3), which is the negation of `thompson-f-ramsey-amplification-needs-unbounded-tower-overhead`. RGAP₁ is
literally "no `E` has CRE(E)", so it is false. Corollary 3 there gives RGAP₂ ⇒ ¬AMP, so RGAP₂ is false. Proposition D
of `thompson-f-ramsey-function-iterates-reach-towers` needs only AMP(D) for some `D`, so it now gives, for every `q`,
an `m` with `R(m) > exp_q(m)`. ∎

**Checks.**
- *Small case.* For `K = 2` and `J = 2`, the index bookkeeping in Step 5 was checked by hand. `a_0 = φ_0(g_0)φ_1(g_1)`
  and `a_1 = φ_{−1}(g_0)φ_0(g_1)`. Then `σa_1σ⁻¹ = φ_0(g_0)φ_1(g_1) = P`. Also `y_0(σa_1v) = g_0 y_{−1}(v)` and
  `y_1(σa_1v) = g_1 y_0(v)`, as the shift identity says.
- *Consistency with the `F_2` kill.* The argument needs a copy of `(G ≀ Z) × Z` in `G` with linear coordinate
  distortion, and `F_2` has no `Z²`. For non-amenable `G` with such an embedding, the theorem only says that `R`
  becomes infinite near `A·6^{556M²}` when `CR(M) = ∞`. This agrees with Moore's criterion.
- *Where the quantifiers are exchanged.* Only in Step 6. There the order "every certificate has a reply" becomes
  "one measure beats all `(g, E)`" by the finite minimax theorem. Step 5 depends on the certificate. This is exactly
  the dependence that Moore's definition allows, because `E` is arbitrary.

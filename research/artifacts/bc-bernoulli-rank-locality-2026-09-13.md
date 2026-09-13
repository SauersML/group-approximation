# Locality of Bernoulli ranks: mixed differences at far sites vanish, so shape (a) never occurs

Lane `ex3-bc-monster-shape-a`, 2026-09-13. Supports `bernoulli-pattern-expansions-are-finite` (route `-proof`).
Notation of `research/artifacts/bc-bernoulli-rank-functionals-2026-09-13.md` (cited as RF) and of
`research/artifacts/bc-bernoulli-cylinder-comparison-2026-09-13.md` (cited as CC).

**Question posed to this lane.** Can the embedded expanders of a torsion-free monster give a spectral gap that holds
uniformly over all configurations of the full shift, and so produce a class of shape (a) (RF, Corollary R8)?

**Answer.** No, and not for any host. A projection over `I_1 ⋊_r G` is already uniformly gapped at every
configuration. Its ranks are therefore local in the strongest sense: the mixed second difference at two far sites is
an integer trace bounded by `C e^(-α d)`, hence `0`. So every pattern expansion is finite, and shape (a) never occurs.

## 0. Setting and conventions

- `G` is countable and torsion-free, `Z = G`, `Λ = {0, ..., n}`, `X = Λ^G`, `I_1 = C_0(X \ {0})`.
- `ℓ` is a proper length function on `G` (the word length if `G` is finitely generated), and `d(g, h) = ℓ(g^(-1) h)`.
  This metric is left-invariant, and balls are finite.
- `π_x` is the orbit representation of RF Lemma R1, in the form used in RF Lemma R7. `f ∈ C(X)` acts diagonally by
  `f(h^(-1)·x)` at `δ_h`, and `u_g δ_k = δ_(k g^(-1))`. The row of `π_x(f u_g)` at `δ_h` lies in column `hg`, and
  `d(h, hg) = ℓ(g)`.
- `r_x = K_0(π_x)` is the rank functional, and `n(y)` is the pattern expansion of RF Lemma R5.
- A **configuration-local element** is `a = Σ_(g ∈ E) f_g u_g ∈ M_m(C(X) ⋊_alg G)` with `E` finite, `e ∈ E`, and each
  `f_g` locally constant, depending only on the coordinates in a finite `W ⊆ G`, with `f_g(0) = 0`.
  - Such elements are dense in `M_m(I_1 ⋊_r G)`.
  - Row `h` of `π_x(a)` is nonzero only if `x|_(hW) ≠ 0`. Its entries depend only on `x|_(hW)`, and its columns lie in
    `hE`.
  - So `π_x(a)` has finite rank when `x` has finite support.
- Constants: `K_a = Σ_g ||f_g||_∞`, `L = max_(g ∈ E) ℓ(g)`, `L_W = max_(w ∈ W) ℓ(w)`, `N_0 = W^(-1) E`,
  `L_N = max_(t ∈ N_0) ℓ(t)`, and `N(v) = v N_0`.
- `x^v` denotes `x` with the symbol at `v` replaced by some `s ∈ Λ`. `x^u` is defined the same way with `s'`, and
  `x^(uv)` makes both replacements.

## 1. Two estimates

**Lemma L1 (a single-site change is a bounded block).** Let `x` have finite support.
1. `Δ_v := π_(x^v)(a) - π_x(a)` satisfies `Δ_v = 1_(N(v)) Δ_v 1_(N(v))`, `||Δ_v|| <= 2||a||` and `rank Δ_v <= m|W|`.
2. If `d(u, v) > 2 L_W`, then `π_(x^(uv))(a) - π_(x^u)(a) = Δ_v`.

*Proof.*
1. Row `h` depends on `x_v` only if `v ∈ hW`, that is, `h ∈ v W^(-1) ⊆ N(v)`. Its columns lie in `hE ⊆ v W^(-1) E =
   N(v)`. The difference has at most `|W|` nonzero rows of `m × m` blocks.
2. Take a row `h` with `v ∈ hW`. If also `u ∈ hW`, then `ℓ(v^(-1) u) = ℓ(w^(-1) w') <= 2 L_W`. So `u ∉ hW`, and hence
   `x^(uv)|_(hW) = x^v|_(hW)` and `x^u|_(hW) = x|_(hW)`. Rows with `v ∉ hW` vanish in both differences. QED.

**Lemma L2 (Combes--Thomas decay, with no growth factor).** Let `b = Σ_(g ∈ E) f_g u_g` be as in Section 0, and let
`z ∈ C` with `||(z - π_x(b))^(-1)|| <= ρ`. Choose `α > 0` with `ρ K_b (e^(αL) - 1) <= 1/2`. Then for finite
`A, B ⊆ G`:

`||1_A (z - π_x(b))^(-1) 1_B|| <= 2ρ e^(-α d(A, B))`.

If `b'`, `z'` and `ρ` satisfy the same hypotheses, then
`||1_A (z - π_x(b))^(-1) (z' - π_(x')(b'))^(-1) 1_B|| <= 4ρ^2 e^(-α d(A, B))`.

*Proof.*
- Put `ψ(h) = min(d(h, B), d(A, B))`. It is bounded and 1-Lipschitz, so `e^(±αψ)` are bounded diagonal operators.
- `π_x(f_g)` is diagonal and commutes with them. Also `e^(αψ) u_g e^(-αψ) = u_g M_g`, where `M_g` is diagonal with
  entries `e^(α(ψ(k g^(-1)) - ψ(k)))`.
- Since `d(k g^(-1), k) = ℓ(g) <= L`, those entries lie in `[e^(-αL), e^(αL)]`. Hence
  `||e^(αψ) π_x(b) e^(-αψ) - π_x(b)|| <= K_b (e^(αL) - 1) <= 1/(2ρ)`.
- A Neumann series gives `||e^(αψ) (z - π_x(b))^(-1) e^(-αψ)|| <= 2ρ`.
- Write `1_A R 1_B = (1_A e^(-αψ)) (e^(αψ) R e^(-αψ)) (e^(αψ) 1_B)`. Here `ψ = d(A, B)` on `A` and `ψ = 0` on `B`.
- For a product, conjugate each factor separately.

No volume or growth bound on `G` enters: the conjugation error is a finite sum over `E`. QED.

## 2. The theorem

**Theorem 1 (far-site mixed differences vanish).** Let `p ∈ M_m(I_1 ⋊_r G)` be a projection. There is `d_0 = d_0(p)`
such that for every finite-support configuration `x`, every pair of sites `u, v` with `d(u, v) >= d_0`, and all
replacement symbols,

`M := r_(x^(uv))(p) - r_(x^u)(p) - r_(x^v)(p) + r_x(p) = 0`.

*Proof.*
1. **Approximation.** Choose a self-adjoint configuration-local `a` with `||a - p|| < 1/8`, so `||a|| <= 9/8`.
   - For every finite-support `x`, `spec π_x(a) ⊆ [-1/8, 1/8] ∪ [7/8, 9/8]`.
   - `P_x = χ_([1/2, ∞))(π_x(a))` is a finite-rank projection with `rank P_x = r_x(p)` (RF Lemma R7, bullet "Ranks").
2. **Riesz form.** Let `Γ = {|z - 1| = 1/2}`, so `dist(Γ, spec π_x(a)) >= 3/8` and `||R_x(z)|| <= ρ := 8/3`, where
   `R_x(z) = (z - π_x(a))^(-1)`. Then `P_x = (1/2πi) ∮_Γ R_x(z) dz`, and `0 ∉` the inside of `Γ`.
   - The resolvent identity gives `P_(x^v) - P_x = (1/2πi) ∮ R_(x^v) Δ_v R_x dz`.
   - This integrand is finite rank and trace-norm continuous, so `r_(x^v)(p) - r_x(p) = (1/2πi) ∮ Tr(R_(x^v) Δ_v R_x) dz`.
3. **Mixed difference.** Write `R_(ij)` for the resolvents at `x_00 = x`, `x_10 = x^v`, `x_01 = x^u`, `x_11 = x^(uv)`.
   - Take `d_0 > 2 L_W`. By L1(2), both `v`-changes are `Δ_v` and both `u`-changes are `Δ_u`.
   - So `M = (1/2πi) ∮ Tr(R_11 Δ_v R_01 - R_10 Δ_v R_00) dz`.
   - Using `R_11 - R_10 = R_11 Δ_u R_10` and `R_01 - R_00 = R_01 Δ_u R_00`, the integrand is
     `Tr(R_11 Δ_u R_10 Δ_v R_01) + Tr(R_10 Δ_v R_01 Δ_u R_00)`.
4. **Estimate.** Let `κ = ||Δ_u||_1 <= m|W| · 9/4` and `δ = d(N(u), N(v)) >= d(u, v) - 2 L_N`.
   - Cyclicity and `Δ_u = 1_(N(u)) Δ_u 1_(N(u))`, `Δ_v = 1_(N(v)) Δ_v` give the following bounds, using L2 with
     `ρ = 8/3` and `K_a (e^(αL) - 1) <= 3/16`:
     - `|Tr(Δ_u R_10 Δ_v R_01 R_11)| <= κ · ||1_(N(u)) R_10 1_(N(v))|| · (9/4) ρ^2 <= κ (16/3)(9/4)(64/9) e^(-αδ)`;
     - `|Tr(Δ_u R_00 R_10 Δ_v R_01)| <= κ · ||1_(N(u)) R_00 R_10 1_(N(v))|| · (9/4) ρ <= κ (256/9)(9/4)(8/3) e^(-αδ)`.
   - The contour has length `π`, so `|M| <= (1/2) C_0 e^(-αδ)`, with `C_0 = κ (9/4)(1024/27 + 2048/27) = 256 κ`.
5. **Integrality.** `M` is an integer. Put `d_0 = 1 + max(2 L_W, 2 L_N + α^(-1) log C_0)`. Then `|M| < 1/2`, so
   `M = 0`. QED.

**Corollary 2 (pattern expansions are finite).** For every `y ∈ K_0(I_1 ⋊_r G)` there is `d_0(y)` such that
`n_([t])(y) = 0` for every pattern `t` whose support has diameter at least `d_0(y)`.
- Consequently `n(y)` is supported on finitely many `G`-orbits of patterns.
- Also `r_x(y) = r_x(T_r(n(y)))` for every finite-support `x`.

*Proof.*
- **Classes.** `C_0(X \ {0})` has an approximate unit of projections, which is also one for the crossed product. So
  `y = [p] - [q]` with `p` and `q` projections over `I_1 ⋊_r G`. Take `d_0(y) = max(d_0(p), d_0(q))`.
- **Möbius form.** Fix a pattern `x` with support `S` and set `F(U) = r_(x|_U)(y)` for `U ⊆ S`, with `F(∅) = 0`. RF
  Lemma R5 reads `n_([x])(y) = Σ_(U ⊆ S) (-1)^(|S \ U|) F(U)`, which is the iterated difference `(Π_(w ∈ S) ∂_w) F (∅)`.
- **Vanishing.** Suppose `u, v ∈ S` with `d(u, v) >= d_0(y)`. Theorem 1, applied at every `x|_V` with
  `V ⊆ S \ {u, v}`, gives `∂_u ∂_v F ≡ 0`. Differences commute, so `n_([x])(y) = 0`.
- **Finitely many orbits.** Every pattern of diameter `< d_0` has a translate whose support contains `e` and lies in
  the ball of radius `d_0`. That ball is finite, and so is `Λ`.
- **Ranks.** Finally, `r_x(y) = Σ_(t <= x) n_([t])(y) = r_x(T_r(n(y)))` by RF Lemmas R2 and R5. QED.

**Corollary 3 (no shape (a)).** Shape (a) of RF Corollary R8 never occurs, over any countable torsion-free host. So
`T_r` fails to be surjective iff there is a nonzero rank-invisible tail class (shape (b)) or `K_1(I_1 ⋊_r G) ≠ 0`
(shape (c)).
- *Proof.* By Corollary 2, `n(y)` is finitely supported for every `y`. The proof of RF Corollary R8 then sends each
  `y ∉ im T_r` to shape (b), and degree 1 is shape (c). QED.

**Corollary 4 (uniformly gapped local operators have local ranks).** Let `b ∈ M_m(C(X) ⋊_alg G)` be self-adjoint and
configuration-local. Suppose there are `0 <= γ_1 < γ_2` such that `spec π_x(b) ∩ (γ_1, γ_2) = ∅` for every
finite-support `x`. Then `x ↦ rank χ_([γ_2, ∞))(π_x(b))` is a finite integer combination of pattern counts.

*Proof.*
- **The gap passes to the algebra.** The family `(π_x)_(x ∈ X)` is faithful on `C(X) ⋊_r G`, and
  `x ↦ ||π_x(c)||` is lower semicontinuous. Finite-support configurations are dense in `X`. So the gap holds in the
  spectrum of `b`.
- **A projection in the ideal.** With a continuous `φ` that is `0` on `(-∞, γ_1]` and `1` on `[γ_2, ∞)`, `φ(b)` is a
  projection in `M_m(I_1 ⋊_r G)`, because `φ(0) = 0`. Its ranks are the ranks in the statement.
- **Conclusion.** Apply Corollary 2. QED.

## 3. What this decides, and model tests

- **The question posed.** A spectral gap uniform over all Bernoulli configurations is exactly what any projection
  over `I_1 ⋊_r G` supplies. Corollary 4 shows every such gap produces only a finite pattern count. No construction
  from embedded expanders, isometric or weak, gives a shape-(a) class on any host. That includes the Laplacian of
  induced subgraphs, local potentials, and Dirac or incidence operators.
  - The expander gap on the marking subshift (`bc-counterexample-via-ghost-projection`, the HLS mechanism) is
    unaffected. The subshift admits no single-site changes, and Theorem 1 uses them.
- **Model test 1 (amenable host).** For `G = Z`, CC Section 4 gives `T_r` an isomorphism, which is consistent.
- **Model test 2 (why the gap and integrality are needed).** On `Z^2`, the induced-subgraph component count `c` is not
  local.
  - Let `S` be the boundary of an `L × L` square with two opposite side midpoints `u, v` removed.
  - Then `c(S ∪ {u,v}) - c(S ∪ {u}) - c(S ∪ {v}) + c(S) = 1 - 1 - 1 + 2 = 1`, at distance `L`.
  - The projections onto constants on components form a continuous field that is not in the crossed product. Long
    induced paths have no gap, as in the Attempts of `bernoulli-cylinder-comparison-fails-for-some-group`. So the
    theorem is not vacuous: it rules out exactly this kind of rank.
- **Model test 3.** For `p = 1_(C_s)`, `r_x` counts occurrences of `s` (RF R2), and every mixed difference at distance
  `> diam F_s` vanishes, as it should.
- **Consistency with `bernoulli-defects-vanish-along-bcc-subgroup-tubes`.** For shape (a), Corollary 2 is stronger:
  finiteness holds with no hypothesis on subgroups. The tube statements about shapes (b) and (c) are not affected.

## 4. What remains

- **Where a witness must live.** A Bernoulli witness beyond the host is invisible to every finite-support orbit
  representation. It is either a rank-zero class in `∩_k im K_0(I_k ⋊_r G)`, or an odd class.
  - Its detectors must look at infinite-support configurations, such as a restriction to a closed invariant subset
    like the expander-marking subshift `Y_A = closure(G · 1_(⊔ A_n))`.
  - Or through the Haar trace with Lück's ring `Z[1/p]` (CC item 7), which is not a finite-support rank.
- **Sharpest next question.** Does the HLS ghost class of `C_0(Y_A \ {0}) ⋊_r G` lift along the restriction
  `I_1 ⋊_r G -> C_0(Y_A \ {0}) ⋊_r G`?
  - A lift minus `T_r(n(lift))` would be rank-invisible.
  - Its image on `Y_A` would differ from the ghost class by restrictions of cylinder classes.
  - Not decided here.

## 5. Scope and credit

- **Techniques.** The estimates are standard in mathematical physics:
  - the Combes--Thomas exponential decay of resolvents (J.-M. Combes, L. Thomas, Comm. Math. Phys. 34 (1973));
  - integrality of relative traces of projections (index of a pair of projections; Avron--Seiler--Simon, J. Funct.
    Anal. 120 (1994)).

  Both are proved inline in the form needed and are not imported.
- **Bounded novelty check.** The locality statement is not in RF, CC, the tube artifact, or CEKN arXiv:2210.09209
  Sections 1--2 as read by earlier lanes. No web search was done.
- **Not re-read.** HLS, Osajda and CEKN were not re-read by this lane, and Theorem 1 uses none of them.
- **Status.** Unreviewed by `ex-verify-*`.

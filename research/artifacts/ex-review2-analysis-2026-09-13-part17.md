# EX review wave 2, part 17: Bauer division, Toms rounding and the BK boundary (census priority D, 2026-09-13)

Lane `ex-verify2-analysis`. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0. Census: part 11. The two Toms
realizer theorems of this batch are in part 13.

**Blobs.** Rechecked at tip `09e244d0f1`.
- **ex2-tw-hilbert-cube-boundary:**
  - `bauer-strict-comparison-unit-divides-iff-atomless-element` and `zero-dimensional-atomless-diagonal-divides-unit`
    (`c174e86dc`);
  - `bauer-unit-division-defect-uniform-criterion` (`c53085883`, route `041b86bcf`);
  - `square-atomless-measure-family-forces-dirac-pushforward` (`2b7ad1e79`).
- **ex2-rank-monotone-rounding:**
  - `toms-block-diagonal-sharpening-has-fuzz-persistence` (`5250036b3`);
  - `toms-monotone-block-rounding-obeys-a-miranda-granularity-bound` (`373403ba5`, route `21a227faa`);
  - `toms-rank-bookkeeping-admits-monotone-realizer-profiles` (`66e86d194`).
- **ex2-bk-relative-lemma-b:** `bk-relative-boundary-descends-or-is-positively-detected` (`cd89f81b4`).

**Prerequisites, all with a PASS.**
- `strict-comparison-compares-ultrapower-projections`: `review-toms-winter-ultrapower-comparison-2026-09-12.md`.
- `strict-comparison-unit-divisibility-equivalences`, `bauer-strict-comparison-pure-iff-divisible-unit` and
  `toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`: ex-review-analysis 2026-09-12 part 4.
- Proposition 8.2 and `bauer-unit-division-metric-order-criterion`: part 2 §2.7.
- `bk-radical-traces-vanishing-on-boundary-are-zero` and `bk-radical-projection-quotients-are-toeplitz-infinite`:
  part 5.

## 17.1 Verdicts

| claim | verdict |
|---|---|
| `bauer-strict-comparison-unit-divides-iff-atomless-element` | PASS |
| `zero-dimensional-atomless-diagonal-divides-unit` | PASS |
| `bauer-unit-division-defect-uniform-criterion` | PASS |
| `square-atomless-measure-family-forces-dirac-pushforward` | PASS |
| `toms-block-diagonal-sharpening-has-fuzz-persistence` | PASS |
| `toms-monotone-block-rounding-obeys-a-miranda-granularity-bound` | PASS; its corollary is vacuous after part 13, as the node says |
| `toms-rank-bookkeeping-admits-monotone-realizer-profiles` | PASS |
| `bk-relative-boundary-descends-or-is-positively-detected` | PASS, one wording note |

## 17.2 Re-derivations

**Atomless element ⟺ division.**
- **(i) ⟹ (ii).**
  - The atom of `h = Σ_j (j/N)φ(e_jj)` at `0` is at most `λ(1 − φ(1))`.
  - The pieces share one distribution `ν` on `(0, 1]` of mass `≤ 1/N`.
  - An atom at `x > 0` collects `ν` at the distinct points `Nx/j`, so it is at most `1/N`.
- **(ii) ⟹ concentration.** If no `η` works, take a limit point `(λ, x)` of the witnesses. Weak* continuity of
  `λ ↦ μ_{h,λ}` and Portmanteau on closed intervals give an atom of mass `≥ ε`.
- **CDF transform.** `μ(−∞, s − η] ≤ F(λ, s) ≤ μ(−∞, s)` and `F` is jointly continuous. The central `θ(C(K))` acts as
  scalars in the fibres.
- **(iii) ⟹ (i).**
  - Lipschitz functions are Lipschitz in the trace 2-norm with the same constant, which gives the ramp bounds
    `O(η_n + ε_n/η_n)`.
  - The resulting projections of `A^ω` have limit traces `j/k`. Ultrapower comparison places `k` orthogonal copies, and
    the remainder has zero limit traces, so it is `0`.
  - Order zero lifting finishes.
- **Zero-dimensional diagonal.** `h: Y ↪ [0, 1]` gives `μ_{h,λ} = h_*(λ|_{C(Y)})`, whose atoms are the masses of single
  points, hence `0`.

**Defect-uniform criterion.**
- **Lemma H.1.**
  - Order zero calculus gives `e_j − e_j^2 = f(φ)(e_jj)`, with trace `λ(φ(1) − φ(1)^2)/N ≤ δ/N`.
  - At most `Nth(λ) + 1` coefficients are nonzero and at most one is fractional. So
    `λ(B − B^2) ≤ th(λ)δ + δ/N + 1/(4N)`.
- **Summation.** `Σ_i th_iδ_i ≤ t max_i δ_i` and `Σ_i (δ_i + 1/4)/N_i ≤ 2Σ_i 1/N_i`.
- **Constants.** With `s = ε_0/8` and `κ = ε_0^2/384`, the defect term `2(2κ + tκ)/s ≤ 48κ/ε_0 = ε_0/8`. So the rank sums
  lie in `[t − ε_0/8, t + ε_0/2]`, and the moves run as in the reviewed Proposition 8.2.
- **Hilbert cube.** `ord_Q(r) ≤ log_2(4/r) + 2` turns `ord > κ_0N` into `ℓ_A(N, κ_0) < 16·2^{−κ_0N}`.

**Dirac pushforwards on the square.**
- **Dimension.** The components of level sets form an upper semicontinuous decomposition. `f = g∘q` with `g` light, so
  Hurewicz gives `dim Γ ≤ 1`.
- **Lebesgue covering.** If every component had diameter `< 1`, the maximum diameter would be attained. A pulled-back
  order-2 cover of small mesh meets no two opposite sides, which contradicts Lebesgue's covering theorem (order `≥ 3`).
- **The measure.** `diam C ≥ 1` gives a projection interval of length `≥ 1/√2`. Kuratowski--Ryll-Nardzewski supplies
  the Borel section.
- **The family.** It is closed under weak* limits of witnesses `(i, J)`, and its members are atomless through their
  marginals.

**Fuzz persistence.**
- **Degree.** On `∂[0,1]^K` some `t_i ∈ {0, 1}`. So `G_i = Λ_i ∈ {a, b}`, and along both straight-line homotopies the
  coordinate stays within `C` of `a` or `b`, never at `c ∈ (a + C, b − C)`.
- **Defect.** `λ(1 − λ) ≥ min(λ, 1 − λ)/2`, and `dist(Σλ_j, Z) ≤ Σ min(λ_j, 1 − λ_j)`. So each block has
  `Tr(e_i − e_i^2) ≥ 1/4`, and the normalized bound is `1/(4kr_L)`.

**Miranda granularity bound.**
- **Poincaré--Miranda.** `u_b = dist(·, Q∖V_b) − dist(·, V_b)`. `Q∖V_b ≠ ∅` because the face `{t_b = 0}` misses `V_b`.
- **Budget.** `rank_b ≤ r_nF_n(w^{(b)}) + (K − 1)r_nε_n`, from block-diagonality and domination of the other blocks.
- **Jump.** The integer wall `k` exists when `r_n(ρ − Kε_n) ≥ 2`. The all-wall jump gives `ε_M ≥ K/r_M = 1/r_n`.
- **Golden rate.**
  - `Cr_n^{−γ}2^{M−n}` decreases in `n`, and the minimal `n` tends to infinity.
  - Minimality gives `r_M > c_0r_n^{1+γ}`. So `r_M^{−γ} ≳ r_M^{−1/(1+γ)}`, hence `γ^2 + γ ≤ 1`.

**Rank bookkeeping.**
- `ceil` is lower semicontinuous, and `g − 2 ≤ R_n ≤ g`.
- **Superadditivity.** For `g_1, g_2 > 2`: `ceil(g_1 − 2) + ceil(g_2 − 2) < g_1 + g_2 − 2 ≤ ceil(g_1 + g_2 − 2)`. The
  other cases are immediate.
- **The ramp.** For `j ≥ 1`, `c_j = clamp(g − 1 − j) > 0` iff `j ≤ ceil(g − 2)`, so the rank is `R_n`. The node indexes
  lines from `1`.

**BK boundary descent.**
- **Descent.** The pullback `σ∘π∘q_J` is densely finite, since surjections carry Pedersen ideals onto Pedersen ideals,
  and it annihilates `H`. Theorem 7 makes it `0`.
- **Obstruction.** A nonzero class in `G ∩ K_0^+` is a nonzero projection, which stays nonzero under a faithful map
  into a stably finite algebra.
- **Where the peeling stalls.** Six-term exactness gives `ker π_* = im K_0(I)`. Spielberg for
  `0 → R/K → E/K → E/R → 0` covers the escaping case.
- **Forced stall.** This is Corollary 10.

## 17.3 Notes

- **Stale wording.** `bk-relative-boundary-descends-or-is-positively-detected` says it is "conditional on the
  unreviewed Theorem 7 = `bk-radical-traces-vanishing-on-boundary-are-zero`", but that node has PASS in part 5. The
  condition can be dropped from the wording. Sent to the owner.
- **Minor, not sent.** In `toms-rank-bookkeeping-monotone-profiles-proof` Step 2, `R_n < max(0, g − 1)` is strict only
  when `g > 1`. It should read `≤`, and the sandwich is unaffected.

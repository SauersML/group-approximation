# Strict comparison divides the unit over C-space tracial boundaries, part 2 (2026-09-13)

Lane `ex-tw-rotation-gluing`. Continues `research/artifacts/ex-tw-c-space-unit-division-2026-09-13.md`
(Theorem A, facts (F1)–(F5), Lemmas 1–3). Not reviewed.

## 3. Proof of Theorem A

Fix `n ≥ 1` and put `t = (2n+1)/(2n(n+1))` and `γ = 1/(2n(n+1))`, so `(t − γ, t + γ) = (1/(n+1), 1/n)`.
Put `ε = γ/2`. Then `t ≤ 3/4` and `ε ≤ 1/8`, so `1 − t − ε ≥ 1/8`.

**Step 1 (precisions).**
- Choose `N_k ≥ 1` and `δ_k > 0` for `k ≥ 1`. Put `d_k = 1/(4N_k) + δ_k` and `s_k = d_k^{1/2}`.
- Require `s_k ≤ 1/2` and `Σ_k (6 s_k + δ_k) ≤ ε/2`; for instance `d_k = (ε/(16·2^k))²`.

**Step 2 (screening).**
- Let `U_k` be the family of open `O ⊂ K` for which some c.p.c. order zero `φ: M_{N_k} → A` has
  `λ(1 − φ(1)) < δ_k` on `O`. By Lemma 1, `U_k` covers `K`.
- Property C gives disjoint open families `V_k` refining `U_k` with `⋃_k V_k` covering `K`. By compactness,
  finitely many members `V_{k,a}` with `k ≤ L` already cover `K`.
- Take open `V'_{k,a}` with `cl V'_{k,a} ⊂ V_{k,a}` that still cover `K` (shrinking a finite open cover of a
  normal space).
- Each `V_{k,a}` lies in a member of `U_k`, so it carries an order zero map at precision `(N_k, δ_k)`.
  Lemma 2, with the closed sets `cl V'_{k,a}`, gives order zero `φ_k: M_{N_k} → M` with
  `λ(1 − φ_k(1)) < δ_k` on `⋃_a cl V'_{k,a}`.
- Put `W_k = ⋃_a V'_{k,a}`. The `W_k` cover `K`, so choose a partition of unity `h_1, …, h_L` with
  `supp h_k ⊂ W_k`. Then `φ_k` is `δ_k`-good on `supp h_k`.

**Step 3 (staircases and approximants).**
- Lemma 3 with `(φ_k, h_k, t)` gives `B_k ∈ M`.
- Put `s_min = min_{k≤L} s_k`, and choose `η > 0` with `3η ≤ min_{k≤L} d_k`, `8Lη/s_min ≤ ε/4` and
  `Lη ≤ ε/8`.
- (F5) gives positive contractions `b_k ∈ A` with `‖b_k − B_k‖_{2,u} ≤ η`. Put `x_k = (b_k − s_k)_+`.

**Step 4 (rank bounds).** For `λ ∈ K` and `s_k ≤ σ ≤ 1/2`:
```text
(R-up)   μ_{b_k,λ}((σ,1])  ≤  t h_k(λ) + 6 s_k + 8η/s_min,
(R-low)  μ_{b_k,λ}((σ,1])  ≥  t h_k(λ) − δ_k − η − σ.
```
- **Upper bound, active case (`h_k(λ) > 0`).** Lemma 3 and (F5) give `λ(b_k) ≤ t h_k(λ) + η` and
  `λ(b_k − b_k²) ≤ d_k + 3η ≤ 2 d_k`. Monotonicity in `σ` and (F2) at `s = s_k` give
  `≤ (t h_k(λ) + η)(1 + 2 s_k) + 4 d_k/s_k ≤ t h_k(λ) + 6 s_k + 2η`.
- **Upper bound, inactive case (`h_k(λ) = 0`).** Lemma 3(i) and (F5) give `λ(b_k) ≤ η` and
  `λ(b_k − b_k²) ≤ 3η`, so (F2) gives `≤ 2η + 6η/s_k ≤ 8η/s_min`.
- **Lower bound.** (F2) and Lemma 3(ii).

**Step 5 (orthogonalizing moves).**
- Choose `ε'_k, ε_k > 0` with `Σ_{k≤L} (ε'_k + ε_k) ≤ ε/(8L)`. Put `W_0 = 0`.
- **Inductive hypothesis at stage `k − 1`.** `W_{k−1} ∈ A` is a sum of pairwise orthogonal positive
  contractions `w_i^{(k−1)}`, `i < k`, with `d_λ(w_i^{(k−1)}) = μ_{b_i,λ}((σ_i,1])` for some
  `σ_i ∈ [s_i, s_i + ε/(8L)]`. In particular (R-up) bounds each `d_λ(w_i^{(k−1)})`.
- **Free space.** Put `F_{k−1} = 1 − min(1, W_{k−1}/ε_k) ∈ A_+`.
  - Its support is where the spectrum of `W_{k−1}` lies below `ε_k`, so
    `d_λ(F_{k−1}) ≥ 1 − d_λ(W_{k−1}) ≥ 1 − Σ_{i<k} (t h_i(λ) + 6 s_i + 8η/s_min)`.
  - With (R-up) for `x_k`, and `Σ_i h_i ≤ 1`:
    ```text
    d_λ(F_{k−1}) − d_λ(x_k)  ≥  1 − t − Σ_{i≤L} 6 s_i − 8Lη/s_min  ≥  1 − t − 3ε/4  ≥  1/8.
    ```
  - Integrating over `μ_τ` (F1) gives `d_τ(x_k) < d_τ(F_{k−1})` for every `τ ∈ T(A)`.
- **The move.**
  - Strict comparison gives `x_k ≾ F_{k−1}`. (F3) gives `c_k ∈ A` with `c_k c_k* = (x_k − ε'_k)_+` and
    `c_k* c_k ∈ her(F_{k−1})`.
  - Put `W_k = (W_{k−1} − ε_k)_+ + c_k* c_k`.
- **Exact orthogonality.**
  - `1 − min(1, s/ε_k)` vanishes for `s ≥ ε_k`, so `F_{k−1}(W_{k−1} − ε_k)_+ = 0`. Every element of
    `her(F_{k−1})` is therefore orthogonal to `(W_{k−1} − ε_k)_+`.
  - Since the `w_i^{(k−1)}` are orthogonal, `(W_{k−1} − ε_k)_+ = Σ_{i<k} (w_i^{(k−1)} − ε_k)_+`.
- **The hypothesis at stage `k`.**
  - Put `w_i^{(k)} = (w_i^{(k−1)} − ε_k)_+` for `i < k`, and `w_k^{(k)} = c_k* c_k`.
  - These are orthogonal positive contractions.
  - By (F3), `d_λ((c_k* c_k − r)_+) = μ_{b_k,λ}((s_k + ε'_k + r, 1])`.
  - Subtracting `ε_k` raises each `σ_i` by `ε_k`, and the total increase stays below `ε/(8L)`.

**Step 6 (the rank of the result).** Put `W = W_L ∈ A`. Ranks add over orthogonal positive elements, so
```text
d_λ(W) = Σ_{k≤L} μ_{b_k,λ}((σ_k,1])     with σ_k ∈ [s_k, s_k + ε/(8L)].
```
- By (R-up), `d_λ(W) ≤ t Σ_k h_k(λ) + Σ_k 6 s_k + 8Lη/s_min ≤ t + 3ε/4`.
- By (R-low), `d_λ(W) ≥ t − Σ_k (δ_k + s_k) − Lη − ε/8 ≥ t − 3ε/4`.
- Integrating over `μ_τ` gives `|d_τ(W) − t| < γ` for every `τ ∈ T(A)`.

**Step 7 (division).**
- For every `τ`: `n d_τ(W) < n(t + γ) = 1` and `(n+1) d_τ(W) > (n+1)(t − γ) = 1`.
- Strict comparison in matrix algebras over `A` gives `n[W] ≤ [1_A] ≤ (n+1)[W]` in `W(A)`.
- As `n` is arbitrary, item 3 of `strict-comparison-unit-divisibility-equivalences` holds, hence item 1:
  the unit is tracially `N`-divisible for every `N`. ∎

## 4. Corollary B and scope

**Corollary B.** Let `A` be as in Theorem A.
- `A` is pure, by `bauer-strict-comparison-pure-iff-divisible-unit`, (e) ⟹ (a).
- If `A` is nuclear with tracially locally finite nuclear dimension, then `A ≅ A ⊗ Z`, by
  `toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`, (e) ⟹ (a).

**What was already covered, and what is added** (relative to the graph and the literature recorded there).
- *Nuclear `A`, `dim K < ∞`.* Toms–Winter was already known here (`stw18-finite-trace-boundary-toms-winter`).
- *Nuclear `A`, `K` a countable union of closed finite-dimensional compacta.* The bundle is trivial
  (`r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial`). So `A` has uniform Gamma
  (`bauer-uniform-gamma-iff-trivial-tracial-bundle`), and CETW gives `Z`-stability with no tlfnd hypothesis.
- *Added, exact algebras.* Purity under strict comparison for exact algebras, possibly non-nuclear, with
  Bauer simplex and C-space boundary, finite-dimensional boundaries included. That is STW XXVII(1) on this
  locus.
- *Added, nuclear algebras.* `Z`-stability with tlfnd over C-space boundaries that are not countable unions
  of closed finite-dimensional compacta.
  - That such compacta exist is recalled, not re-read: R. Pol's weakly infinite-dimensional,
    not countable-dimensional compactum (Proc. AMS 82, 1981) is reported to have property C.
  - No specific example is asserted here as verified.
- Whether every weakly infinite-dimensional compactum has property C is, as recalled, an open problem of
  dimension theory. So the method's reach among weakly infinite-dimensional boundaries is itself undecided.

## 5. Where the method stops, and a local-to-global form

**Rotation is not needed.** Rotation gluing by central cosines needs partial isometries between two local
halvings on each overlap. Strict comparison only compares global elements. The staircase-and-move scheme
avoids overlaps altogether:
- each piece is global, with a controlled rank everywhere;
- strict comparison moves it into the exact orthogonal complement of the earlier pieces.

**Why property C, and why no adaptivity.**
- A piece contributes rank overshoot `6 s_k` only where it is active. Every level is a disjoint family, so
  at any point each level has at most one active piece, and the overshoots sum to at most `Σ_k 6 s_k`.
- The covers `U_k` depend only on the precision `(N_k, δ_k)`, never on earlier levels. The moves use strict
  comparison, not commutation with earlier pieces.
- The central analogue (uniform Gamma, bundle triviality) needs later local systems to approximately commute
  with earlier ones. Its covers are adaptive, so property C alone does not obviously suffice there.
- This is why Theorem A reaches C-spaces while bundle triviality is established only for countable unions of
  closed finite-dimensional compacta.

**Proposition D (local-to-global).** Let `A` be unital, simple, separable, exact and non-elementary, with
strict comparison and a nonempty Bauer simplex. Say the unit *divides over* a closed `Y ⊂ K` if for all `N`
and `δ > 0` some c.p.c. order zero `φ: M_N → A` has `λ(1 − φ(1)) < δ` for every `λ ∈ Y`. If every point of
`K` has a closed neighbourhood over which the unit divides, then the unit is tracially `N`-divisible for
every `N`.

*Proof.*
- Finitely many interiors `int Y_1, …, int Y_L` cover `K`. Use them as the levels of Section 3, one set per
  level, with partition of unity `supp h_k ⊂ int Y_k`.
- Since `L` is now fixed before the precision, choose one precision `(N, δ)` for all levels with
  `L(6 d^{1/2} + δ) ≤ ε/2`, where `d = 1/(4N) + δ`.
- For each `k` take an order zero map that is `δ`-good on `Y_k`; Lemma 2 is not needed.
- Steps 3–7 apply verbatim. ∎

**Consequence for counterexamples.** Let `A` be a strict-comparison algebra with Bauer simplex whose unit is
not tracially divisible.
- The *division locus* `Z_div(A)`, the set of points with no closed neighbourhood over which the unit
  divides, is closed and nonempty. It is closed because its complement is open by definition.
- `K` does not have property C.
- It is not proved that `Z_div(A)` has no C-space neighbourhood. The construction over a closed C-space `Y`
  gives elements of controlled rank near `Y`, not order zero maps over `Y`. A local form of Rørdam–Winter's
  Proposition 5.1 would close that gap.

**The Hilbert cube (heuristic, not proved).** Suppose that at precision `(N, δ)` the good neighbourhoods have
small diameter in the first `d(N, δ)` coordinates, with `d → ∞`.
- Any finite family of levels built from disjoint refinements must still cover each face `[0,1]^d`.
- Lebesgue's covering theorem forces at least `d + 1` levels at a common mesh.
- So summable screening fails. A counterexample over the Hilbert cube must have local divisions that shrink,
  in unboundedly many coordinates, as the precision grows.

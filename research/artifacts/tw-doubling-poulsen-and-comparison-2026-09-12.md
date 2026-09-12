# Doubling AH systems have the Poulsen simplex, and strict comparison blinds the bundle certificate

Lane `tw-doubling-witness`, 2026-09-12.

**Task.** Build an inductive limit with doubling connecting maps whose extreme
traces form a closed set, keeping strict comparison and equal-trace projections
that are not approximately equivalent. Or prove the requirements incompatible.

**Outcome.**
1. Theorem 3: every diagonal system with doubling form, diagonal points, free
   leaf labels and summable contamination has a dense extreme boundary. Toms's
   non-simple limit (arXiv:2606.12188v2, Section 4) and his simple algebra
   (Proposition 4) are instances, so both trace simplices are the Poulsen
   simplex and neither is Bauer.
2. Theorem 4: in every unital simple separable exact non-elementary algebra with
   strict comparison, equal-trace projections of the uniform tracial completion
   are approximately equivalent. So strict comparison and the equal-trace
   certificate of `trivial-r-fibre-bundles-compare-equal-trace-projections` are
   incompatible, whatever the connecting maps and the simplex.
3. Section 7 records what a Bauer doubling system would have to give up.

No witness for BBSTWW Question 3.14 is produced.

## 1. Setting

Let `A_i = s_i (C(X_i) ⊗ K) s_i`, where `X_i` is compact metrizable and `s_i`
has constant rank `r_i`. Write `tr_x` for the normalized fibre trace at `x`.
Every trace on `A_i` is `∫ tr_x dμ(x)` for a unique `μ ∈ Prob(X_i)`, so
`T(A_i) = Prob(X_i)`.

Let `φ_i : A_i → A_{i+1}` be unital and `A = lim (A_i, φ_i)`.
- For `y ∈ X_{i+1}`, `tr_y ∘ φ_i` is a trace on `A_i`, with measure `P_i(y)`.
- `ψ_i(μ) = ∫ P_i(y) dμ(y)` is the dual map `T(A_{i+1}) → T(A_i)`. It extends to a
  positive, mass-preserving linear map on finite signed measures, so it does not
  increase total variation `‖·‖_TV`.
- `T(A) = lim← (Prob(X_i), ψ_i)`. Write `μ_i` for the measure of `τ|A_i`, and
  `Ψ_{r,N} = ψ_r ∘ ··· ∘ ψ_{N−1}`.

**Doubling form.** The system has doubling form with contamination `α_i ∈ (0,1]` if

```text
P_i(y) = α_i |W_i|^{-1} Σ_{w ∈ W_i} δ_{λ_{i,w}(y)} + (1 − α_i) ν_i(y),     Σ_i (1 − α_i) < ∞,
```

Here `W_i` is finite with `|W_i| ≥ 2`, the maps `λ_{i,w} : X_{i+1} → X_i` are
continuous, and each `ν_i(y)` is a probability measure.

Two further conditions:
- **(D) diagonal points.** There are maps `d_i : X_i → X_{i+1}` with
  `λ_{i,w} ∘ d_i = id` for every `w`.
- **(F) free labels.** The joint map `Λ_i = (λ_{i,w})_w : X_{i+1} → X_i^{W_i}` is
  surjective.

## 2. Concentration at deep stages gives extremality

**Lemma 1.** Let `τ = (μ_r) ∈ T(A)`, and suppose there are points `x_N ∈ X_N`
with `μ_N({x_N}) → 1`. Then `τ` is extreme.

*Proof.* Suppose `τ = tτ' + (1 − t)τ''` with `0 < t < 1`, and put
`m_N = μ_N({x_N})`.
- Since `μ'_N ≤ μ_N / t`, we get `μ'_N({x_N}) ≥ 1 − (1 − m_N)/t`.
- So `‖μ'_N − δ_{x_N}‖_TV ≤ 2(1 − m_N)/t` and `‖μ_N − δ_{x_N}‖_TV = 2(1 − m_N)`.
- For `r ≤ N`, `μ'_r − μ_r = Ψ_{r,N}(μ'_N − μ_N)`, whose total variation is at
  most `2(1 − m_N)(1 + 1/t)`.

Letting `N → ∞` gives `μ'_r = μ_r` for every `r`, so `τ' = τ`. ∎

## 3. Branch traces

**Lemma 2.** Assume doubling form and (D). For every `m` and `x ∈ X_m` there are
`τ ∈ T(A)` and points `y_N ∈ X_N` (`N ≥ m`) with `y_m = x` and

```text
‖μ_N − δ_{y_N}‖_TV ≤ 2 Σ_{s ≥ N} (1 − α_s).
```

In particular `τ` is extreme, and `μ_m({x}) ≥ 1 − Σ_{s ≥ m} (1 − α_s)`.

*Proof.*
- Put `y_{N+1} = d_N(y_N)`. By (D),
  `ψ_N(δ_{y_{N+1}}) = α_N δ_{y_N} + (1 − α_N) ν_N(y_{N+1})`.
- For `r ≤ N` put `μ_r^{(N)} = Ψ_{r,N}(δ_{y_N})`. Then
  `‖μ_r^{(N+1)} − μ_r^{(N)}‖_TV ≤ ‖ψ_N(δ_{y_{N+1}}) − δ_{y_N}‖_TV ≤ 2(1 − α_N)`.
- The sequence is Cauchy in total variation. Its limits `μ_r` satisfy
  `ψ_r(μ_{r+1}) = μ_r`, and the stated bound holds. Below `m`, set `μ_r = Ψ_{r,m}(μ_m)`.
- Extremality follows from Lemma 1. ∎

For Toms's non-simple limit (`α ≡ 1`) this is his Lemma 2. For his simple
algebra it is Proposition 4(3).

## 4. Extreme traces are dense

**Theorem 3.** Assume doubling form, (D) and (F). Then `∂_e T(A)` is dense in
`T(A)`.

Suppose also that some `X_i` has two points. Then `T(A)` is not a point, hence
infinite-dimensional. By Lindenstrauss–Olsen–Sternfeld (Ann. Inst. Fourier 28,
1978) it is the Poulsen simplex. In particular `∂_e T(A)` is not closed, and
`T(A)` is not Bauer.

*Proof.*

**Step 1: reduce to one stage.** A weak* neighbourhood of `τ` is given by finitely
many `a` from some `A_m` and an `ε > 0`. Choose `m' ≥ m` with
`Σ_{s ≥ m'} (1 − α_s) < ε`, and view each `a` in `A_{m'}`. Then `σ(a) = ∫ f_a dσ_{m'}`,
where `f_a(x) = tr_x(a)` is continuous with `‖f_a‖ ≤ ‖a‖`.

**Step 2: leaf measures.** For `N > m'` let `L = W_{m'} × ··· × W_{N−1}`, and let
`λ_ℓ : X_N → X_{m'}` be the composite of the `λ_{s,w_s}`.
- Inducting on `N`:
  `Ψ_{m',N}(δ_y) = β |L|^{-1} Σ_ℓ δ_{λ_ℓ(y)} + (1 − β) ν`,
  with `β = Π_{s=m'}^{N−1} α_s ≥ 1 − Σ_{s ≥ m'} (1 − α_s)` and `ν` a probability
  measure.
- The joint map `(λ_ℓ)_ℓ : X_N → X_{m'}^L` is a composite of products of the
  surjections `Λ_s`, so by (F) it is surjective.

**Step 3: choose labels.** Uniform empirical measures on `|L| ≥ 2^{N−m'}` points
are weak* dense in `Prob(X_{m'})` as `N → ∞`:
- partition `X_{m'}` into finitely many small cells;
- round each cell's mass down to a multiple of `1/|L|`;
- put the leftover mass, at most `#cells/|L|`, on one point.

So choose `N` and labels `z ∈ X_{m'}^L` with `|∫ f_a d(|L|^{-1} Σ_ℓ δ_{z_ℓ}) − τ(a)| < ε`
for the finitely many `a`. Pick `y ∈ X_N` with `λ_ℓ(y) = z_ℓ`, and let `σ` be the
branch trace of Lemma 2 started at `y` at stage `N`. Then

```text
‖σ_{m'} − |L|^{-1} Σ_ℓ δ_{z_ℓ}‖_TV ≤ ‖Ψ_{m',N}(σ_N − δ_y)‖_TV + 2(1 − β) ≤ 4 Σ_{s ≥ m'} (1 − α_s) < 4ε,
```

so `|σ(a) − τ(a)| < (4‖a‖ + 1) ε`. Since `σ` is extreme, this proves density.

**Two points.** If `X_i` has two points, then by (F) so does every later `X_s`.
Take `m'` with `Σ_{s ≥ m'} (1 − α_s) < 1/4` and `x ≠ x'` in `X_{m'}`. Their branch
traces satisfy `μ_x({x}) ≥ 3/4 > 1/4 ≥ μ_{x'}({x})`, so they differ. A
finite-dimensional simplex with dense extreme points is a single point. ∎

## 5. Toms's algebras

Source: arXiv:2606.12188v2. The text on MSI at
`/projects/standard/hsiehph/sauer354/lit/toms-winter/2606.12188.txt` was read at
lines 331–441, 1001–1050 and 1171–1300.

**5.1 The non-simple limit (Section 4).**
- `X_1 = Gr(d,2d)` and `X_{i+1} = X_i × X_i × CP^{j_i}`.
- `φ_i(a) = (π_1* a ⊗ γ_{i,1}) ⊕ (π_2* a ⊗ γ_{i,2})`, where the `γ_{i,r}` are line
  bundles pulled back from `CP^{j_i}`.
- At `y = (x', x'', ℓ)` the two summands have rank `r_i` and rank-one line fibres,
  so `P_i(y) = ½(δ_{x'} + δ_{x''})`.

This is doubling form with `α_i = 1`, `W_i = {1,2}`, `λ_{i,w} = π_w`. The diagonal
`d_i(x) = (x, x, ℓ_0)` gives (D), and it is Toms's Lemma 2 branch. The pair
`(π_1, π_2)` is surjective, which gives (F). So **`T(A)` is the Poulsen simplex.**

**5.2 The simple algebra B (Proposition 4).**
- `ψ_i = ψ_i^top ⊕ ψ_i^pt`. Here `ψ_i^top` is a telescoped composite of `k_i`
  doubling maps applied to the whole `s_i`-corner, and `ψ_i^pt` is a finite direct
  sum of point evaluations.
- Toms sets `α_i = rank(s^top_{i+1}) / rank(s_{i+1})`. His proof arranges
  `Σ (1 − α_i) < ∞` and `Π α_i > 1 − η`.
- A composite of `k` doubling maps is a direct sum over `w ∈ {1,2}^k` of pullbacks
  along composites of coordinate projections, each tensored with a product of
  line bundles. So the top part contributes the uniform average over the `2^k`
  leaf points.
- The point evaluations contribute a probability measure `ν_i` that does not
  depend on `y`.

So B has doubling form with `W_i = {1,2}^{k_i}`. Iterated diagonals give (D), and
composites of surjective product maps give (F). So **`T(B)` is the Poulsen
simplex.**

**Consequences.**
- The algebra of `toms-ah-counterexample-to-uniform-gamma` is not Bauer. Its
  uniform tracial completion is not a W*-bundle over a compact extreme boundary,
  so as it stands it does not answer Question 3.14.
- The branch traces Toms uses to evaluate the Thom–Porteous obstruction at an
  unknown point of the degeneracy locus are exactly the extreme traces that
  Theorem 3 shows to be dense.

## 6. Strict comparison makes equal-trace projections approximately equivalent

**Theorem 4.** Let `A` be unital, simple, separable, exact and non-elementary,
with `T(A) ≠ ∅` and strict comparison. Let `M` be its uniform tracial completion.
Suppose `P, Q ∈ M_k(M)` are projections with `τ(P) = τ(Q)` for all `τ ∈ T(A)`.
Then for every `ε > 0` there is a contraction `W ∈ M_k(M)` with `W = QWP`,
`‖W*W − P‖_{2,u} ≤ ε` and `‖WW* − Q‖_{2,u} ≤ ε`.

*Proof.*
1. **Embed the completion.** The unit ball of `M_k(A)` is `‖·‖_{2,u}`-dense in
   that of `M_k(M)`, so `M_k(M)` embeds in `M_k(A^ω)` as bounded approximating
   sequences. Take `σ = lim_ω τ_n` and representatives `a_n → P`. Then
   `σ(P) = lim_ω τ_n(a_n) = lim_ω τ_n(P)`, which equals `σ(Q)`.
2. **Subequivalence.** By `strict-comparison-compares-ultrapower-projections` there
   is `v ∈ M_k(A^ω)` with `v*v = P` and `vv* ≤ Q`.
3. **Equivalence.** `x = Q − vv*` is a projection with
   `σ(x) = σ(Q) − σ(P) = 0` for every limit trace `σ`. Choose `τ_n` nearly attaining
   the supremum in `‖x_n‖_{2,u}`. The limit trace `σ = lim_ω τ_n` then has
   `σ(x) = ‖x‖²_{2,u}`, so `x = 0` and `vv* = Q`.
4. **Back to the completion.** Lift `v` to contractions `v_n ∈ M_k(A)`. Put
   `W_n = Q v_n P ∈ M_k(M)`. In `M_k(A^ω)`, `(W_n) = QvP = v`. Hence
   `lim_ω ‖W_n* W_n − P‖_{2,u} = 0` and `lim_ω ‖W_n W_n* − Q‖_{2,u} = 0`. ∎

**Corollary 5.** Suppose `T(A)` is Bauer and `A` has strict comparison.
- The nontriviality criterion of
  `trivial-r-fibre-bundles-compare-equal-trace-projections` never applies to the
  bundle of `A`.
- Hence a C*-algebra carrying equal-trace projections that are not approximately
  equivalent fails strict comparison, for every exact building block and every
  simplex. The requirements of the task are incompatible.
- A Toms–Winter counterexample with Bauer simplex still gives a nontrivial bundle,
  through `bauer-uniform-gamma-iff-trivial-tracial-bundle` and
  `uniform-gamma-algebras-satisfy-toms-winter`. This certificate cannot detect it.
- The bundle question itself has no comparison hypothesis, so Question 3.14 stays
  open.

## 7. What a Bauer doubling system would have to give up

These are observations, not theorems.
- **(D), (F) and summable contamination cannot all be kept.** Theorem 3 uses only
  these three. Coordinate-projection doubling on full products has (D) and (F)
  whatever fixed-point structure is added. So a Hilbert-cube inverse limit with
  coordinate-projection connecting maps on full products, and summable
  contamination, is Poulsen.
- **Contamination must stay summable.** Suppose the equal-trace pair is carried
  by the top corner, as in Toms: `p_{m+1} = ψ_m^top(p_m) ≤ s^top_{m+1}`. Then
  `‖p_m‖²_{2,u} = rank(p_m)/rank(s_m) ≤ Π_{s<m} α_s · rank(p_1)/rank(s_1)`. If
  `Π α_s = 0`, the pair vanishes in the completion.
- **Correlated copies are what is left.** The joint map `Λ_i` would have to be
  non-surjective, or diagonal points would have to be absent.
  - Toms's propagation (his Section 5) extracts the next Thom–Porteous class from
    both independent copies of `X_i`. Correlating the copies is exactly where the
    obstruction and Bauerness compete.
  - For Bauer, the leaf configurations reachable from deep stages must
    accumulate only on restrictions of extreme traces.
  - This was not pursued further.
- **Strict comparison is not available in any design** (Theorem 4).

## Trust surfaces

- Sections 2–4 and 6 are elementary and self-contained. They have not been
  independently reviewed, and nothing is in Lean.
- Section 5 reads Toms's construction as stated. Two points are read off the
  construction rather than quoted from a separate statement in the paper: the
  doubling form of the telescoped top map, and the constant measure of the
  point-evaluation part. Only the top part and `Σ(1 − α_i) < ∞` enter Theorem 3.
- Downstream use needs only density and non-closedness of `∂_e T`. Neither
  depends on the uniqueness theorem for the Poulsen simplex.
- Theorem 4 rests on `strict-comparison-compares-ultrapower-projections` (reviewer
  PASS) and standard facts about uniform tracial ultrapowers: limit traces, and
  lifting contractions from a C*-quotient.

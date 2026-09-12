# A dimension-free projection invariant for hyperfinite W*-bundles (2026-09-12)

Lane `tw-hilbert-cube-bundle`, working on BBSTWW Question 3.14
(`nontrivial-w-star-bundle-with-r-fibres-exists`) over bases such as the Hilbert
cube, where the countable-dimensional triviality theorem
(`r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial`) does not apply.

This artifact proves one theorem and records one design analysis.
- **Theorem 1 (established here).** In the trivial bundle `C_σ(K,R)`, over ANY
  compact Hausdorff base `K`, two projections with the same trace function are
  approximately Murray–von Neumann equivalent in the uniform 2-norm.
- **Corollary 2 (a nontriviality criterion).** An R-fibre bundle containing
  equal-trace projections that are not approximately equivalent is not trivial,
  whatever the dimension of its base.
- **Section 3 (heuristic, not a claim).** Why Toms's Thom–Porteous mechanism
  does not directly give a Bauer witness.

Neither a witness nor a triviality proof over the Hilbert cube is obtained.

## Setting and notation

- `R` is the hyperfinite II_1 factor, with trace `τ` and `‖x‖_2 = τ(x*x)^{1/2}`.
- For a compact space `K`, `C_σ(K,R)` is the algebra of norm-bounded maps
  `x: K → R` continuous for `‖·‖_2` on `R`. It carries `E(x)(λ) = τ(x(λ))` and
  `‖x‖_{2,u} = sup_λ ‖x(λ)‖_2`.
- Finite von Neumann algebra facts used: `‖x‖_2 = ‖x*‖_2`,
  `‖xy‖_2 ≤ ‖x‖·‖y‖_2` and `‖xy‖_2 ≤ ‖x‖_2·‖y‖`. For contractions `a, b`:
  `‖a*a − b*b‖_2 ≤ 2‖a − b‖_2`.
- Norm-bounded products of `‖·‖_2`-continuous maps are `‖·‖_2`-continuous, so
  `C_σ(K,R)` is an algebra.

## 1. Theorem 1

**Theorem 1.** Let `K` be compact Hausdorff and `P, Q ∈ C_σ(K,R)` projections
with `τ(P(λ)) = τ(Q(λ))` for every `λ ∈ K`. For every `ε > 0` there is
`W ∈ C_σ(K,R)` with

```text
‖W‖ ≤ 1,   W = QWP,   ‖W*W − P‖_{2,u} ≤ ε,   ‖WW* − Q‖_{2,u} ≤ ε.
```

No dimension hypothesis on `K` is used. The proof realizes a partition of unity
of `K` by exactly central projections taken from a finite-dimensional relative
commutant, which is where Ozawa's covering-dimension argument would otherwise
enter.

**Proof.** Fix `ε_0 > 0`, to be chosen at the end.

*Step 1: local partial isometries.*
- For each `μ ∈ K`, the equal-trace projections `P(μ), Q(μ)` of the II_1 factor
  `R` are equivalent. Choose `v_μ ∈ R` with `v_μ*v_μ = P(μ)` and
  `v_μ v_μ* = Q(μ)`.
- The set `U_μ = {λ : ‖P(λ) − P(μ)‖_2 < ε_0, ‖Q(λ) − Q(μ)‖_2 < ε_0}` is open.
- By compactness choose `μ_1, …, μ_N` whose sets `U_i = U_{μ_i}` cover `K`, and
  write `v_i = v_{μ_i}`.

*Step 2: a finite-dimensional algebra carrying everything.*
- Fix an increasing sequence of finite-dimensional unital subalgebras `D_m ⊂ R`
  with `‖·‖_2`-dense union, e.g. the dyadic matrix algebras.
- The set `S = {P(λ), Q(λ) : λ ∈ K} ∪ {v_i, v_i*}` is `‖·‖_2`-compact.
- The functions `x ↦ ‖x − E_{D_m}(x)‖_2` are continuous, non-increasing in `m`,
  and tend to `0` pointwise. By Dini they tend to `0` uniformly on `S`.
- Choose `D = D_m` with `‖x − E_D(x)‖_2 < ε_0` for every `x ∈ S`.

*Step 3: central projections realizing a partition of unity.*
- `D ≅ M_n` is a unital subfactor. So `R ≅ D ⊗ (D' ∩ R)`, and by uniqueness of
  the trace, `τ(yz) = τ(y)τ(z)` for `y ∈ D` and `z ∈ D' ∩ R`.
- Choose a self-adjoint `h ∈ D' ∩ R` whose spectral distribution under `τ` is
  Lebesgue measure on `[0,1]`. It exists because `D' ∩ R` is a II_1 factor, so it
  contains a diffuse abelian subalgebra.
- Let `f_1, …, f_N` be a continuous partition of unity with `supp f_i ⊂ U_i`.
  Put `s_0 = 0` and `s_i = f_1 + … + f_i`, so `s_N = 1`.
- Define `p_i(λ) = χ_{[s_{i−1}(λ), s_i(λ))}(h)` for `i < N`, and
  `p_N(λ) = χ_{[s_{N−1}(λ), 1]}(h)`.
- Then the `p_i(λ)` are pairwise orthogonal projections in `D' ∩ R` with
  `Σ_i p_i(λ) = 1` and `τ(p_i(λ)) = f_i(λ)`.
- **Continuity.** `‖p_i(λ) − p_i(λ')‖_2²` is the Lebesgue measure of the
  symmetric difference of two intervals, at most
  `|s_{i−1}(λ) − s_{i−1}(λ')| + |s_i(λ) − s_i(λ')|`. So `p_i ∈ C_σ(K,R)`.
- **Product rule.** For `y ∈ D`: `τ(p_i(λ) y) = f_i(λ) τ(y)`.

*Step 4: gluing.*
- Put `P̃ = E_D(P)` and `Q̃ = E_D(Q)`. These lie in `C_σ(K,R)`, since `E_D` is
  `‖·‖_2`-contractive. Put `ṽ_i = E_D(v_i) ∈ D`, a constant section.
- Put `Z = Σ_i p_i ṽ_i ∈ C_σ(K,R)`. Since the `p_i` are orthogonal and commute
  with `D`:
  ```text
  Z*Z = Σ_i p_i ṽ_i*ṽ_i,        ZZ* = Σ_i p_i ṽ_i ṽ_i*.
  ```
  In particular `Z*Z ≤ Σ_i p_i = 1`, so `‖Z‖ ≤ 1`.
- By orthogonality, commutation and the product rule, for every `λ`:
  ```text
  ‖Z*Z − P̃‖_{2,λ}² = Σ_i τ(p_i(λ) |ṽ_i*ṽ_i − P̃(λ)|²)
                    = Σ_i f_i(λ) ‖ṽ_i*ṽ_i − P̃(λ)‖_2².
  ```
- If `f_i(λ) > 0` then `λ ∈ U_i`, and
  ```text
  ‖ṽ_i*ṽ_i − P̃(λ)‖_2 ≤ ‖ṽ_i*ṽ_i − v_i*v_i‖_2 + ‖P(μ_i) − P(λ)‖_2 + ‖P(λ) − P̃(λ)‖_2
                     < 2ε_0 + ε_0 + ε_0 = 4ε_0.
  ```
- Hence `‖Z*Z − P̃‖_{2,u} < 4ε_0`, and likewise `‖ZZ* − Q̃‖_{2,u} < 4ε_0`.
  Therefore `‖Z*Z − P‖_{2,u} < 5ε_0` and `‖ZZ* − Q‖_{2,u} < 5ε_0`.

*Step 5: compressing into the corner.*
- Put `W = QZP`. Then `‖W‖ ≤ 1` and `W = QWP`.
- Fibrewise, `‖(1 − Q)Z‖_2² = τ((1 − Q)ZZ*) = τ((1 − Q)(ZZ* − Q)) ≤ ‖ZZ* − Q‖_2 < 5ε_0`.
- Similarly `‖Z(1 − P)‖_2² = τ((1 − P)(Z*Z − P)) < 5ε_0`.
- So `‖W − Z‖_{2,u} ≤ ‖(1 − Q)Z‖_{2,u} + ‖QZ(1 − P)‖_{2,u} ≤ 2(5ε_0)^{1/2}`.
- Therefore `‖W*W − P‖_{2,u} ≤ ‖W*W − Z*Z‖_{2,u} + ‖Z*Z − P‖_{2,u} ≤ 4(5ε_0)^{1/2} + 5ε_0`,
  and the same bound holds for `‖WW* − Q‖_{2,u}`.
- Choose `ε_0` with `4(5ε_0)^{1/2} + 5ε_0 ≤ ε`. ∎

**Remark (subequivalence).** The same argument, with `v_μ*v_μ = P(μ)` and
`v_μ v_μ* ≤ Q(μ)`, gives approximate subequivalence when
`τ(P(λ)) ≤ τ(Q(λ))` for all `λ`. Only the equal-trace case is used below.

## 2. Corollary 2: a nontriviality criterion

For projections `P, Q` in a W*-bundle `M` over `K`, put

```text
δ_M(P,Q) = inf { max(‖W*W − P‖_{2,u}, ‖WW* − Q‖_{2,u}) : W ∈ M, ‖W‖ ≤ 1, W = QWP }.
```

**Corollary 2.** Let `M` be a W*-bundle over a compact space `K` with every
fibre `R`. Suppose `M` contains projections `P, Q` with `E(P) = E(Q)` and
`δ_M(P,Q) > 0`. Then `M ≇ C_σ(K,R)`.

**Proof.** An isomorphism of continuous W*-bundles over `K` is a
`C(K)`-linear *-isomorphism intertwining the conditional expectations. So it
preserves norms, `E`, and `‖·‖_{2,u}`, and hence the number `δ(P,Q)`. In
`C_σ(K,R)`, every pair of equal-trace projections has `δ = 0` by Theorem 1. ∎

**What this adds to the graph.**
- **The invariant is dimension-free.** It detects nontriviality over any base,
  including Hilbert cubes, which is where
  `r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial` leaves the question.
- **Relation to Ozawa's Theorem 15.** Condition (ii) there (approximately
  central approximate halving projections) is the triviality criterion. A
  positive `δ` on equal-trace projections is a checkable obstruction to (ii),
  visible without testing centrality against all of `M`.
- **Relation to Toms.** Toms (arXiv:2606.12188v2, Section 6) obstructs uniform
  property Γ by exhibiting equal-trace projections in the uniform tracial
  completion that are not equivalent. For a Bauer algebra, that completion is
  the strict-closure bundle (`bauer-uniform-gamma-iff-trivial-tracial-bundle`),
  and Corollary 2 is the bundle form of the same obstruction. The "approximate"
  form suffices, because Toms pulls the implementing partial isometry back to a
  finite stage only approximately in trace.

## 3. Toms's mechanism and the Bauer requirement (analysis)

Source read on MSI: `/projects/standard/hsiehph/sauer354/lit/toms-winter/2606.12188.txt`,
Sections 1–5.

- **Toms's non-simple system (Section 4).**
  - `A = lim q_i(C(X_i) ⊗ K) q_i`, with `X_1 = Gr(d, 2d)` and `X_{i+1} = X_i × X_i × CP^{j_i}`.
  - Connecting maps `φ_i(a) = (π_1*a ⊗ γ_{i,1}) ⊕ (π_2*a ⊗ γ_{i,2})` use the two
    coordinate projections `π_1, π_2`.
  - Section 6 shows this non-simple limit already fails uniform property Γ.
    Section 7 adds point evaluations only to make it simple.
- **Its traces are averaged.**
  - A point trace of `A_{i+1}` at `(x', x'', z)` restricts to `½(τ_{x'} + τ_{x''})`
    on `A_i`. A coherent family of point traces needs `x' = x''` at every stage.
  - `T(A)` is the inverse limit of `Prob(X_i)` under the averaging maps. Whether
    its extreme boundary is closed was not determined.
  - So the non-simple system does not visibly give a W*-bundle over a compact
    set of extreme traces, and Corollary 2 cannot yet be applied to it.
- **The single-projection variant is Bauer.**
  - Use one coordinate projection `π: X_{i+1} = X_i × CP^{j_i} → X_i`, with
    `p_{i+1} = π*p_i ⊗ (γ_{i,1} ⊕ γ_{i,2})`, and similarly for `q`.
  - Then `A` is a `C(X̂)`-algebra over `X̂ = lim X_i`, an infinite-dimensional
    compactum, with UHF-type fibres. So `T(A) = Prob(X̂)` is Bauer, and the
    strict closure is an R-fibre bundle over `X̂`.
- **But the obstruction does not visibly propagate.**
  - Heuristic: Toms's propagation (Lemma 1, Step 2) extracts a leading term built
    from the classes of both copies `π_1*(q_i − p_i)` and `π_2*(q_i − p_i)`.
  - With one projection both copies coincide. The leading term then involves the
    square of `∆_{d_i}(c(q_i − p_i))`. That class is top-degree on `X_1`
    (`2d² = dim Gr(d,2d)`), so its square vanishes.
  - This heuristic was not checked against Toms's full Step 2 factorization.
  - It matches Villadsen's reason for doubling: products of top classes survive
    only when pulled back from independent factors.
- **Design target left open.** A witness in the Toms style needs:
  1. equal-trace projections `P, Q` in an R-fibre bundle over a compact base;
  2. a finite-stage bundle-map obstruction propagated through independent copies of
     the old base (doubling);
  3. extreme traces forming a closed set, so the completion is a bundle over them.

  Doubling averages point traces, and averaging destroys closedness of extreme
  traces in the obvious presentation. The obstruction and Bauerness pull in
  opposite directions.

## Trust surfaces and novelty

- Theorem 1 is elementary and self-contained. It has not been independently
  reviewed, and nothing is in Lean.
- The partition-of-unity step (Step 3) is the same device as the CPoU-type
  arguments of Castillejos–Evington–Tikuisis–White–Winter, specialized to the
  trivial bundle. Novelty is not claimed for Theorem 1 itself. The contribution is
  its dimension-free statement as a bundle invariant, and its use as a witness
  criterion for Question 3.14.
- Section 3 is analysis, not a theorem. Toms's Section 6 and Lemma 1 Step 2 were
  read only in part.

---
rg: 2
id: local-mf-stability-splits-into-gap-and-paths-proof
kind: route
title: Split rounding by the intermediate value theorem along paths, compare exact representations of a Kazhdan cover by a Schur intertwiner, and let the finite sets of small irreducibles of the covers decrease to the irreducibles of a quotientless kernel
target: local-mf-stability-splits-into-rounding-gap-and-path-connection
requires:
  - fpbs-shalom-property-t-is-open
  - finitely-generated-linear-groups-are-residually-finite
  - finite-image-exact-kazhdan-torus-models-reduce-to-stage-lifts
artifacts:
  - research/local-mf-stability-splits-into-rounding-gap-and-path-connection.md
  - research/locally-mf-stable-kazhdan-kernels-collapse-torus-radicals.md
---

The notation is that of the target claim. Norms are operator norms. For `b, b' ∈ U(n)^S` put
`‖b − b'‖ = max_s ‖b(s) − b'(s)‖`.

Imports, used verbatim:
- `fpbs-shalom-property-t-is-open`: "Let `F` be a free group on a finite set `X` and `N` a normal
  subgroup of `F` with `F/N` Kazhdan. Then some finite `S` in `N` has `F/<<S>>` Kazhdan." It is used
  only to fix `R_0` and `κ`, as in `finite-image-exact-kazhdan-torus-models-reduce-to-stage-lifts`.
- `finitely-generated-linear-groups-are-residually-finite`: "Let `k` be a field and
  `Gamma <= GL_n(k)` finitely generated. Then `Gamma` is residually finite."
- Kazhdan constant, definition: `κ` is a Kazhdan constant of `P_(R_0)` for `S` if every unitary
  representation `π` of `P_(R_0)` with a unit vector `v` and `max_s ‖π(s)v − v‖ < κ` has a nonzero
  invariant vector.
- Remark W only (not used by Theorems S, H, E): Dadarlat, arXiv:2007.12655v2, Lemma 3.18: "Let
  `π : G -> U(H)` be a unitary representation for which there is a sequence `(p_n)_n` of nonzero finite
  dimensional projections such that `lim_n ‖[π(s), p_n]‖ = 0` for all `s ∈ G`. Then the trivial
  representation `ι_G` is weakly contained `π ⊗ π̄`."

## Step 0. Two elementary estimates

1. `dist_R` is 1-Lipschitz for `‖·‖` on `U(n)^S`, since it is a minimum of 1-Lipschitz functions.
2. For a word `r` of length `L` and `b, b' ∈ U(n)^S`, `‖r(b) − r(b')‖ ≤ L ‖b − b'‖`. This is the usual
   telescoping over the letters of `r`, since all factors are unitary.

## Step 1. Theorem S

**(LS_R) ⇒ (Gap_R,θ).** This is immediate.

**(LS_R) ⇒ (Conn_R).** Let `b_i` be an asymptotic K-representation. (LS_R) gives `c_i ∈ Hom_(n_i)(P_R)`
with `ε_i = ‖b_i − c_i‖ -> 0`.
1. Take `i` with `ε_i < 1`. For each `s`, `u_s = c_i(s)* b_i(s)` is unitary with `‖u_s − 1‖ = ε_i`.
   Each eigenvalue `e^(iα)` of `u_s`, with `|α| ≤ π`, has `2|sin(α/2)| ≤ ε_i`. Hence `|α| ≤ π ε_i / 2`.
2. Let `H_s` be the skew-Hermitian principal logarithm of `u_s`, so `‖H_s‖ ≤ π ε_i / 2`. Put
   `γ_i(t)(s) = c_i(s) exp(t H_s)`. Then `γ_i(0) = c_i`, `γ_i(1) = b_i`, and
   `‖γ_i(t) − b_i‖ ≤ ‖(1 − t) H_s‖ ≤ π ε_i / 2`.
3. By Step 0.2, `sup_t ‖r(γ_i(t)) − 1‖ ≤ ‖r(b_i) − 1‖ + |r| π ε_i / 2 -> 0` for every `r ∈ N`.
4. For the finitely many `i` with `ε_i ≥ 1`, use any path from `c_i` to `b_i`. Finitely many indices
   do not affect limits. So `γ_i` is a uniform K-path family, as required.

**(Gap_R,θ) and (Conn_R) ⇒ (LS_R).**
1. Let `b_i` be an asymptotic K-representation, and suppose `dist_R(b_i)` does not tend to `0`. Then
   there are `ε ∈ (0, θ]` and an infinite set `I` with `dist_R(b_i) ≥ ε` for `i ∈ I`.
2. Take `γ_i` from (Conn_R). The function `f_i(t) = dist_R(γ_i(t))` is continuous by Step 0.1, with
   `f_i(0) = 0` and `f_i(1) ≥ ε` for `i ∈ I`. By the intermediate value theorem there is `t_i` with
   `f_i(t_i) = ε`.
3. The sequence `a_i = γ_i(t_i)`, for `i ∈ I`, is an asymptotic K-representation, because the family is
   uniform. It has `dist_R(a_i) = ε ≤ θ` for all `i ∈ I`, and this does not tend to `0`. That
   contradicts (Gap_R,θ).

This proves Theorem S. The last sentence of Theorem S follows, since (LS_R) does not mention `θ`.

## Step 2. Lemma R

1. Every representation of `P_R` with `R ⊇ R_0` is a representation of `P_(R_0)`, with the same invariant
   vectors. So `κ` is a Kazhdan constant of every such `P_R` for `S`.
2. Let `σ ∈ Supp c` act on `W`, and let `V : W -> C^n` be an isometry with `c(g) V = V σ(g)`.
3. The finite-dimensional space `Hom(W, C^n)`, with the Hilbert--Schmidt inner product, carries the
   unitary representation `π(g) Y = c'(g) Y σ(g)^-1` of `P_R`. For `s ∈ S`,

   ```text
   ‖π(s) V − V‖_HS = ‖c'(s) V − V σ(s)‖_HS = ‖(c'(s) − c(s)) V‖_HS ≤ ‖c'(s) − c(s)‖ ‖V‖_HS,
   ```

   and this is `< κ ‖V‖_HS`.
4. By step 1, `π` has a nonzero invariant vector `Y`, so `c'(g) Y = Y σ(g)` for all `g`. The kernel of `Y`
   is `σ`-invariant, and it is not all of `W`, so by irreducibility it is `0`. Hence `Y` embeds `σ`
   into `c'`, and `σ ∈ Supp c'`.
5. By symmetry `Supp c' ⊆ Supp c`.

## Step 3. Theorem H

1. **Claim: `sup_t dist_R(γ_i(t)) -> 0`.** If not, there are `ε ∈ (0, θ]` and an infinite set `I` with
   `sup_t dist_R(γ_i(t)) > ε` for `i ∈ I`. Since `dist_R(γ_i(0)) = 0`, the intermediate value theorem
   gives `t_i` with `dist_R(γ_i(t_i)) = ε`. As in Step 1, the sequence `(γ_i(t_i))_(i ∈ I)` is an
   asymptotic K-representation with `dist_R ≡ ε ≤ θ`. This contradicts (Gap_R,θ).
2. Fix `i` with `sup_t dist_R(γ_i(t)) < κ/4`. By uniform continuity on `[0,1]`, choose
   `0 = t_0 < t_1 < ... < t_m = 1` with `‖γ_i(t_k) − γ_i(t_(k+1))‖ < κ/4`.
3. Choose `e_k ∈ Hom_(n_i)(P_R)` with `‖γ_i(t_k) − e_k‖ < κ/4`. Take `e_0 = γ_i(0)` and `e_m = γ_i(1)`,
   which is allowed because they are exact.
4. Then `‖e_k − e_(k+1)‖ < 3κ/4 < κ`, so `Supp e_k = Supp e_(k+1)` by Lemma R. Chaining gives
   `Supp γ_i(0) = Supp γ_i(1)`.

The test (T-Gap) is the contrapositive.

## Step 4. Theorem E

**Part 1 (uniform finiteness).**
1. Let `σ, σ'` be inequivalent irreducible `d`-dimensional representations of `P_(R_j)`, and `u ∈ U(d)`.
2. If `‖σ − u σ' u*‖ < κ`, then by Lemma R, `σ ∈ Supp(u σ' u*)`. Since `u σ' u*` is irreducible, this
   gives `σ ≅ σ'`, a contradiction.
3. So any choice of one representative per class gives a `κ`-separated subset of the compact metric
   space `(U(d)^S, ‖·‖)`. Its size is at most the `κ/2`-packing number `N(d, κ, |S|)` of that space,
   which does not depend on `j`.

**Part 2 (escape).**
1. `P_(R_(j+1))` is a quotient of `P_(R_j)`, and inflation is injective on classes. So the finite sets
   `Irr_d(P_(R_j))` decrease in `j`. They are therefore eventually constant, equal to a set `I_d`.
2. Each `σ ∈ I_d` kills `R_j` for every `j`, hence kills `N = ∪_j R_j`, hence factors through `K`.
3. `σ(K) ≤ U(d)` is a finitely generated linear group. By the imported Mal'cev theorem it is residually
   finite. If `σ(K) ≠ 1`, a nontrivial finite quotient of `σ(K)` is a nontrivial finite quotient of `K`,
   contradicting (Q). So `σ(K) = 1`. Since `σ` is irreducible, `d = 1` and `σ` is trivial.
4. For each `d ≤ D` let `j_d` be a stage from which `Irr_d(P_(R_j)) = I_d`. Put `j(D) = max_(d ≤ D) j_d`.

## Step 5. Corollaries E1 and E2

**E1.**
1. Given `D`, take `n` so large that `R_(j(D))` holds in `F_n`. Then `θ_n` extends to a homomorphism
   `P_(R_(j(D))) -> F_n`, which is onto because `θ_n(S)` generates `F_n`.
2. A nontrivial irreducible representation of `F_n` pulls back to a nontrivial irreducible
   representation of `P_(R_(j(D)))` of the same dimension. By Theorem E its dimension is `> D`.
3. If `H < F_n` has index `m` with `2 ≤ m ≤ D + 1`, then `ℓ^2(F_n / H)` minus the constants is a
   nonzero representation of dimension `m − 1 ≤ D` without invariant vectors. It contains a nontrivial
   irreducible representation of dimension `≤ D`, which contradicts step 2.
4. A nontrivial abelianization gives a nontrivial `1`-dimensional representation, so `F_n` is perfect
   (take `D = 1`).

**E2.**
1. Fix `D` and put `R' = R ∪ R_(j(D))`. By (LS) for `R'` there are `c'_i ∈ Hom_(n_i)(P_(R'))` with
   `‖b_i − c'_i‖ -> 0`. So `‖c_i − c'_i‖ < κ` for large `i`.
2. Both are exact representations of `P_R`, since `R ⊆ R'`. By Lemma R, `Supp c_i = Supp c'_i` as
   `P_R`-representations.
3. Every member of `Supp c'_i` is an irreducible representation of `P_(R')`, which is a quotient of
   `P_(R_(j(D)))`. By Theorem E it is trivial or has dimension `> D`.
4. A fixed nontrivial `σ` of dimension `d` is excluded once `D = d`. The disjoint subsequence is chosen
   inductively: each finite set `Supp c_(i_k) ∖ {1}` is avoided by all large `i`.

## Step 6. Remark W

Let `K` be Kazhdan without nontrivial finite quotients. Suppose `ψ_n : C*(K) -> M_(k_n)` are unital
completely positive maps with `‖ψ_n(xy) − ψ_n(x) ψ_n(y)‖ -> 0` for all `x, y`, and
`‖ψ_n(u_s) − 1‖ ≥ η > 0` for some `s ∈ S` and infinitely many `n`. We derive a contradiction.

1. **Kazhdan projection.** Every unitary representation of `K` is one of `P_(R_0)`, so `κ` works for
   `K`. Put `h = (1/2)(1 + (1/|S|) Σ_(s ∈ S) u_s)`, which is self-adjoint because `S` is symmetric.
   Let `π` have no invariant vectors and let `v` be a unit vector. Some `s` has `‖π(s)v − v‖ ≥ κ`, so
   `Re <π(s)v, v> ≤ 1 − κ^2/2`. Hence `<π(h)v, v> ≤ 1 − δ` with `δ = κ^2/(4|S|)`, and
   `σ(π(h)) ⊆ [0, 1 − δ]`. On invariant vectors `π(h) = 1`. Therefore `σ(h) ⊆ [0, 1 − δ] ∪ {1}` in
   `C*(K)`, and `f = χ_{1}(h)` is a projection in `C*(K)`. For every `π`, `π(f)` is the projection onto
   `ker(π(h) − 1)`. By strict convexity, that kernel is the space of invariant vectors.
2. **Stinespring.** Write `ψ_n = V_n* π_n(·) V_n` with `V_n` an isometry. Put `π = ⊕_n π_n` on `H`, and
   let `p_n = V_n V_n*` sit in the `n`-th summand, a nonzero projection of rank `k_n`. For `g ∈ S`,
   `‖(1 − p_n) π(g) p_n‖^2 = ‖ψ_n(u_g* u_g) − ψ_n(u_g)* ψ_n(u_g)‖ -> 0`, and the same holds with `g`
   replaced by `g^-1`. Since `S` is symmetric, `‖[π(g), p_n]‖ -> 0` for `g ∈ S`, hence for all `g ∈ K`.
   Because `f` is a norm limit of group-algebra elements, `‖[e, p_n]‖ -> 0` for `e = π(f)`.
3. **The mass sits off the invariant part.** `e` commutes with `π(K)` and `e (π(s) − 1) = 0`. Hence
   `π(s) − 1 = (1 − e)(π(s) − 1)(1 − e)`. So, for the infinitely many `n` in the hypothesis,
   `η ≤ ‖ψ_n(u_s) − 1‖ = ‖p_n (1 − e)(π(s) − 1)(1 − e) p_n‖ ≤ 2 ‖(1 − e) p_n‖^2`.
4. **Almost invariant projections for `ρ`.** Let `ρ = π` restricted to `H' = (1 − e)H`. Then `ρ` has no
   invariant vectors. Put `x_n = (1 − e) p_n (1 − e)`, a positive finite-rank operator on `H'` with
   `‖x_n‖ = ‖(1 − e)p_n‖^2 ≥ η/2` along the subsequence. We have `‖x_n^2 − x_n‖ ≤ 2‖[e, p_n]‖ -> 0` and
   `‖[ρ(g), x_n]‖ ≤ ‖[π(g), p_n]‖ -> 0`. So `σ(x_n)` lies within `ε_n -> 0` of `{0, 1}`. For large `n`
   in the subsequence, `q_n = χ_[1/2, 1](x_n)` is a nonzero finite-rank projection with
   `‖q_n − x_n‖ ≤ ε_n`. Hence `‖[ρ(g), q_n]‖ ≤ 2 ε_n + ‖[ρ(g), x_n]‖ -> 0`.
5. **Lemma 3.18 and (T).** By the imported Lemma 3.18, `ι` is weakly contained in `ρ ⊗ ρ̄`. So there are
   unit vectors `w` with `max_s ‖(ρ ⊗ ρ̄)(s) w − w‖ < κ`. By the Kazhdan constant definition, `ρ ⊗ ρ̄` has a
   nonzero invariant vector.
6. **A finite-dimensional subrepresentation.** `ρ ⊗ ρ̄` is the representation `T ↦ ρ(g) T ρ(g)*` on the
   Hilbert--Schmidt operators on `H'`. Let `T ≠ 0` be invariant. Then `T T*` is invariant, positive,
   compact and nonzero. Any eigenspace of `T T*` for a nonzero eigenvalue is finite-dimensional,
   nonzero and `ρ`-invariant. Call the restriction `σ`.
7. **Contradiction.** `σ(K) ≤ U(d)` is finitely generated and linear. By Mal'cev it is residually finite,
   so by (Q) it is trivial. So `H'` contains a nonzero `K`-invariant vector. But `ρ` has none.

This proves Remark W. Asymptotic multiplicativity was used only on the pairs `(u_g*, u_g)` and
`(u_g, u_g*)` for `g ∈ S`.

This completes the proof of the target.

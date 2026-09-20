---
rg: 2
id: locally-mf-stable-kazhdan-kernels-collapse-torus-radicals-proof
kind: route
title: Round the kernel lifts to exact representations of a cover containing a finite presentation of the torus, repair the wrap by Theorem A, and read off a genuine finite-dimensional representation of the torus
target: locally-mf-stable-kazhdan-kernels-collapse-torus-radicals
requires:
  - finite-image-exact-kazhdan-torus-models-reduce-to-stage-lifts
  - fpbs-shalom-property-t-is-open
  - finitely-generated-linear-groups-are-residually-finite
  - lef-implies-operator-mf
  - mf-positive-controls
artifacts:
  - research/finite-image-exact-kazhdan-torus-models-proof.md
  - research/mapping-torus-mf-radical-lies-in-finite-residual.md
---

The notation is that of the target claim. Norms are operator norms.

Imports, used verbatim:
- `finite-image-exact-kazhdan-torus-models-reduce-to-stage-lifts`, Theorem A: "Let `U` be an exact
  model and `T ∈ U(n)` a unitary with `δ = max_s ‖T U(s) T* - U(w_s)‖ < κ`. Let
  `U♭ = ⊕_(σ ∈ Supp U) σ` [...]. Then: 1. `‖U♭(a)‖ = ‖U(a)‖` for every `a` in the group algebra
  `C[F]`. [...] 3. There is a unitary `V` with `V U♭(x) V* = U♭(ŵ x)` for **all** `x ∈ F`, exactly."
  An exact model is a homomorphism `U : F -> U(n)` with `U(r) = 1` for every `r ∈ R_Γ`. Theorem A is
  stated for any image.
- `fpbs-shalom-property-t-is-open`: "Let `F` be a free group on a finite set `X` and `N` a normal
  subgroup of `F` with `F/N` Kazhdan. Then some finite `S` in `N` has `F/<<S>>` Kazhdan." It is used
  only to fix `R_0, κ`, as in the target's setting.
- `finitely-generated-linear-groups-are-residually-finite`: "Let `k` be a field and
  `Gamma <= GL_n(k)` finitely generated. Then `Gamma` is residually finite."
- `lef-implies-operator-mf`: "Every countable LEF group is operator MF, in the norm-matrix-corona
  sense of `countable-group-mf-conventions`." In that sense, `g ∉ Rad_MF(G)` exactly when some
  homomorphism `G -> U(Q)` is nontrivial at `g`. Its image is MF, and conversely every MF group
  embeds in some `U(Q)`. Unitaries of `Q` lift to unitaries of `∏ M_(n_i)` by polar decomposition in
  each coordinate, so such a homomorphism is a covariant model.
- `mf-positive-controls`: "every countable residually finite group is MF".

## Step 1. G-complete sets exist and are upward closed

Let `R_K ⊆ F` be the set of all relators of `K`. The group `H = <S, t | R_K, t s t^-1 = w_s>` is `G`:
- The relators `r_s = ŵ(v_s)^-1 s` lie in `R_K`. So in `H` we have `t v_s t^-1 = ŵ(v_s) = s`. Hence
  `t^-1 s t = v_s`, and `<S>` is normal in `H`.
- The map `H -> G` is onto. It restricts to a surjection `<S>_H -> K`, which is injective because
  every relator of `K` is killed in `H`.
- The map `t -> 1 ∈ Z` shows that `H = <S>_H ⋊ <t>` with `t` of infinite order acting by `φ`.

`G` is finitely presented, so finitely many of the defining relators of `H` already present `G`. This
is B. H. Neumann's lemma, and the proof is short:
- By Tietze moves, `G = <S, t | Q>` for some finite `Q`.
- Each `q ∈ Q` is trivial in `H`, so it is a consequence of finitely many defining relators of `H`.
- Let `R_1 ⊆ R_K` be the finitely many relators from `R_K` used for all `q ∈ Q`, and put
  `G_1 = <S, t | R_1, t s t^-1 = w_s>`.
- Then `G_1 ↠ H = G`. Every `q` holds in `G_1`, so `G = <S, t | Q> ↠ G_1`. Both maps are the identity
  on generators, so `G_1 = G`.

Then `R = R_1 ∪ R_Γ` is G-complete. If `R ⊆ R' ⊆ R_K` with `R'` finite, the group
`<S, t | R', t s t^-1 = w_s>` lies between `<S, t | R, ...> = G` and `H = G`, so it is `G`.

Each `P_R` with `R ⊇ R_0` is a quotient of `K~`, marked by `S`. A unitary representation of `P_R` is a
representation of `K~` with the same invariant vectors, so `κ` is a Kazhdan constant of `P_R` for `S`.

## Step 2. Proof of Theorem D

Fix a word `x_k ∈ F` representing `k`, and read `U_i(k)` as `U_i(x_k)`. Another word changes it by
`o(1)`, because relators of `K` are trivial in `G`. For `i ∈ J`, choose `c_i ∈ Hom_(n_i)(P_R)` with
`ε_i := max_s ‖U_i(s) − c_i(s)‖ = dist_R(U_i|_S) -> 0`.

(a) **Words.** For unitaries and a word `x` of length `|x|`, telescoping gives
`‖x(U_i) − x(c_i)‖ ≤ |x| ε_i`.

(b) **Wrap defect.** `π` is a homomorphism and `t s t^-1 = w_s` in `G`. So
`η_i := max_s ‖T_i U_i(s) T_i* − w_s(U_i)‖ -> 0`. With `L = max_s |w_s|`,

```text
‖T_i c_i(s) T_i* − c_i(w_s)‖ ≤ ε_i + η_i + L ε_i  -> 0.
```

So for large `i ∈ J` it is `< κ`.

(c) **Theorem A.** `c_i` is an exact model, since `R ⊇ R_Γ`. Theorem A gives `c♭_i` of dimension
`d_i ≤ n_i` and a unitary `V_i` with `V_i c♭_i(x) V_i* = c♭_i(ŵ x)` for all `x ∈ F`, and
`‖c♭_i(a)‖ = ‖c_i(a)‖` for `a ∈ C[F]`.

(d) **A representation of `G`.** Put `ρ_i(s) = c♭_i(s)` and `ρ_i(t) = V_i`.
- For `r ∈ R`, take `a = r − 1`. Then `‖c♭_i(r) − 1‖ = ‖c_i(r) − 1‖ = 0`.
- `ρ_i(t s t^-1) = V_i c♭_i(s) V_i* = c♭_i(w_s) = ρ_i(w_s)`.

So `ρ_i` kills every defining relator of `<S, t | R, t s t^-1 = w_s>`, which is `G` by (GC).

(e) **Nontriviality.** Take `a = x_k − 1`. Then

```text
‖ρ_i(k) − 1‖ = ‖c_i(x_k) − 1‖ ≥ ‖U_i(x_k) − 1‖ − |x_k| ε_i ≥ δ − |x_k| ε_i ≥ δ/2
```

for large `i ∈ J`.

(f) **`Rad_fd(G) = Rad_fin(G)` for finitely generated `G`.**
- If a finite quotient of `G` is nontrivial at `g`, so is its regular representation.
- If `ρ(g) ≠ 1` for a finite-dimensional unitary `ρ`, then `ρ(G) ≤ GL_d(C)` is finitely generated. It
  is residually finite by Mal'cev, so a finite quotient of `ρ(G)` separates `ρ(g)` from `1`.

Hence `k ∉ Rad_fd(G) = Rad_fin(G)`. ∎

## Step 3. Corollary D1

Finite groups are LEF, and LEF groups are MF (`lef-implies-operator-mf`). So

```text
Rad_MF(G) ≤ Rad_LEF(G) ≤ Rad_fin(G) ≤ K,
```

where the last inequality holds because `G/K = Z` is residually finite.

Let `k ∈ K` with `k ∉ Rad_MF(G)`. There is a covariant model `π` with `π(k) ≠ 1`, so there are an
infinite `J` and `δ > 0` with `‖U_i(k) − 1‖ ≥ δ` on `J`. Every relator of `K` is trivial in `G`, so
`(U_i|_S)_(i ∈ J)` is a sequence as in the definition of local MF-stability. Apply that definition to
the G-complete `R` of Step 1: `dist_R(U_i|_S) -> 0` along `J`. Theorem D gives `k ∉ Rad_fin(G)`.

So `Rad_fin(G) ≤ Rad_MF(G)`, and all the radicals coincide. `Rad_fd = Rad_fin` is Step 2(f). ∎

## Step 4. Corollary D2

Let `K` be finitely generated, MF and locally MF-stable. Property (T) and the torus are not used.

(a) **A uniformly separating model.** Let `π : K -> U(Q)` be injective with lifts `b_i`, and
enumerate `K \ {1} = {g_1, g_2, ...}`. Put `δ_l = limsup_i ‖b_i(g_l) − 1‖ > 0`. For each `j` and each
`l ≤ j`, choose `i_l(j) ≥ j` with `‖b_(i_l(j))(g_l) − 1‖ ≥ δ_l/2`, and put

```text
b'_j = b_(i_1(j)) ⊕ ... ⊕ b_(i_j(j)).
```

- Every relator `r` of `K` has `‖r(b'_j) − 1‖ ≤ max_(i ≥ j) ‖r(b_i) − 1‖ -> 0`.
- `‖b'_j(g_l) − 1‖ ≥ δ_l/2` for all `j ≥ l`.

(b) **Rounding along growing covers.** Enumerate the relators `r_1, r_2, ...` of `K` and put
`R^(m) = {r_1, ..., r_m}`. By local MF-stability, `dist_(R^(m))(b'_j) -> 0` as `j -> ∞` for each `m`.
So we can choose `j(m)` and `c_m ∈ Hom(P_(R^(m)))` with `max_s ‖b'_(j(m))(s) − c_m(s)‖ < 1/m` and
`j(m) -> ∞`. Let `L_m = c_m(F)`, marked by `S`.

(c) **Convergence.** Let `x ∈ F`.
- If `x = 1` in `K`, then `x` is a product of conjugates of finitely many `r_j`. So `c_m(x) = 1` for
  all large `m`.
- If `x = g_l ≠ 1` in `K`, then `‖c_m(x) − 1‖ ≥ δ_l/2 − |x|/m > 0` for all large `m`.

So `(L_m, S) -> (K, S)` in the space of marked groups.

(d) **LEF.** Each `L_m` is a finitely generated linear group, hence residually finite by Mal'cev.
So `(L_m, S)` is a marked limit of its finite quotients. A diagonal sequence gives finite marked groups
`(E_m, S) -> (K, S)`.

For a finite set `B ⊆ K`, take the ball of radius `ρ` containing `B`. For large `m`, the words of
length `≤ 2ρ + 1` that are trivial in `E_m` are exactly those trivial in `K`. So the induced map
`B -> E_m` is injective and multiplicative on `B`. That is LEF. ∎

## Step 5. Corollary D3

- If `K` has no nontrivial finite quotient, then every homomorphism from `G` to a finite group kills
  `K`. So `K ≤ Rad_fin(G)`, and hence `Rad_fin(G) = K` by Step 3.
- Corollary D1 then gives `Rad_MF(G) = K`.
- `φ` enters only through (GC), that is, through the existence of a G-complete `R` (Step 1).

∎

## Step 6. Corollary D4

**`Rad_fin(G) = K` exactly when `K` has no nontrivial finite quotient.**
- "If" is Step 5.
- "Only if": suppose `K` has a normal subgroup of index `n ≥ 2`. The intersection `M` of the finitely
  many normal subgroups of index `n` of the finitely generated `K` is characteristic, of finite index
  and proper.
- So `G/M = (K/M) ⋊ Z` exists and is finite-by-cyclic, hence residually finite.
- Its kernel part `K/M` is nontrivial, so `Rad_fin(G) ≠ K`.
- Necessity for `Rad_MF(G) = K` is `Rad_MF ≤ Rad_fin` from Step 3.

**(SD).** Suppose `σ_R(π, k; δ) = 0` with `J_δ` infinite. Then some infinite `J ⊆ J_δ` has
`dist_R(U_i|_S) -> 0` along `J`. Theorem D gives `k ∉ Rad_fin(G) = K`, which contradicts `k ∈ K`.

**Independence of the lifts.** `dist_R` is `1`-Lipschitz for the max-norm on `U(n)^S`. Changing lifts
by a null sequence therefore changes `dist_R` by `o(1)` and `‖U_i(k) − 1‖` by `o(1)`. So `σ_R > 0`
along every `J_δ` is a property of `π`. ∎

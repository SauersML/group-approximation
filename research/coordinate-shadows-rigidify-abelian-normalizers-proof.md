---
rg: 2
id: coordinate-shadows-rigidify-abelian-normalizers-proof
kind: route
title: Brick-local maps multiply coordinate shadows by at most the number of pieces, so twisting matrices permute shadow-bounded directions
target: coordinate-shadows-rigidify-abelian-normalizers-in-nv
requires: []
---

Notation as in the target. Every step is elementary. No result is imported.

**Key estimate.** Let `Φ ∈ kV` have pieces `B_1, …, B_L`. Let `S ⊆ C^k`. Then
`|pr_J(ΦS)| <= L·|pr_J S|`.
- On `B_i`, `Φ(u_1w_1, …, u_kw_k) = (v_1w_1, …, v_kw_k)`. So `pr_J Φ(z) = f_i(pr_J z)` for
  `z ∈ B_i`, where `f_i` replaces the prefix `u_j` by `v_j` in each coordinate `j ∈ J`.
- Hence `pr_J(Φ S) = ∪_i f_i(pr_J(S ∩ B_i))`, which has at most `Σ_i |pr_J S| = L|pr_J S|` points.

With a coordinate permutation `σ` (the group `kV ⋊ Sym(k)`), the same argument gives
`|pr_{σJ}(ΦS)| <= L·|pr_J S|`.

**(S1).** The `⟨ΦgΦ^{-1}⟩`-orbit of `Φz` is `Φ(⟨g⟩z)`. Apply the key estimate. For the converse,
apply it with `Φ^{-1}`, which also has finitely many pieces.

**(S2).**
- The `⟨g^r⟩`-orbit of `z` lies in the `⟨g⟩`-orbit of `z`, so `ω_J(g^r) <= ω_J(g)`.
- Conversely, `⟨g⟩z = ∪_{0<=j<|r|} g^j(⟨g^r⟩z)`. So `ω_J(g) <= Σ_{j<|r|} L(g^j)·ω_J(g^r)`, by the key
  estimate.

**(S3).**
- If every orbit has at most `N` points, every point has period at most `N`. Then `g^{N!}`
  fixes `C^k` pointwise, so `g^{N!} = 1`.
- The converse is clear.

**(S4).** Let `B_J = {v ∈ Z^d : x^v is J-bounded}`.
- By (S1), `v ∈ B_J` iff `g^{-1}x^vg = x^{Mv}` is J-bounded, iff `Mv ∈ B_J`.
- By (S2), `B_J \ {0}` is a union of the nonzero lattice points on rational lines. So it is
  the lattice-point set of a subset `D_J ⊆ P^{d-1}(Q)`.
- `M` is invertible over `Q`, so it permutes `P^{d-1}(Q)`, and `[v] ∈ D_J` iff `[Mv] ∈ D_J`.
- Hence `M·D_J = D_J`.

**(S5).** Let `d = 2`, with `D_J` finite and nonempty.
- `M` permutes the finite set `D_J`, so `M^r` fixes a line `[w] ∈ D_J` for some `r >= 1`. Then
  `w` is a rational eigenvector of `M^r`.
- Let `Γ ≤ GL_2(Z)` be the normalizer image. It permutes `D_J`, so a subgroup `Γ_0` of finite
  index fixes a line `[w]`.
- Take `w` primitive. Complete it to a basis of `Z^2`. Then `Γ_0` is conjugate into
  `{(ε_1, b; 0, ε_2) : ε_i = ±1, b ∈ Z}`, which is virtually `Z`. So `Γ` is virtually abelian,
  hence amenable.
- A hyperbolic `A ∈ Γ` would give a hyperbolic `A^s ∈ Γ_0`, which has eigenvalue `±1`. That is
  impossible.
- So there is no Sol lattice. There is also no faithful `Z^2 ⋊ F_2` extending this `Z^2`,
  since its image would contain `F_2`.
- Stabilizing `g ↦ g × id` does not change `pr_J`-orbits for `J ⊆ {1..k}`. So the conclusion
  persists in every `nV ⊇ kV`.

**(S6).** Let `x^v` act as `g_i^{v_i}` on the `J_i`-coordinates. For `K ⊆ {1..k}`:
- `pr_K(⟨x^v⟩z)` is the image of `n ↦ (pr_{K∩J_i} g_i^{nv_i} z_{J_i})_i`.
- It is bounded iff each factor is bounded. Each factor is bounded iff `v_i = 0` or `g_i` is
  `(K∩J_i)`-bounded, using (S2) for `g_i ∈ |J_i|V`.
- Hence `B_K ⊗ Q` is the coordinate subspace `∩_{i ∈ I(K)} e_i^⊥`, where
  `I(K) = {i : g_i is not (K∩J_i)-bounded}`.
- For `K = J_i`, the index set is `I(J_i) = {i}`. It contains `i` by (S3), since `g_i` has
  infinite order. It excludes every other `i'`, since `J_i ∩ J_{i'} = ∅`, so `x_{i'}` is trivial
  there. So `B_{J_i} ⊗ Q = e_i^⊥`.

*Untwisted case.* (S4) gives `M(e_i^⊥) = e_i^⊥` over `Q`.
- It gives `M(e_i^⊥ ∩ Z^d) ⊆ e_i^⊥`, and every point of `e_i^⊥ ∩ MZ^d` has its preimage in
  `e_i^⊥`.
- `MZ^d` has finite index in `Z^d`. So `(Mv)_i = Σ_j M_{ij}v_j = 0` whenever `v_i = 0`, which
  gives `M_{ij} = 0` for `j != i`.
- Hence `M` is diagonal.

*Twisted case.* The key estimate with `σ` gives `v ∈ B_{J_i}` iff `Mv ∈ B_{σ'(J_i)}`, for a fixed
permutation `σ'`.
- So `M` maps the hyperplane `e_i^⊥` onto the coordinate subspace `B_{σ'J_i} ⊗ Q`. By dimension,
  that subspace is a coordinate hyperplane `e_{π(i)}^⊥`.
- `M` is injective, so `π` is a permutation. Each coordinate line is the intersection of
  `d - 1` coordinate hyperplanes, so `M` maps coordinate lines to coordinate lines.
- Hence `M` is monomial.

*Conjugates and stabilization.* If `Z' = ΦZΦ^{-1}` and `g'` realizes `M` on the basis
`Φx_iΦ^{-1}`, then `Φ^{-1}g'Φ` realizes `M` on `Z`. Stabilization keeps the blocks `J_i` and
makes `x_i` trivial on the new coordinates.

*Normalizer image.* A diagonal `M ∈ GL_d(Z)` lies in `{±1}^d`, and a monomial one is a signed
permutation. ∎

**Heisenberg remark.** Take `H = ⟨a, b⟩` with central `c = [a,b]`. Conjugation by `a` acts on
`⟨b, c⟩` by the unipotent `(1, 0; 1, 1)`, which is not diagonal. So `⟨b, c⟩` is never conjugate to
a block-split `Z^2` in `nV`.

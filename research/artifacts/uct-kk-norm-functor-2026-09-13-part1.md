# The KK norm functor, part 1: equivariant tensor powers of Kasparov cycles

Lane ex2-uct-norm-functor, 2026-09-13.  Unreviewed.  Target claim:
`kk-tensor-power-norm-functor-to-kk-zp`.

Notation: `p` prime, `G = Z/p = <σ>`, all algebras separable, `⊗` the minimal
(spatial) tensor product, `N(A) = (A^(⊗p), σ)` with `σ` the cyclic shift.
`KK = KK_0`.  Cycles are even: `(E, φ, F)` with `E` a countably generated
graded Hilbert `B`-module, `φ : A → L(E)` even, `F` odd, `F = F*`, and
`[F, φ(a)]`, `φ(a)(F^2 − 1) ∈ K(E)` for all `a`.  `KK(A, B)` is the set of
homotopy classes (Kasparov): two cycles are equal in `KK` iff they are
homotopic, i.e. restrictions of one cycle over `B ⊗ C[0,1]`, up to unitary
equivalence at the endpoints.  Degenerate cycles are homotopic to `0`.

## 1. The module and the operators

Let `x = (E, φ, F)`.  Put `Ẽ = E^(⊗̂p)`, the exterior graded tensor product, a
Hilbert `B^(⊗p)`-module, with `φ̃ = φ^(⊗̂p)`.  The shift acts on elementary
tensors of homogeneous vectors by the Koszul rule
`σ(ξ_1 ⊗ ⋯ ⊗ ξ_p) = (−1)^(|ξ_p|(|ξ_1| + ⋯ + |ξ_(p−1)|)) ξ_p ⊗ ξ_1 ⊗ ⋯ ⊗ ξ_(p−1)`.
Koszul signs define an honest action of `S_p` on `Ẽ`, so `σ^p = 1`.  It is
compatible with `φ̃` and the shift on `A^(⊗p)`, and with the shift on
`B^(⊗p)`.  So `(Ẽ, φ̃)` is a `G`-equivariant correspondence
`N(A) → N(B)`.

Let `F_i` be `F` acting in slot `i` (graded, so `F_i F_j = −F_j F_i` for
`i ≠ j`).  Then `σ F_i σ^(−1) = F_(i+1)` (indices mod `p`).  Let
`J_i ⊆ L(Ẽ)` be the closed span of operators compact in slot `i`, that is
`L(E) ⊗̂ ⋯ ⊗̂ K(E) ⊗̂ ⋯ ⊗̂ L(E)`.  Then `J_1 ⋯ J_p ⊆ K(Ẽ)`, and
`σ J_i σ^(−1) = J_(i+1)`.

## 2. Kasparov partitions of unity

**Definition.**  Let `Δ ⊆ L(Ẽ)` be a separable subspace.  A *`Δ`-partition*
is a tuple `(M_1, …, M_p)` of even operators with

1. `0 ≤ M_i ≤ 1` and `M_1 + ⋯ + M_p = 1`;
2. `M_i · J'_i ⊆ K(Ẽ)`, where `J'_i` is the separable subspace of `J_i`
   spanned by `φ̃(A^(⊗p)) (F_i^2 − 1) φ̃(A^(⊗p))`, `φ̃(A^(⊗p)) [F_i, φ̃(A^(⊗p))]`,
   and their adjoints;
3. `[M_i, d] ∈ K(Ẽ)` for all `d ∈ Δ`.

**Existence.**  For `p = 2` this is Kasparov's technical theorem in the form
used for the external product (Blackadar, *K-theory for operator algebras*,
§18.9; Kasparov 1980).  For general `p` it follows by induction on the number
of slots: apply the two-slot theorem to `Ẽ = E^(⊗̂(p−1)) ⊗̂ E`, with the
partition already built on the first factor tensored with `1`.  Standard
input, not re-read from the source for `p > 2`.

**Averaging lemma.**  If `Δ` is `σ`-invariant and `(M_i)` is a `Δ`-partition,
then `M'_i := p^(−1) Σ_(k=0)^(p−1) σ^k M_(i−k) σ^(−k)` is a `Δ`-partition with
`σ M'_i σ^(−1) = M'_(i+1)`.

*Proof.*  Condition 1 is convex and is preserved:
`Σ_i M'_i = p^(−1) Σ_k σ^k (Σ_i M_(i−k)) σ^(−k) = 1`.  Condition 2 is linear
in `M_i`, and `σ^k J'_(i−k) σ^(−k) = J'_i` because `σ` permutes slots and fixes
`φ̃(A^(⊗p))` as a set.  So
`M'_i J'_i = p^(−1) Σ_k σ^k (M_(i−k) J'_(i−k)) σ^(−k) ⊆ K(Ẽ)`, since `σ`
normalizes `K(Ẽ)`.  Condition 3 is linear in `M_i`, and `Δ` is `σ`-invariant.
The shift relation is by reindexing.  ∎

Only the partition is averaged, never the operator.  The cycle condition
`F^2 − 1 ∈ K` is not convex, so averaging operators would not work.

## 3. The norm of a cycle

**Proposition 1.**  Let `(M_i)` be a `σ`-equivariant `Δ`-partition, where `Δ`
contains `φ̃(A^(⊗p))`, all `F_j`, and all `σ^k`-conjugates of these.  Put
`F̃ := Σ_i M_i^(1/2) F_i`.  Then `N(x) := (Ẽ, φ̃, F̃)` is a `G`-equivariant
Kasparov cycle for `(N(A), N(B))`, and `σ F̃ σ^(−1) = F̃` exactly.

*Proof.*  Invariance: `σ F̃ σ^(−1) = Σ_i M_(i+1)^(1/2) F_(i+1) = F̃`.  For the
cycle conditions, write `≡` for equality modulo `K(Ẽ)` after multiplying on
either side by `φ̃(ã)`.  By condition 3 and functional calculus, `M_i^(1/2)`
commutes with `φ̃(A^(⊗p))` and all `F_j` up to `K(Ẽ)`.

- `[F̃, φ̃(ã)] ≡ Σ_i M_i^(1/2) [F_i, φ̃(ã)] ≡ 0`, by condition 2.
- `F̃^2 ≡ Σ_(i,j) M_i^(1/2) M_j^(1/2) F_i F_j`.  The terms with `i ≠ j` cancel
  in pairs, since `F_i F_j + F_j F_i = 0` and the coefficients agree up to
  compacts.  So `φ̃(ã)(F̃^2 − 1) ≡ Σ_i M_i φ̃(ã)(F_i^2 − 1) ≡ 0`, by condition 2.
- `F̃ = F̃*` up to `K(Ẽ)`, and one may replace `F̃` by `(F̃ + F̃*)/2`, which is
  still exactly `σ`-invariant.

These are the computations of the two-slot external product, repeated for
`p` slots.  ∎

**Proposition 2 (independence and homotopy).**
1. Two equivariant `Δ`-partitions are joined by the straight-line path, which
   is an equivariant `Δ`-partition at every time.  So `N(x)` is well defined
   up to operator homotopy.
2. If `h` is a cycle for `(A, B ⊗ C[0,1])`, then `N(h)` is a cycle over
   `N(B) ⊗ C([0,1]^p)`.  Push it forward along the equivariant restriction
   `C([0,1]^p) → C[0,1]` to the diagonal.  This gives a homotopy from
   `N(h_0)` to `N(h_1)`, because restricting a partition to an endpoint gives
   a partition there.
3. A unitary equivalence `U` of cycles gives the equivariant unitary
   equivalence `U^(⊗p)`.

**Proposition 3 (zero and identity).**
1. `N` of the zero cycle is the zero cycle.
2. `N` of the identity cycle `(A_A, mult, 0)` is the identity cycle of `N(A)`,
   because `F̃ = Σ M_i^(1/2) · 0 = 0`.

## 4. Norms of contractible algebras

**Theorem A.**  If `A ≃_KK 0`, then `N(A) ≃_(KK^G) 0`.

*Proof.*  `[id_A] = 0` in `KK(A, A)`, so the identity cycle is homotopic to
the zero cycle through a cycle `h` over `A ⊗ C[0,1]`.  By Propositions 2 and
3, `N(h)` restricted to the diagonal is an equivariant homotopy from the
identity cycle of `N(A)` to the zero cycle.  So `[id_(N(A))] = 0` in
`KK^G(N(A), N(A))`.  ∎

No product compatibility is used, only the construction of §§1–3 for single
cycles and for one-parameter families.

**Corollary A (the shift on `O_2^(⊗p)` is Rokhlin).**  `N(O_2)` is
`KK^G`-contractible.  The shift on `O_2^(⊗p) ≅ O_2` is pointwise outer: a
nontrivial permutation of tensor factors of a simple, non-type-I algebra is
outer (standard, not re-read).  By `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`,
item 2, the shift has the Rokhlin property and is conjugate to the model
`id ⊗ μ_G`.  For `p = 2`: the flip on `O_2 ⊗ O_2` is Rokhlin.

*Model test.*  The trivial action on `O_2` is contractible and not Rokhlin,
so outerness is doing work.  `N(M_n)` with `M_n ≃_KK C` is `(M_(n^p), Ad U_σ)`,
inner by a `σ`-fixed unitary, `KK^G`-equivalent to `C`, and not contractible.
Theorem A is consistent with this, since `M_n` is not KK-contractible.

Continued in part 2: tensor powers of KK-equivalences, the functor, bootstrap
norms and the Tate-localized norm.

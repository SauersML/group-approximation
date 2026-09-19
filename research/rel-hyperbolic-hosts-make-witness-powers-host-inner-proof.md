---
rg: 2
id: rel-hyperbolic-hosts-make-witness-powers-host-inner-proof
kind: route
title: Drutu--Sapir finiteness makes a power of the witness automorphism host-inner, and each of the two resulting cases makes the host non-MF
target: rel-hyperbolic-hosts-make-witness-powers-host-inner
requires:
  - fa-groups-finitely-many-homs-to-rel-hyperbolic-groups
  - property-t-implies-property-fa
  - finite-outer-order-radical-witnesses-cross-alekseev-thom
  - mf-is-commensurability-invariant
  - several-ended-groups-act-fixed-point-freely-on-trees
  - lacunary-hyperbolic-witness-kernels-are-non-rf-hyperbolic
  - non-mf-tf-hyperbolic-gives-fp-full-radical-kazhdan-group
---

Notation is that of the target. `(G, K)` is a witness, `G = K ⋊_φ Z` with `φ = c_t|_K`, and
`c_x(y) = x y x^(-1)`. `H` is relatively hyperbolic under the Drutu--Sapir standing assumption, and
`ψ : K → H` is injective with `ψ(K)` not parabolic.

**Two elementary facts about MF** (operator MF, `countable-group-mf-conventions`).
- **(M1) Subgroups.** If `Γ` is MF and `Λ ≤ Γ`, then `Λ` is MF: restrict an injective
  homomorphism of `Γ` into the unitary group of the matrix corona to `Λ`.
- **(M2) Full radical.** If `Rad_MF(Λ) = Λ ≠ 1`, then `Λ` is not MF. If it were, the identity
  `Λ → Λ` would be a homomorphism to an MF group with trivial kernel, so `Rad_MF(Λ) = 1`.

`G` is not MF. The argument of (M2) applies: if `G` were MF, the identity would give
`Rad_MF(G) = 1`, but `Rad_MF(G) = K ≠ 1`.

## Step 1: a power of `φ` is host-inner

`K` is Kazhdan, so by `property-t-implies-property-fa` it is finitely generated and has property FA.

For each `n ≥ 0`, the map `ψ_n = ψ ∘ φ^n : K → H` is a homomorphism. Its image is `ψ(K)` because
`φ^n` is an automorphism of `K`, so `ψ_n` is non-parabolic. By (DS) of
`fa-groups-finitely-many-homs-to-rel-hyperbolic-groups`, the `ψ_n` fall into
finitely many `H`-conjugacy classes. So there are `0 ≤ a < b` and `g ∈ H` with
`ψ φ^b = c_g ψ φ^a`.

Put `m = b - a ≥ 1` and `h = g`. For `k ∈ K`, write `k = φ^a(k_0)`, which is possible because
`φ^a` is onto. Then

```text
ψ(φ^m(k)) = ψ(φ^b(k_0)) = h ψ(φ^a(k_0)) h^(-1) = h ψ(k) h^(-1).
```

This is (HI).

## Step 2: `h` normalizes `ψ(K)`, and all powers are controlled

By (HI), `h ψ(K) h^(-1) = ψ(φ^m(K)) = ψ(K)`. Apply (HI) to `φ^(-m)(k)` to get
`h^(-1) ψ(k) h = ψ(φ^(-m)(k))`. By induction on `|j|`,

```text
h^j ψ(k) h^(-j) = ψ(φ^(mj)(k))      for all j in Z and k in K.      (HI_j)
```

## Case A: some `h^j` with `j ≠ 0` lies in `ψ(K)`

Since `h^(-j)` then also lies in `ψ(K)`, take `j ≥ 1` and `h^j = ψ(k_0)`. By (HI_j), for every `k`,

```text
ψ(φ^(mj)(k)) = ψ(k_0) ψ(k) ψ(k_0)^(-1) = ψ(k_0 k k_0^(-1)).
```

Since `ψ` is injective, `φ^(mj) = c_(k_0)` is inner, with `mj ≥ 1`. So `[φ]` has finite order in
`Out(K)`, dividing `mj`.

By part 1 of `finite-outer-order-radical-witnesses-cross-alekseev-thom`, `G` has a finite-index
subgroup `≅ K × Z`, and `(K × Z, K)` is a witness. By part 2 of that node, `K` is nontrivial,
finitely presented, torsion-free, sofic and Kazhdan, with `Rad_MF(K) = K`.

So `K` is not MF by (M2). Then `ψ(K) ≅ K` is a non-MF subgroup of `H`, and `H` is not MF by (M1).

## Case B: no `h^j` with `j ≠ 0` lies in `ψ(K)`

Let `L = K ⋊_(φ^m) Z`, with product `(k, j)(k', j') = (k φ^(mj)(k'), j + j')`. Define
`Φ : L → H` by `Φ(k, j) = ψ(k) h^j`.

**It is a homomorphism.** By (HI_j),

```text
Φ(k, j) Φ(k', j') = ψ(k) h^j ψ(k') h^(-j) h^(j + j') = ψ(k) ψ(φ^(mj)(k')) h^(j + j')
                  = Φ(k φ^(mj)(k'), j + j').
```

**It is injective.** Suppose `ψ(k) h^j = 1`. Then `h^j = ψ(k^(-1)) ∈ ψ(K)`, so `j = 0` by the
case hypothesis. Then `ψ(k) = 1`, so `k = 1` because `ψ` is injective.

**`L` has finite index in `G`.** Let `G_m = K <t^m>`, the preimage of `mZ` under `G → G/K ≅ Z`.
It has index `m` in `G`. The map `(k, j) ↦ k t^(mj)` is an isomorphism `L → G_m`, since
`t^(mj) k' t^(-mj) = φ^(mj)(k')`, and every element of `G` is uniquely `k t^i`.

**`H` is not MF.** `G` is not MF, so `G_m` is not MF by `mf-is-commensurability-invariant`. Then
`Φ(L) ≅ G_m` is a non-MF subgroup of `H`, and `H` is not MF by (M1).

Cases A and B are complementary, which proves the theorem.

## Corollary 1: relatively hyperbolic kernels

Let `K` be relatively hyperbolic under the standing assumption, with peripheral subgroups
`K_1, ..., K_r ≠ K`. Take `H = K` and `ψ = id`.

`K` is not parabolic in itself. If `K ≤ x K_i x^(-1)`, then conjugating by `x^(-1)` gives
`K ≤ K_i`, so `K_i = K`, which is excluded.

The theorem gives (HI) with `h ∈ H = K = ψ(K)`, so Case A holds with `j = 1`. Hence `[φ]` has finite
order, the witness is virtually `(K × Z, K)`, `K` is finitely presented, and `Rad_MF(K) = K`.

**Word-hyperbolic `K`** is the case with the single peripheral subgroup `{1}` (Remark 1.13 as
imported). The standing assumption holds:
- `K` is finitely generated, being Kazhdan;
- `K` is infinite, being nontrivial and torsion-free;
- `{1} ≠ K`.

For readers who do not accept that convention, a direct check. `K` is infinite and Kazhdan, so it is
not virtually `Z`, since property (T) passes to finite-index subgroups and `Z` is not Kazhdan. So `K`
is one-ended or has infinitely many ends. By FA and Stallings (`several-ended-groups-act-fixed-point-freely-on-trees`),
`K` is one-ended. By FA again, `K` has no splitting as an HNN extension or a nontrivial amalgam, so
(L) of the imported node gives `Out(K)` finite. Then `[φ]` has finite order directly.

By part 4 of FO-AT, region (IO) requires that no nonzero power of `φ` is inner. So no witness in
(IO), and in particular none in (IO-ext), has a relatively hyperbolic kernel.

## Corollary 2: the hyperbolic-kernel equivalence

**Forward.** Let `(G, K)` be a witness with `K` word-hyperbolic. By Corollary 1 and part 2 of FO-AT,
`K` is:
- nontrivial, torsion-free and word-hyperbolic;
- Kazhdan and sofic;
- of full radical, `Rad_MF(K) = K`.

So `Q = K` satisfies `sofic-tf-hyperbolic-kazhdan-group-with-full-mf-radical`.

**Backward.** This is the argument of the route `exact-mf-radical-over-z-via-sofic-hyperbolic-kernel`,
repeated here so that this proof does not depend on that OPEN route. Let `Q` be as in the claim.
It is word-hyperbolic, hence finitely presented. By part 2 of FO-AT, `(Q × Z, Q × 0)` is a witness,
and its kernel `Q × 0 ≅ Q` is word-hyperbolic. The implication is proved; its hypothesis is OPEN.

**Lacunary kernels.** By part 3 of `lacunary-hyperbolic-witness-kernels-are-non-rf-hyperbolic`, a
witness kernel quasi-isometric to a lacunary hyperbolic group is word-hyperbolic. So the forward
direction applies.

**What this closes.** The "Not claimed" converse of `non-mf-tf-hyperbolic-gives-fp-full-radical-kazhdan-group`
asked for finiteness of `Out(K)` for hyperbolic Kazhdan `K`, which was not imported. Corollary 1
supplies it through the verbatim Drutu--Sapir and Levitt imports.

## Corollary 3: hyperbolic hosts

Let `ψ : K → H` be injective with `H` word-hyperbolic.
- `H` is finitely generated.
- `H` is infinite, because it contains the infinite group `ψ(K)`.
- `ψ(K) ≠ 1`, so `ψ(K)` is not parabolic for the peripheral subgroup `{1}`.

By the theorem `H` is not MF, which settles `non-mf-hyperbolic-group`. If `H` is torsion-free, then
(H1) of `sofic-tf-hyperbolic-kazhdan-group-with-full-mf-radical` holds.

Then (a) of `non-mf-tf-hyperbolic-gives-fp-full-radical-kazhdan-group` holds, and so (T1) of its
trichotomy fails. Hence (T2) or (T3) holds:
- a witness `Q × Z` with a word-hyperbolic kernel exists; or
- some torsion-free hyperbolic Kazhdan group is not sofic (`nonsofic-hyperbolic-group`).

## Corollary 4: MF kernels

Suppose `K` is MF. Then Case A never occurs: it would give `Rad_MF(K) = K ≠ 1`, contradicting (M2).
- The theorem says that every relatively hyperbolic `H` into which `K` embeds non-parabolically is
  non-MF.
- `K` is not relatively hyperbolic, since Corollary 1 would put it in Case A.

## Rigor note

The only external inputs are the verbatim imports (DS), (L) and Remark 1.13 in
`fa-groups-finitely-many-homs-to-rel-hyperbolic-groups-citation`, together with
the established graph nodes listed in `requires`. Nothing about acylindrically hyperbolic groups is
used or claimed.

---
rg: 2
id: algebraic-t1-sets-carry-free-distal-commutator-actions
kind: claim
title: In characteristic 2 a nontrivial torsion-free element of SL_2 has no eigenvalue 1, so on every infinite Z^2-minimal F-invariant subset M of Ledrappier's square the group F ∩ SL_2(A) acts freely, each element uniformly away from the identity; the commutator subgroup moves points inside their fibres over the maximal equicontinuous factor, so M is not a proximal extension of it; no character, coset or translation is compatible with M; and algebraic T1 is equivalent to a module embedding of A^2 into C(N, F_2)
distinct_from:
  algebraic-rows-carry-rigid-free-commutants-but-never-minimality: that isolates minimality as the missing property of T1 and shows every fibre of M over its maximal equicontinuous factor is infinite; this shows F ∩ SL_2(A) acts freely on M with each element uniformly distal from the identity, that [F,F] acts freely inside every fibre, and that M is not even a proximal extension of that factor.
  minimal-system-automorphisms-fix-every-proximal-factor: that shows automorphisms of general minimal systems are trivial on proximal factors; this uses the linear structure of Ledrappier's square to force a free, fibrewise, uniformly distal action, which any algebraic T1 set must carry.
  profinite-skew-layers-collapse-into-the-equicontinuous-factor: that constrains fibre-preserving automorphisms through profinite and connected layers; this derives the dynamical constraint (freeness and uniform distality from the identity) directly from characteristic 2.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - algebraic-rows-carry-rigid-free-commutants-but-never-minimality
  - char-2-benoist-quint-needs-the-homogeneous-form
```

**ESTABLISHED (lane bh-bq2, 2026-09-19; lane proof, elementary; not independently reviewed; no priority
claimed).**

## Setting

- `A`, `X = X_L^2 = Hom(A^2, F_2)`, the actions of the shifts `u^v` and of `GL_2(A)`, and `Γ = F × Z^2` are as in
  `char-2-benoist-quint-needs-the-homogeneous-form`.
- `d` is a translation-invariant metric on the compact group `X`.
- `F ≤ GL_2(A)` is torsion-free and non-solvable, for example free of rank 2.
- `M ⊆ X` is closed, infinite, `Z^2`-minimal and `F`-invariant: the object T1 asks for.
- `π : M → K` is the maximal equicontinuous factor of `(M, Z^2)`.

## Statement

1. **No fixed points, uniformly.**
   - Every `γ ∈ F` with `det(γ − I) ≠ 0` has `δ_γ = inf_(x ∈ M, v ∈ Z^2) d(σ_v x, σ_v γx) > 0`.
   - This covers every `γ ∈ (F ∩ SL_2(A)) \ {1}`. In characteristic 2, `det(γ − I) = tr γ` on `SL_2`, and
     `tr γ = 0` forces `γ^2 = I`.
   - The shifts also act freely on `M`.
   - So `F ∩ SL_2(A) ⊇ [F, F]` acts freely on `M`, each pair `(x, γx)` is distal, and the action is free for
     every invariant measure.
2. **Commutators live in the fibres.**
   - There is a homomorphism `τ : F → K` with `π(γx) = π(x) + τ(γ)`.
   - So `[F, F]`, which is non-solvable and infinite, preserves every fibre of `π` and acts freely on it.
     Any two points of one `[F, F]`-orbit form a distal pair.
   - Hence `M` is not a proximal extension of `K`, and in particular not almost automorphic. Every fibre
     contains an infinite set of pairwise distal points.
3. **No algebraic shadow.**
   - No nonzero character of `X` is constant on `M`.
   - `{w : M + w = M}` is finite.
   - `M` is not a finite union of cosets forming one `Γ`-orbit, that is, not the support of a homogeneous
     measure.
   - Every `Γ`-ergodic `ν` on `M` has `|ν̂(a)| < 1` for all `a ≠ 0`, and a finite translation stabilizer.
4. **Module form.**
   - Let `(N, Z^2)` be a minimal system with an action of `F` by homeomorphisms commuting with `Z^2`.
   - Continuous maps `h : N → X` that are equivariant for both actions correspond, via
     `j(a)(n) = h(n)(a)`, to `F_2`-linear maps `j : A^2 → C(N, F_2)` with `j(u^v a) = j(a) ∘ σ_v` and
     `j(γ^T a) = j(a) ∘ γ`. Here `h(N)` is an infinite `Z^2`-minimal `F`-invariant set iff `j` is injective.
   - So the topological part of algebraic T1 holds for `F` iff, for some such `N`, the
     `F_2[Z^2 × F]`-module `C(N, F_2)` contains a copy of `A^2` (with `F` acting by transposes).
   - By item 1, `F ∩ SL_2(A)` then acts freely on `N`.

## Proof

**1.**
- `D = γ − I` is a continuous endomorphism of `X` commuting with `Z^2`.
- Its kernel `Fix(γ)` is dual to `A^2/(γ^T − I)A^2`. This is a finitely generated torsion module over the
  principal ideal domain `A`, because the determinant is nonzero, so it is finite.
- `D(M)` is `Z^2`-minimal, being an equivariant image of a minimal set.
  - If `0 ∈ D(M)`, then `D(M) = {0}` because `0` is `Z^2`-fixed. Then `M ⊆ Fix(γ)`, which is finite:
    impossible.
  - So `0 ∉ D(M)`, and `d(σ_v x, σ_v γx) = d(0, σ_v Dx) ≥ d(0, D(M)) > 0`, as `D(M)` is compact.
- On `SL_2(A)`, `det(γ − I) = det γ − tr γ + 1 = tr γ` in characteristic 2. If `tr γ = 0`, Cayley–Hamilton
  gives `γ^2 = tr(γ)γ − I = I`, so `γ = I` because `F` is torsion-free.
- For `v ≠ 0`, `σ_v` is multiplication by `u^v ≠ 1`, with finite fixed group dual to `A^2/(u^v − 1)A^2`. The
  intersection `M ∩ Fix(σ_v)` is closed and `Z^2`-invariant, hence empty.
- `(x, y)` is proximal iff `0` lies in the orbit closure of `y − x`.

**2.**
- Automorphisms of a minimal system preserve its equicontinuous structure relation. So `γ` induces a
  homeomorphism of `K` commuting with the dense rotation subgroup, hence with all translations, hence itself a
  translation `τ(γ)`.
- `τ` is a homomorphism into the abelian group `K`, so it kills `[F, F]`.
- For `g ≠ h` in `[F, F]`, `(gx, hx) = (y, hg^(-1)y)` with `y = gx`, which is distal by item 1.
- Points in one fibre of a proximal extension are proximal, and almost 1-1 extensions are proximal extensions.

**3.**
- *Characters.* `{a : a(·) constant on M}` is an additive subgroup stable under `s^(±1), t^(±1)`, hence an
  `A`-submodule. It is also `F^T`-stable. As `F` fixes no line, it is `0` or of full rank. Full rank would put
  `M` in a coset of a finite subgroup.
- *Translations.* `{w : M + w = M}` is a closed `Γ`-invariant subgroup, so finite or `X`, and `M ≠ X` because
  `X` has the fixed point `0`.
- *Cosets.* See item 5 of `char-2-benoist-quint-needs-the-homogeneous-form`: a coset piece would contain a
  periodic point.
- *Fourier.* `|ν̂(a)| = 1` iff `a(·)` is `ν`-almost everywhere constant. The same module argument applies with
  `supp ν = M` infinite.
- *Stabilizer.* Translations preserving `ν` preserve `supp ν = M`.

**4.**
- `h ↔ j` is the bijection between continuous maps `N → Hom(A^2, F_2)` and `F_2`-linear maps
  `A^2 → C(N, F_2)`. The two equivariance conditions translate as stated.
- *`j` injective ⇒ `h(N)` infinite.* A finite `Z^2`-minimal set is one periodic orbit, so it lies in the group
  of `nZ^2`-periodic points for some `n`. Then every nonzero `a ∈ (s^n − 1, t^n − 1)A^2` has `j(a) = 0`.
- *`h(N)` infinite ⇒ `j` injective.* If `h(N)` is infinite, `j(a) = 0` makes `a(·)` vanish on `h(N)`, so
  `a = 0` by item 3.
- A fixed point of `γ` in `N` maps to a fixed point in `h(N)`. ∎

## What a construction must supply

- An algebraic T1 set is a minimal `Z^2`-subshift with a **free** action of a non-abelian free group. Its
  commutator subgroup acts inside the equicontinuous fibres, each element uniformly distal from the identity.
- This excludes Toeplitz, substitutive and all other almost automorphic sets outright: they are proximal
  extensions of their equicontinuous factor, not merely finite-fibred.
- Single automorphisms that preserve the fibres of a factor and stay uniformly away from the identity do
  exist, for example the fibre flip of a minimal `Z/2` group extension. The difficulty is a free group of them inside an
  expansive system, realized linearly.

## Lesson for general BH

- **Characteristic 2 gives freeness for free.** A torsion-free element of `SL_2` in characteristic 2 has no
  eigenvalue 1. So a free group of algebraic automorphisms can preserve an infinite minimal set only by acting
  freely and uniformly away from the identity.
- **The commutant lives in the distal part.** The commutator subgroup is invisible to the maximal
  equicontinuous factor. So the whole free commutant must live in the part of the minimal set that is not a
  proximal extension of that factor and is distal fibre by fibre.
- **Consequence for T1.** On algebraic rows, T1 means manufacturing a free, uniformly distal, fibre-preserving
  free-group action inside an expansive minimal system. That is the deepest layer of the structure theory of
  minimal systems, not the equicontinuous one.

---
rg: 2
id: spine-epsilon-images-avoid-contractible-2-complexes
kind: claim
title: Small-fiber PL images of the Poincaré-sphere spine are never subcomplexes of contractible 2-complexes
distinct_from:
  bestvina-brady-epsilon-map-conjecture: that asserts a cell-attachment model for every small-fiber image; this asserts only that no such image lies in a contractible 2-complex, and it follows from that conjecture through `epsilon-map-conjecture-gives-spine-images-avoid-2-complexes`.
  bestvina-brady-poincare-kernel-has-geometric-dimension-three: that is the geometric dimension of the kernel H_L; this is a statement about maps out of one finite 2-complex, which implies it through `spine-epsilon-images-avoiding-2-complexes-give-gd-three`.
  whitehead-asphericity-conjecture: that is asphericity of all subcomplexes of aspherical 2-complexes; this concerns only small-fiber images of one complex, and follows from it through TF.
  contractible-2-complex-subcomplexes-have-torsion-free-pi1: that asks for torsion-free fundamental groups of all finite subcomplexes of contractible 2-complexes; this is the special case needed for images of the spine, and follows from it through `contractible-2-complex-torsion-free-gives-spine-images-avoid`.
  subcomplex-pi1-kernels-vanish-in-hyperlinear-quotients: that is an unconditional constraint on hyperlinear quotients; it settles the acyclic images here, but not those with nonzero H_1.
  acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear: that excludes L itself, with ε = 0, from contractible 2-complexes; this excludes all small-fiber perturbations of L.
artifacts:
  - research/artifacts/eilenberg-ganea-frontier-2026-09-16.md
---

**OPEN.** Let `L` be a flag triangulation of a spine of the Poincaré homology sphere, with the path
metric in which every simplex is a regular Euclidean simplex of side 1.

**Claim.** There is `ε > 0` such that no contractible 2-dimensional simplicial complex `Y` contains
a finite subcomplex `K` that is the image of a surjective PL map `g: |L| → |K|` whose point
preimages all have diameter `< ε`.

## Position

- `whitehead-asphericity-conjecture` ⇒ `contractible-2-complex-subcomplexes-have-torsion-free-pi1` ⇒
  this claim ⇒ `bestvina-brady-poincare-kernel-has-geometric-dimension-three` ⇒ the
  Eilenberg--Ganea conjecture fails.
- `bestvina-brady-epsilon-map-conjecture` together with claim A implies this claim.
- So this is a common weakening of the ε-map conjecture and Whitehead's conjecture that suffices
  for the Bestvina--Brady argument. Proofs of all four implications are in the routes and in the
  artifact, §4.

## What is proved

Write `H_1(K) = Z^m`. It is free, being `H_2(Y, K)`. Take `ε ≤ δ`, a Lebesgue number of the open
vertex-star cover.
- **Coarse lifting** (artifact §2, complete proof). There is a simplicial `λ: K' → L` with
  `λ ∘ g ≃ id`. So `I* = SL(2,5)` embeds in `π_1(K)` and is a retract of it.
- **Acyclic images are excluded** (`m = 0`). `λ_*` is a nontrivial finite quotient of `π_1(K)`,
  contradicting `subcomplex-pi1-kernels-vanish-in-hyperlinear-quotients`(b).
- **Images with m ≥ 1.** For every nontrivial `β ∈ π_1(L)`, every finite subcomplex of `Y` in which
  `g(β)` is null-homotopic kills a nonzero class of `H_1(K)`. This is the same claim, part (a).
- **Pushout.** `L ∪_λ Y' ≃ ∨^m S^2` contains `L` (artifact §5.4).

## Attempts

1. **Nitsche--Thom Theorem 1.3 on `Z / K`.**
   - The theorem would apply if `Z / K` had a covering with trivial `H_2`.
   - If `Z` kills all of `π_1(K)`, every class of `H_2(Z/K) ≅ Z^m` is spherical, by relative
     Hurewicz from null-homotopy discs, so no covering qualifies.
   - Dies for `m ≥ 1`. See artifact §6.1.
2. **Homotopy type of the pushout.**
   - `L ∪ e^2`, attached along a non-central element of `SL(2,5)`, is `≃ S^2`. So complexes
     `≃ ∨^m S^2` containing `L` exist for every `m ≥ 1`.
   - `[L, ∨^m S^2] = ∏ H^2(L; Z) = 0`, so the inclusion carries no information.
   - Dies: the homotopy data of `(L ∪_λ Y', L)` is consistent. See §6.2.
3. **Rank count for Nitsche--Thom 1.2.**
   - Any finite enlargement killing `π_1(K)` has `H_2(Z, K) ≅ Z^m`, so the exponent-sum matrix has
     kernel `Z^m`.
   - Dies for `m ≥ 1`. See §6.3.
4. **Enlarging `K` to an acyclic subcomplex.**
   - Extending `λ_*` over new cells means solving an overdetermined system over `I*` itself.
   - Part (b) of the Q claim shows the extension always fails, and existence of a finite acyclic
     enlargement inside `Y` is not known.
   - Dies: circular. See §6.4.
5. **Controlling null-homotopies.**
   - A single disc bounding some `g(β)`, whose support completes no relative cycle of `Z_2(Y, K)`,
     would finish the proof.
   - Nothing controls `Y`. For the Bestvina--Brady kernel it has infinitely many cell orbits.
   - Dies. See §6.5.
6. **Other tools.**
   - Correction 2-cells create `H_2`.
   - Gersten's criterion is silent, because `cd π_1(K) = ∞`.
   - Characteristic classes vanish, because `H^2(K; Z) = 0`.
   - L²-invariants are dead (idea I5).
   - The mapping cylinder `M_g ⊇ L` is 3-dimensional, so what remains is a relative D2-type problem.
   - See §6.6--6.8.

**Exact gap.** The case `m ≥ 1`: a small-fiber image with nonzero `H_1` inside a contractible
2-complex. See the artifact, §7.

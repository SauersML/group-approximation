---
rg: 2
id: automorphisms-of-hierarchical-rows-are-virtually-abelian
kind: claim
title: Automorphisms of a minimal row that is finite-to-one over an equicontinuous factor, or of a path fold or Busemann transplant of such a row, form a virtually finite-by-abelian group; so every rigid row built so far carries only virtually abelian time
distinct_from:
  minimal-system-automorphisms-fix-every-proximal-factor: that shows m.a.p. automorphism groups act trivially on almost automorphic and proximal-type systems; this bounds the whole automorphism group, for every group, and adds the finite-to-one hierarchical case and the fibre embedding for folds and transplants.
  attracting-boundary-factors-fix-commuting-actions: that treats rows that are finite extensions of boundary actions (finite automorphism groups); this treats rows whose rigidity comes from a Z^r fibre, which have infinite automorphism groups.
  time-lift-actors-carry-no-complexity-beyond-row-language: that bounds the word problem of a time group by the row language; this bounds its algebraic type by the row's equicontinuous structure.
---

**ESTABLISHED** (lane proof; bh-invent-12, 2026-09-18; elementary; not independently reviewed). Items that
are imported rather than proved here: DRS uniqueness of macrotile decompositions (arXiv:0910.2415 §2), the
existence of periodic flats in cocompact `Ã₂` lattices (Ballmann–Brin), and Labbé's Markov partition, each
as recorded in the required nodes.

## Setting

`Aut(Z, H)` is the group of homeomorphisms of `Z` commuting with an action of the group `H`. For a
subshift these are the invertible cellular automata commuting with `H`. A *row* is a minimal system `Z` of a
finitely generated group `Λ₂`, as in the time-lift node. A time lift over `Z` needs a homomorphism
`Φ: Λ₁ -> Aut(Z, Λ₂)`, and it is faithful only if `Φ` is injective.

**(H′) Finite-to-one over rotations.** Let `Y` be a minimal `Z^d`-system. It satisfies (H′) if there are a
factor map `ρ: Y -> K` onto a minimal rotation of a compact abelian group `K`, with
`ρ(v·y) = ρ(y) + φ(v)`, and a constant `M` such that `|ρ^(-1)(κ)| ≤ M` for a dense set of `κ ∈ K`.

## Statement

1. **One fibre sees all automorphisms.** Let `Z` be minimal, and `π: Z -> Ω` a factor map onto a proximal
   system, or onto a minimal system with a dense-basin attractor. For every `ω ∈ Ω`, restriction is an
   injective homomorphism `Aut(Z, Λ₂) -> Aut(π^(-1)(ω), Stab(ω))`.
2. **Rows finite-to-one over rotations.** If `Y` satisfies (H′), then for every finite-index `L ≤ Z^d`,
   `Aut(Y, L)` has a finite-index subgroup `A₀` that is finite-by-abelian. In particular, every finitely
   generated subgroup of `Aut(Y, L)` is virtually abelian.
3. **Hierarchical rows satisfy (H′).** Let `τ` be a Wang tile set with zoom `N` such that every `τ`-tiling
   splits uniquely into `N × N` macrotiles `S(t)`, and the tiles `t` form a `τ`-tiling again. Then every
   minimal subsystem `Y` of the tiling space satisfies (H′) with `K = Z_N^2` (the `N`-adic odometer) and
   `M = |τ|`.
4. **Instances.** The finitely generated subgroups of the following automorphism groups are virtually
   abelian:
   - (a) `Aut(Y, Z²)` for every minimal subsystem `Y` of a crossing-wire fixed-point tiling space
     (`crossing-wire-fixed-point-tile-sets-are-quantum-rigid`), or of any tiling space as in item 3;
   - (b) `Aut(Ω_U, Z²)` for Labbé's shift, which is almost automorphic over its toral rotation
     (`labbe-shift-is-a-toral-rotation-coding`);
   - (c) `Aut(Z, F_n × Z)` for the ABHT path fold `Z` of a minimal horizontally expansive fibre `X`
     satisfying (H′), as in `path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is`. This covers
     ABHT's own shift, whose fibre is a recoding of Labbé's;
   - (d) `Aut(Z, Γ)` for every minimal subsystem `Z` of a Busemann transplant `Y_Δ`
     (`busemann-transplants-give-free-sfts-on-building-lattices`) over a torsion-free cocompact `Ã₂`
     lattice in the setting of that node, with a minimal fibre `Y` satisfying (H′).

## Proof

**Item 1.**
- Every `α ∈ Aut(Z, Λ₂)` satisfies `π∘α = π`. For proximal `Ω` this is item 2 of
  `minimal-system-automorphisms-fix-every-proximal-factor`. For an attractor it is Theorem A of
  `attracting-boundary-factors-fix-commuting-actions` applied to `π` and `π∘α`.
- So `α` preserves `F = π^(-1)(ω)` and commutes there with `Stab(ω)`. Restriction is a homomorphism.
- If `α|_F = id`, then `α` has a fixed point. Its fixed set is closed, invariant and nonempty, so it is
  all of `Z` by minimality.

**Item 2.**
- **Components.** `Y` is `Z^d`-minimal and `L` has finite index. So `Y` is a finite union of clopen
  `L`-minimal sets `Y_1, …, Y_r`, permuted by `Z^d` (standard). Each `α ∈ Aut(Y, L)` maps `L`-minimal sets
  to `L`-minimal sets, so `Aut(Y, L)` permutes the `Y_i`. Let `A₀` be the kernel of this permutation action.
  It has index at most `r!`.
- **The rotation part.** Put `H = closure(φ(L))`. It has finite index in `K`, since `K` is the closure
  of `φ(Z^d)`, so it is open. `ρ(Y_i)` is `L`-minimal, hence a single coset `k_i + H`.
  - For `α ∈ A₀`, the map `y ↦ ρ(α y) − ρ(y)` is continuous and `L`-invariant on `Y_i`, because
    `ρ(α(v y)) − ρ(v y) = ρ(α y) + φ(v) − ρ(y) − φ(v)`. So it equals a constant `c_i(α) ∈ H`.
  - `α ↦ (c_1(α), …, c_r(α))` is a homomorphism `A₀ -> H^r`, whose image is abelian.
- **The kernel is finite.** Let `A₁` be the kernel. Each coset `k_i + H` is open, so it contains a point
  `κ_i` whose fibre `F_i = ρ^(-1)(κ_i) ∩ Y_i` has at most `M` points. Elements of `A₁` preserve each `F_i`.
  - Suppose `α ∈ A₁` fixes `F_i` pointwise. Then `Fix(α) ∩ Y_i` is closed, `L`-invariant and nonempty, so
    it is `Y_i`.
  - Hence `A₁ -> ∏_i Sym(F_i)` is injective, and `|A₁| ≤ (M!)^r`.
- **Conclusion.** `A₀` is finite-by-abelian. A finitely generated finite-by-abelian group is virtually
  abelian: the centralizer `C` of the finite kernel has finite index, `[C, C]` is finite and central in
  `C`, so `C` has finite index over its centre (B. H. Neumann). This passes to finite-index overgroups.

**Item 3.**
- **The odometer.** A tiling `y` has, at every level `k`, a unique decomposition into level-`k`
  macrotiles `S^k(t)`. The position of the origin inside them gives `ρ(y) ∈ Z_N^2`. This map is continuous
  and equivariant, and the odometer is minimal, so `ρ(Y) = Z_N^2`.
- **Deep points.** Call `κ` deep if the level-`k` macrotiles `Q_k` containing the origin satisfy
  `dist(0, ∂Q_k) -> ∞`. Deep points are dense: prescribe the digits `d_k` to be central positions at all
  large `k`.
- **Fibre bound.** Fix a deep `κ` and `y ∈ ρ^(-1)(κ)`. Let `t_k ∈ τ` be the tile simulated by `Q_k`. Then
  `Q_k` carries `S^k(t_k)`, and the `Q_k` exhaust `Z²`, so `(t_k)_k` determines `y`. Moreover
  `t_k = S(t_(k+1))[d_k]`, so `t_(k+1)` determines `t_k`.
  - Two points of the fibre whose sequences agree at some level agree at every lower level.
  - Take more than `|τ|` points of the fibre. Their sequences are pairwise distinct, so at some level
    they are pairwise distinct at that level. This contradicts pigeonhole.

**Item 4.**
- (a) This is items 3 and 2 with `L = Z²`. DRS fixed-point tile sets, including the crossing-wire layouts,
  have coordinates mod `N` that force the macrotile grid (DRS §2, recalled).
- (b) This is item 2 with `M = 1`: by item 5 of the Labbé node the coding map is injective off a meagre
  set of the torus.
- (c) **Setting.**
  - `Z` is minimal (ABHT).
  - Its flow layer gives a factor map `π: Z -> ∂F_n`. As an `F_n × Z` system this is proximal, since the
    `Z` factor acts trivially and `F_n ↷ ∂F_n` is proximal.
  - Take `ξ = a^(+∞)` with `a ≠ 1`. Then `Stab(ξ) = ⟨a'⟩ × Z` for the root `a'` of `a`.

  **The fibre over `ξ`.**
  - By downward determinism, siblings carry equal rows. This is the classical case of the coherence step
    of `path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid`.
  - So the rows along one geodesic line toward `ξ` identify `π^(-1)(ξ)` with `X`.
  - Under this identification `t` acts as the horizontal shift and `a'` as the vertical shift by its
    Busemann translation `ℓ ≠ 0`. So `Stab(ξ)` acts through `L = Z × ℓZ`, which has finite index.

  **Conclusion.** Item 1 embeds `Aut(Z, F_n × Z)` into `Aut(X, L)`, and item 2 applies.
- (d) **Setting.**
  - `Y_Δ` is the skew product `Ω ×_β Y` (item 1 of the transplant node). Its fibre over `c` is `Y`, with
    `Stab(c)` acting through its Busemann image.
  - Take `c` a chamber at infinity of a periodic flat `F`. Such flats exist in cocompact rank-2 lattices
    (Ballmann–Brin, recalled; also used in item 3 of the transplant node).
  - The translations of `F` fix `c`. By `chamber-fixing-building-lattice-elements-translate-horospheres`
    they map injectively to a finite-index `L ≤ Z²`.

  **The attractor.** `Ω` is minimal with a dense-basin attractor (Instance 3 of
  `attracting-boundary-factors-fix-commuting-actions`). A minimal subsystem `Z` of `Y_Δ` maps onto `Ω`,
  and its fibre over `c` is an `L`-invariant closed subset of `Y`.

  **Conclusion.** Item 1 embeds `Aut(Z, Γ)` into the automorphisms of that fibre. By minimality of `Y`,
  the fibre is `Y` itself, or a union of `L`-minimal components of `Y`, to which item 2 applies
  componentwise. `∎`

## Consequences for the master route

1. **Time lifts are capped by the fibre, not by the scaffold.** The rigid rows recorded on main are:
   - boundary rows (finite automorphism groups, `attracting-boundary-factors-fix-commuting-actions`);
   - hierarchical and rotation-coded `Z²` rows (item 4(a),(b));
   - their folds and transplants over the non-amenable, one-ended groups `F_n × Z` and `Ã₂` lattices
     (item 4(c),(d)).

   Over every one of them, a time lift carries only virtually abelian time. Rows with infinite fibres
   over a non-amenable factor do exist, but item 1 hands their automorphisms back to one `Z^r` fibre.
2. **The `Λ₁ × Z^r` fibre problem has no hierarchical solution.** An input `Λ₁` that acts on a boundary
   fibre commutes with a finite-index `L ≤ Z^r` there. If the fibre is hierarchical or a rotation coding,
   `Λ₁` is virtually abelian.
3. **The missing object.** A rigid row that can carry a non-virtually-abelian input must be a minimal
   `Z^r`-SFT that satisfies (H′) for no rotation factor. For every `M`, its maximal equicontinuous
   factor then has fibres of size greater than `M` over a nonempty open set. No rigid SFT of that kind is known. Every rigidity
   mechanism on main (compression, one-scale fixed-point certificates, rotation codings) produces tame rows.
   This matches the v6 retirement of Aut and time-lift designs, and upgrades it from m.a.p. inputs to all
   non-virtually-abelian inputs.

## Lesson for general BH

**Rigidity makes rows tame, and tame rows have abelian symmetry.**
- Every rigid row built so far comes from compression or from a hierarchy.
  - Compression rows are finite extensions of proximal boundaries, so their automorphism groups are finite.
  - Hierarchical rows are at most `|τ|`-to-one over their odometer, so their automorphism groups are
    virtually abelian.
  - Folds and transplants add a non-amenable scaffold. One fibre still sees every automorphism, so the
    scaffold adds nothing.
- So symmetry that commutes with a rigid row cannot carry a general input. The input has to sit inside the
  acting group's own points, which is the seed gate (SEED) of SYNTHESIS v6, not in the commutant of a fixed
  rigid row.

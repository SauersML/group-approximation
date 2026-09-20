---
rg: 2
id: mapping-class-ports-are-dehn-thurston-translations-not-twists
kind: claim
title: No abelian subgroup of Mod(S_g), Dehn twists included, has finitely many orbits on any infinite orbit of integral multicurves; the port must be adjoined, and the Dehn–Thurston translation lattice is a regular port on ML_Z that fixes PML pointwise, with the stabilizer condition automatic
distinct_from:
  baumslag-gersten-port-route-fails-at-the-dilation-centralizer: that kills a port on the dilation side of BS-type edges, where the element is expansive; this shows that even parabolic elements (Dehn twists) are not ports, and that the port must be a translation.
  permutational-ports-need-stabilizers-crossing-every-splitting: that says port stabilizers cannot come from a splitting; this gives, for closed MCG, a port whose stabilizer condition holds automatically, because the port acts regularly.
  closed-mcg-embeds-in-rational-projective-full-group: that is R1's host on the ray sphere PML; this host lives on the lattice ML_Z, and its translations act trivially at infinity, so R1 cannot see them.
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - cofinite-abelian-subgroups-give-relative-pbh
  - permutational-ports-need-stabilizers-crossing-every-splitting
  - closed-mcg-embeds-in-rational-projective-full-group
  - houghton-h2-is-not-fp2-over-q
```

**ESTABLISHED** (lane bh-invent-02, 2026-09-19). Lane proof, elementary given the recalled
inputs listed under Trust surface. Not reviewed. Credits for the inputs: Dehn–Thurston
coordinates (Dehn; Thurston; Penner), BLM (Birman–Lubotzky–McCarthy), Ivanov, McCarthy,
Farb–Margalit (intersection estimates), K. S. Brown (Houghton groups).

Throughout, `g ≥ 2`, `N = 6g − 6`, and `ML_Z` is the set of integral measured laminations,
i.e. multicurves with multiplicities, with `0` the empty one.

## Statement

1. **Twists are not ports.** Let `A ≤ Mod(S_g)` be abelian, and let `O ⊆ ML_Z` be the
   `Mod`-orbit of some `γ ≠ 0`. Then `A` has infinitely many orbits on `O`. The same holds on
   the rational points of `PML`, since `[γ] ↦` its primitive representative is equivariant.
   So no abelian subgroup of `Mod(S_g)` is a Houghton port for any `Mod`-orbit of multicurves.
2. **The lattice.** There is a bijection `Φ: ML_Z → Z^N` with the following property. For
   every `f ∈ Mod(S_g)`, `Φ f Φ^-1` is *piecewise affine*: a bijection of `Z^N` that agrees
   with some `x ↦ Mx + b`, `M ∈ GL_N(Z)`, on each of finitely many pieces, each piece the
   set of lattice points of a rational polyhedron.
   Write `PAff_N(Z)` for the group of all such bijections.
3. **The translation port.** Let `T ≅ Z^N` be the translations of `Z^N`, and put
   `D_g = ⟨Φ Mod(S_g) Φ^-1, T⟩ ≤ PAff_N(Z)`.
   - `D_g ↷ Z^N` is faithful by definition, and `T` acts regularly. The map `f ↦ Φ f Φ^-1` is
     injective for `g ≥ 3`; for `g = 2` its kernel is the hyperelliptic involution. So `D_g = T · Stab(0)` is an exact
     factorization, and `Stab(0) ⊇ Φ Mod(S_g) Φ^-1` when `Φ(0) = 0`.
   - `T` acts trivially at infinity: `(x + v)/|x| − x/|x| → 0`. On the sphere of rays, which
     is where `PML` and R1's host live, every translation is the identity.
   - **Stabilizer condition, automatic.** Take any action of `D_g` of general type on a
     hyperbolic space. Then `Stab(0)` has unbounded orbits
     (`permutational-ports-need-stabilizers-crossing-every-splitting`, items 1–2, since
     `T·Stab(0) = D_g`). On a tree it contains a hyperbolic element whenever it is finitely
     generated. No Higman envelope is involved, because `Mod(S_g)` is already finitely
     presented.
4. **Calibration, rank one.** `PAff_1(Z) = H_2 ⋊ ⟨x ↦ −x⟩`, where `H_2 = FSym(Z) ⋊ Z` is
   Houghton's group. It is not finitely presented (`houghton-h2-is-not-fp2-over-q`; Brown).
   So in rank one the lattice host fails exactly as `H_2` does.
5. **The bounded part is not enough.** For `N = 2`, the piecewise translations in
   `PAff_2(Z)` do not form a finitely generated group. Their germs at infinity have jumps
   at arbitrarily many rational directions. So any finiteness proof must use the linear
   parts, e.g. `GL_2(Z)`, which acts transitively on primitive directions, to move the jump
   directions.

## Proof

**Item 1.** A finite `A` has finite orbits on the infinite set `O`. An infinite abelian `A`
either contains a pseudo-Anosov or does not.

- **(a) No pseudo-Anosov.** Then `A` is reducible (Ivanov), and a finite-index `A′ ≤ A` fixes
  each component of a nonempty multicurve `σ` (BLM). Let `c` be a component.
  - `i(aδ, c) = i(δ, a^-1 c) = i(δ, c)` for `a ∈ A′`, so `i(·, c)` is constant on
    `A′`-orbits.
  - It is unbounded on `O`. Choose a curve `β` with `i(β, γ) > 0` and `i(β, c) > 0`, for
    instance a high iterate of any curve under a pseudo-Anosov. Farb–Margalit Prop. 3.4
    gives `i(T_β^k γ, c) ≥ (|k| − 2) i(β,γ) i(β,c) − i(γ,c)`, and `T_β^k γ ∈ O`.
  - So `A′`, hence `A`, has infinitely many orbits.
- **(b) With a pseudo-Anosov `φ`.** Then `A` is virtually `⟨φ⟩` (McCarthy), so it suffices to
  treat `⟨φ⟩`. Fix a curve `α`.
  - **Few points per orbit.** Along a `⟨φ⟩`-orbit, `i(φ^n δ, α)` grows like `λ^|n|`, with
    `λ > 1` the dilatation. So each orbit has `O(log L)` points with `i(·, α) ≤ L`.
  - **Many points in `O`.** Choose `β` with `i(β, γ) > 0`. The points `T_β^k γ ∈ O` satisfy
    `i(T_β^k γ, α) ≤ |k| i(β,γ) i(β,α) + i(γ,α)` (same proposition). They are pairwise
    distinct: the lower bound gives `i(T_β^k γ, γ) ≥ (|k| − 2) i(β,γ)^2 > 0` for `|k| ≥ 3`, so
    no nontrivial power of `T_β` fixes `γ` (if `T_β^k` did, so would `T_β^{3k}`). So `O` has
    at least `cL` points with `i(·, α) ≤ L`.
  - Finitely many orbits would give `O(log L)`. So there are infinitely many.
- **Dehn twists.** They fall under (a). In Dehn–Thurston coordinates for a pants
  decomposition containing `c`, `T_c` is `t_c ↦ t_c + m_c`, and every `m_i` is invariant.
- **`PML_Q`.** `Mod` preserves primitivity of integral multicurves, so orbits on `PML_Q`
  correspond to orbits on primitive elements of `ML_Z`, and the argument applies there. ∎

**Item 2.**
- **Dehn–Thurston coordinates.** Fix a pants decomposition `P` with seams. They identify
  `ML_Z` with the set of `(m_i, t_i)_{i ≤ 3g−3}` subject to:
  - `m_i ≥ 0`;
  - `t_i ≥ 0` whenever `m_i = 0`;
  - `m_i + m_j + m_k` is even on each pair of pants.

  This is the set of lattice points of a finite union of relatively open rational cones in
  the lattice `Λ = L ⊕ Z^{3g−3}`, where `L` is the parity sublattice of the `m`-coordinates.
  So `Λ ≅ Z^N`.
- **Mapping classes in these coordinates.** Each mapping class acts piecewise linearly,
  with finitely many rational cones (Penner; Penner–Harer: the PIL structure of `ML` is
  preserved by `Mod`, and `Mod` is finitely generated).
  - A linear piece on a full-dimensional cone maps that cone's lattice points, which
    generate `Λ`, into `ML_Z ⊆ Λ`. So its matrix, and likewise its inverse, preserves `Λ`,
    and it lies in `GL(Λ)`.
  - Lower-dimensional cones take the linear map of an adjacent full cone, by continuity on
    `ML`.
- **Lattice Hilbert hotel.** Call a *cell* a set `z + {Σ_{i≤k} n_i b_i : n_i ≥ 0}`, where
  `b_1, …, b_k` is part of a basis of `Z^N`. Every cell is affinely `GL_N(Z)`-equivalent to
  `N^k × 0`.
  - **Decomposing.** The lattice points of a relatively open rational cone form a finite
    disjoint union of cells, by a unimodular triangulation (toric resolution).
  - **Absorbing low dimensions.** `N^{k+1} ≅ N^{k+1} ⊔ N^k` via `x ↦ x + e_1` and the face
    `x_1 = 0`.
  - **Doubling.** `N^N ≅ N^N ⊔ N^N` for `N ≥ 2`, splitting along `x_1 ≥ x_2` and
    `x_2 ≥ x_1 + 1`, which are both unimodular cones.
  - **Conclusion.** Any two finite unions of cells, each containing an `N`-dimensional cell,
    are in piecewise-affine bijection. Both `ML_Z` and `Z^N` are such unions (orthants).
  - Take `Φ` to be the bijection so obtained, and absorb `{0}` so that `Φ(0) = 0`.
- **Composition.** Composites and inverses of piecewise-affine maps are piecewise affine,
  since preimages of polyhedra under affine maps are polyhedra. ∎

**Item 3.**
- `d = t_{d(0)} · (t_{−d(0)} d)`, and `T ∩ Stab(0) = 1`.
- For the stabilizer condition: if `Stab(0)` had a bounded orbit, item 1 of the cited node
  would give `Λ(D_g) = Λ(T)`, which has at most 2 points.

**Item 4.**
- **Pieces in rank one.** In rank one the pieces are intervals and `GL_1(Z) = {±1}`, so an
  element is eventually `±x + c` at each end.
- **End-preserving elements.** An end-preserving bijection has equal eventual shifts at the
  two ends (index). So it lies in `FSym(Z) ⋊ ⟨x ↦ x+1⟩ = H_2`, with index 2 overall.
- **Not finitely presented.** An index-2 overgroup of a group that is not finitely
  presented is not finitely presented.

**Item 5.**
- **The germ map.** The map "translation vector in a generic direction θ" is a homomorphism
  from piecewise translations to locally constant functions on the ray circle, with
  finitely many rational jumps.
- **Jumps everywhere.** For each primitive `ρ`, translating the half-plane
  `{⟨ρ^⊥, x⟩ > 0}` by `ρ` is a bijection with jumps at `±ρ`.
- **Not finitely generated.** A finitely generated subgroup has jumps in finitely many
  directions only. ∎

## Trust surface (recalled, not re-read at source)

- Dehn–Thurston coordinates and their parity conditions.
- The PIL structure of `ML`, preserved by `Mod`.
- Ivanov's theorem that infinite irreducible subgroups contain a pseudo-Anosov.
- BLM on canonical reduction systems.
- McCarthy: centralizers of pseudo-Anosovs are virtually cyclic.
- Exponential growth of intersection numbers along pseudo-Anosov orbits.
- Farb–Margalit Prop. 3.4.
- Unimodular triangulations of rational cones.

## Lesson for general BH

**Ports are translations.** Every port found so far has bounded displacement:
- the odometer on `Z`;
- Brown's Houghton element;
- here, the Dehn–Thurston translations of `ML_Z`.

**Twists do not qualify.** Dehn twists are parabolic, but not translations of any coordinate
the group preserves: they fix intersection numbers. So no subgroup of the input's own abelian
subgroups can serve as a port. The same holds for pseudo-Anosovs, whose orbits are
logarithmically sparse.

**The port has to be adjoined,** as the odometer was adjoined to `V`. A regular translation
port then satisfies `permutational-ports-need-stabilizers-crossing-every-splitting` for free,
through the exact factorization `D = T · Stab(0)`.

**For closed MCG this splits the problem into two layers.**
- *At infinity*, the lattice host induces rational piecewise-`GL_N(Z)` maps of the ray
  sphere, the maps R1's host `𝒯_{6g−7}` is built from. There R1's gates are Sync (proved
  on main), TD and the spine.
- *In bounded displacement*, there is a Houghton-type layer. Rank one fails (`H_2`), and
  translations alone are not finitely generated.

This mirrors Houghton's `H_n`, which becomes finitely presented once there are enough
directions at infinity.

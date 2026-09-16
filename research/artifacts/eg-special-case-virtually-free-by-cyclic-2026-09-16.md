# Eilenberg--Ganea for free-by-(tree-acting) groups and the virtually free-by-cyclic hole (lane hi-spec-eilenberg-ganea-conjecture, 2026-09-16)

This artifact supports three nodes:
- `free-by-virtually-cyclic-torsion-free-groups-have-gd-two`, called **Theorem A** below;
- `virtually-free-by-cyclic-normal-fibre-gives-gd-two`, called **Theorem B**;
- `torsion-free-virtually-free-by-cyclic-groups-have-gd-two`, the open hole.

All results are unreviewed.

**Conventions.**
- `cd` is cohomological dimension over `Z`.
- `gd G` is the least dimension of a `K(G,1)` CW complex.
- A tree action is *without inversions* if no element swaps the two ends of an edge.

## 0. Imported standard facts

These are recalled from standard references, not fetched this session, and are marked as
unverified pins. Each is textbook material.

- **(S) Serre.** If `G` is torsion-free and has a finite-index subgroup `U` with `cd U < ∞`,
  then `cd G = cd U`. Source: J.-P. Serre, *Cohomologie des groupes discrets* (1971); see
  K. S. Brown, *Cohomology of Groups*, GTM 87, Theorem VIII.3.1.
- **(SS) Stallings--Swan.** A group of `cd ≤ 1` is free, of any rank. Source: Stallings, Ann.
  of Math. 88 (1968), for finitely generated groups; Swan, J. Algebra 12 (1969) 585--610, in
  general.
- **(BS) Bass--Serre.** A group acting on a tree without inversions is the fundamental group of
  the quotient graph of groups. Its vertex and edge groups are the stabilizers of chosen lifts,
  and its edge monomorphisms are inclusions composed with conjugations. Source: Serre,
  *Trees*, §I.5.4.
- **(SW) Scott--Wall.** Let `X` be a graph of spaces with connected aspherical vertex and edge
  spaces and `π_1`-injective edge maps. Then `X` is aspherical, and `π_1 X` is the fundamental
  group of the associated graph of groups. Source: Scott--Wall, *Topological methods in group
  theory* (1979), Proposition 3.6.
- **(KPS) Karrass--Pietrowski--Solitar.** A finitely generated virtually free group is the
  fundamental group of a finite graph of finite groups. So it acts on a tree without
  inversions with finite stabilizers. Source: J. Austral. Math. Soc. 16 (1973) 458--466.
- **(R) Restriction.** If `C ⊲ Γ` has finite index, then restriction
  `H^1(Γ;Q) → H^1(C;Q)^{Γ/C}` is an isomorphism. Source: Brown, *Cohomology of Groups*,
  III.10.4.

## 1. Theorem A

**Theorem A.** Let `G` be torsion-free and `N ⊲ G` free, of any rank, possibly trivial.
Suppose `Γ = G/N` acts on a simplicial tree `T` without inversions and with finite vertex
stabilizers. Then `G` has a 2-dimensional `K(G,1)`, and `gd G = cd G ≤ 2`.

**Proof.**

*Step 1: all stabilizers are free.*
- Let `π: G → Γ` be the quotient map. `G` acts on `T` through `π`, again without inversions.
- For a vertex or edge `x` of `T`, the stabilizer is `G_x = π^{-1}(Γ_x)`.
- An edge stabilizer is contained in the stabilizers of the edge's endpoints, so every
  `Γ_x` is finite. Hence `N ≤ G_x` has finite index `|Γ_x|`.
- `G_x ≤ G` is torsion-free, and `cd N ≤ 1` since `N` is free. By (S), `cd G_x ≤ 1`.
- By (SS), `G_x` is free.

*Step 2: `G` is a graph of free groups.* By (BS), `G ≅ π_1(𝒢, Y)`, where:
- `Y = T/G` is the quotient graph;
- every vertex group `G_v` and edge group `G_e` is a stabilizer from Step 1, hence free;
- every edge monomorphism `G_e → G_{t(e)}` is injective.

`Y` may be infinite; nothing below needs finiteness.

*Step 3: a 2-dimensional graph of spaces.*
- For each vertex `v` of `Y`, let `X_v` be a wedge of circles indexed by a free basis of
  `G_v`, or a point if `G_v = 1`. Define `X_e` the same way for each edge `e`. These are
  aspherical connected CW complexes of dimension at most 1.
- For each edge `e` and each endpoint `w` of `e`, realize the monomorphism `G_e → G_w` by a
  based cellular map `f_{e,w}: X_e → X_w`. Send the wedge point to the base vertex, and send
  each circle, subdivided as needed, along an edge-path loop representing the image of the
  corresponding basis element. Such a map exists because `π_1` of a wedge of circles is free
  on the circles.
- Let `X` be `⊔_v X_v ⊔ ⊔_e (X_e × [0,1])` with `X_e × {0}` and `X_e × {1}` glued to the
  endpoint vertex spaces by the maps `f_{e,w}`.
- The attaching maps are cellular, so `X` is a CW complex. Its cells are the cells of the
  `X_v`, together with `σ × (0,1)` and the endpoint images, for cells `σ` of `X_e`. So
  `dim X ≤ 2`.
- The vertex and edge spaces are aspherical and the edge maps are `π_1`-injective. By (SW),
  `X` is aspherical with `π_1 X ≅ π_1(𝒢, Y) ≅ G`.

*Step 4: conclusion.* `X` is a `K(G,1)` of dimension at most 2, so `gd G ≤ 2` and hence
`cd G ≤ 2`. If `cd G ≤ 1`, then `G` is free by (SS) and `gd G = cd G`. Otherwise
`cd G = 2 = gd G`. ∎

**Remarks.**
1. If `N = 1`, the hypothesis says that `G` acts on a tree with finite, hence trivial,
   stabilizers, so `G` is free. This is consistent with the theorem.
2. Only the hypothesis "free normal subgroup with a tree-acting quotient" is used. The
   conclusion `cd G ≤ 2` is not assumed but produced.

## 2. Virtually cyclic groups act on the line

**Lemma L.** Let `Γ` be an infinite group containing a finite-index subgroup `C ≅ Z`. Then `Γ`
acts without inversions and with finite vertex stabilizers on the simplicial line with vertex
set `(1/2)Z`.

**Proof.**

*A central infinite cyclic subgroup.*
- Let `C_0 = ⋂_{γ} γCγ^{-1}` be the normal core. It has finite index in `Γ` and lies in `C`.
  Since `Γ` is infinite, `C_0 ≅ Z`.
- Conjugation gives `Γ → Aut(C_0) = {±1}`. Its kernel `Γ_+` has index at most 2, and `C_0` is
  central in `Γ_+`.

*A homomorphism with finite kernel.*
- By (R), restriction `H^1(Γ_+;Q) → H^1(C_0;Q)^{Γ_+/C_0} = H^1(C_0;Q)` is an isomorphism;
  the action is trivial because `C_0` is central. So there is `τ: Γ_+ → Q` with `τ|_{C_0} ≠ 0`.
- `Γ_+` is finitely generated, being virtually `Z`. So `τ(Γ_+)` is a nonzero finitely
  generated subgroup of `Q`, hence cyclic. Rescale so that `τ(Γ_+) = Z`.
- `ker τ ∩ C_0 = 1`, so `ker τ` injects into the finite group `Γ_+/C_0`.

*Case `Γ_+ = Γ`.* Let `γ` act by `t ↦ t + τ(γ)`. Stabilizers equal `ker τ`, which is finite.
Integer translations preserve `(1/2)Z` and invert no edge.

*Case `[Γ:Γ_+] = 2`.* Fix `s ∈ Γ \ Γ_+`; it inverts `C_0`.
- For `x ∈ Γ_+`, both `x ↦ τ(sxs^{-1})` and `−τ` are homomorphisms `Γ_+ → Q` that agree on
  `C_0`. Their difference kills a finite-index subgroup, so its image is a finite subgroup
  of `Q`, which is trivial. Hence `τ(sxs^{-1}) = −τ(x)`.
- In particular `s^2 ∈ Γ_+` and `τ(s^2) = τ(s·s^2·s^{-1}) = −τ(s^2)`, so `τ(s^2) = 0`.
- Define `ρ(x) = (t ↦ t + τ(x))` and `ρ(xs) = (t ↦ −t + τ(x))` for `x ∈ Γ_+`. Every element of
  `Γ` is uniquely `x` or `xs`.
- `ρ` is a homomorphism. For `x, y ∈ Γ_+`:
  - `ρ(x)ρ(y) = ρ(xy)`, clearly.
  - `ρ(x)ρ(ys)` is `t ↦ −t + τ(y) + τ(x)`, which is `ρ(xys)`.
  - `ρ(xs)ρ(y)` is `t ↦ −t + τ(x) − τ(y)`. Also `xsy = (x·sys^{-1})·s` with
    `τ(x·sys^{-1}) = τ(x) − τ(y)`.
  - `ρ(xs)ρ(ys)` is `t ↦ t + τ(x) − τ(y)`. Also `xsys = x·(sys^{-1})·s^2 ∈ Γ_+` with
    `τ = τ(x) − τ(y) + 0`.
- The image consists of integer translations and reflections `t ↦ n − t` with `n ∈ Z`.
  - These preserve the vertex set `(1/2)Z`.
  - A reflection sends the edge `[k/2, (k+1)/2]` to `[(2n−k−1)/2, (2n−k)/2]`. This is the
    same edge only if `2n = 2k + 1`, which is impossible. So there are no inversions.
- A vertex stabilizer consists of `ker τ` and at most one coset `(ker τ)·xs` of reflections
  fixing that vertex: if `xs` and `ys` both fix it, then `(xs)(ys)^{-1} = x y^{-1}` is a
  translation fixing a point, so it lies in `ker τ`. So vertex stabilizers have order at
  most `2|ker τ|`. ∎

**Corollary A1.** Let `G` be torsion-free and `N ⊲ G` free with `G/N` virtually cyclic. Then
`gd G = cd G ≤ 2`.

**Proof.**
- If `G/N` is finite, `G` is torsion-free and virtually free, so it is free by (S) and (SS).
- Otherwise combine Lemma L with Theorem A. ∎

## 3. Theorem B

**Setting.** `G` is torsion-free and `H ≤ G` has finite index with `H ≅ F ⋊_φ Z`, `F` free.
Replacing `H` by its normal core `H' ⊲ G` keeps this form:
- `H' ∩ F` is free;
- `H'/(H' ∩ F) ↪ Z` is infinite cyclic, because `H'` has finite index in `H`.

**Theorem B.** In this setting, `gd G = cd G ≤ 2` if either:
- **(i) normal fibre.** Some finite-index subgroup `H ≤ G` has a surjection `χ: H → Z` whose
  kernel `K` is free and normal in `G`; or
- **(ii) virtually `F_n × Z`.** `G` has a finite-index subgroup isomorphic to `F_n × Z` with
  `2 ≤ n < ∞`.

**Proof of (i).** `G/K` contains `H/K ≅ Z` with finite index. Apply Corollary A1 with `N = K`. ∎

**Proof of (ii).**
- Let `H_1 ≅ F_n × Z` have finite index in `G`, and let `H ⊲ G` be its normal core. So
  `H ≤ H_1` has finite index in `G`.
- *The center of `H` is infinite cyclic.* `N := H ∩ (1 × Z)` is central in `H` and has finite
  index in `1 × Z`, so `N ≅ Z`. Let `(w, t^k)` be central in `H`.
  - `U := {u ∈ F_n : (u,1) ∈ H}` has finite index in `F_n`. Since `n ≥ 2`, `U` is nonabelian,
    so it contains `u_1, u_2` that do not commute.
  - `w` commutes with every element of `U`. If `w ≠ 1`, its centralizer in `F_n` is cyclic,
    so `u_1` and `u_2` would commute. Hence `w = 1`, and `Z(H) = N`.
- `Z(H)` is characteristic in `H`, and `H ⊲ G`, so `N ⊲ G`. Also `N ≅ Z` is free.
- The projection `p: F_n × Z → F_n` restricted to `H` has kernel `N`. So `H/N ≅ p(H)`, a
  finite-index subgroup of `F_n`, which is finitely generated free.
- Therefore `G/N` is finitely generated and virtually free. By (KPS) it acts on a tree without
  inversions and with finite stabilizers. Theorem A gives `gd G ≤ 2`. ∎

**Corollary B1 (orbit of the fibration spans a line).** In the setting with `H ⊲ G`, let
`ψ: H → Z` be the projection with kernel `F`. For `g ∈ G` write `c_g(h) = ghg^{-1}`.
- Suppose that for every `g` the class `ψ∘c_g` is a rational multiple of `ψ`. Both are
  surjections onto `Z`, so `ψ∘c_g = ±ψ`.
- Then `g^{-1}Fg = ker(ψ∘c_g) = F`, so `F ⊲ G`, and (i) applies.
- This holds automatically when `b_1(H) = 1`.

**Corollary B2 (invariant fibration with free kernel).** Suppose `χ: H → Z` is surjective,
`χ∘c_g = χ` for all `g ∈ G`, and `ker χ` is free. Then (i) applies. In fact `G` is itself
free-by-cyclic:
- By (R), `χ` is the restriction of some `χ̄: G → Q`. Rescale to a surjection `G → Z`.
- `ker χ̄ ∩ H = ker χ` has finite index in `ker χ̄`, so `ker χ̄` is torsion-free and virtually
  free, hence free by (S) and (SS).

*Unverified remark, not used by any node.* Take `F` finitely generated and `χ` a rational
class in `Σ^1(H) ∩ −Σ^1(H)`.
- By Bieri--Neumann--Strebel, `ker χ` is finitely generated.
- Feighn--Handel coherence (Ann. of Math. 149 (1999)) then makes `ker χ` finitely presented.
- Bieri's normal subgroup theorem (J. Pure Appl. Algebra 7 (1976)) should then make `ker χ`
  free.

So B2 would apply whenever some `Q`-invariant class is fibred. These pins were recalled, not
checked this session.

**Corollary B3 (periodic monodromy).** Suppose `H = F_n ⋊_φ Z` with `n ≥ 2` and `φ` of finite
order `k` in `Out(F_n)`. Then (ii) applies:
- `φ^k` is conjugation by some `a ∈ F_n`.
- With `t` the stable letter, `a^{-1}t^k` centralizes `F_n`.
- So `⟨F_n, a^{-1}t^k⟩ ≅ F_n × Z` has index `k` in `H`.

## 4. The open hole and where the argument stops

**Hole.** `torsion-free-virtually-free-by-cyclic-groups-have-gd-two`: every torsion-free group
with a finite-index subgroup `F ⋊ Z`, `F` free, has `gd ≤ 2`.

**Why it matters.** By `virtually-rfrs-cd2-coherence-characterization` (FLSP, arXiv:2603.16763,
Corollary 4.1, pinned on main), a finitely generated virtually RFRS group `G` with
`cd_Q G ≤ 2` is virtually free-by-cyclic iff it is coherent, iff `b_2^(2)(G) = 0`. So the hole
implies:

> every torsion-free, finitely generated, virtually RFRS, coherent group of `cd 2` has
> `gd 2`.

This is EG for the coherent part of the RFRS world.

**What Theorem B leaves.** Work in the setting of §3 with `H ⊲ G` and `Q = G/H`. Theorem B
covers two cases:
- **(a)** some surjection `H → Z` with free kernel has a `G`-normal kernel;
- **(b)** the monodromy is periodic.

The remaining case therefore has, for every fibration `χ: H → Z` with free kernel, some
`g ∈ G` with `χ∘c_g ≠ ±χ`; and, with `F` finitely generated, non-periodic monodromy. So the
`Q`-orbit of every fibred class spans a subspace of rank at least 2.

**Where each natural extension dies.**

1. **Intersecting the orbit.**
   - `N = ⋂_g ker(ψ∘c_g)` is free and normal in `G`.
   - `G/N` is virtually `Z^r` with `r ≥ 2`. It acts properly on `R^r`, but on no tree with
     finite stabilizers, since `Z^2` has no such action.
   - The Theorem A construction over `R^r` gives only `gd ≤ r + 1 ≥ 3`.
2. **Averaging.** `Σ_{q∈Q} q·ψ` is invariant, but it can be zero or non-fibred when `Q`
   permutes several components of `Σ^1(H) ∩ −Σ^1(H)` with no fixed component. Averaging works
   only inside one convex `Q`-invariant component (Corollary B2).
3. **Coinduction.**
   - `G` acts freely on `X^{G/H}`, where `X` is the universal cover of a 2-dimensional
     `K(H,1)`, with the twisted product action.
   - This has dimension `2[G:H]`, and there is no equivariant retraction onto a 2-dimensional
     subcomplex.
   - Fixed-set tricks need `Q` to permute factors of a product decomposition of `X` itself,
     which is the product-of-trees situation of (ii), not the general one.
4. **Deficiency.**
   - `G` is finitely presented of type FP with `χ(G) = χ(H)/[G:H] = 0`. In fact `b_i^(2)` is
     0 for every `i`, by Lück's mapping torus theorem for `H`.
   - For a finite 2-complex `K` with `π_1 K = G` and `cd G ≤ 2`, `π_2 K` is a finitely
     generated projective summand of `C_2(K̃)` with `dim_{NG}(NG ⊗ π_2 K) = χ(K) − χ^(2)(G)`.
     Such a projective vanishes iff its von Neumann dimension does, since an idempotent matrix
     of trace 0 over `NG` is 0.
   - So a finite 2-dimensional `K(G,1)` exists iff `G` has a presentation of deficiency 1.
   - The presentation of `G` assembled from one of `H`, a transversal and one of `Q` has very
     negative deficiency. No Tietze-move control is known.
5. **Graph of free groups.** It is not known whether `G` splits at all when `b_1(G) = 0`.
   Theorem A needs a free normal subgroup with a tree-acting quotient, and none is visible in
   the remaining case.

**Scope.** This lane did not decide whether the Bestvina--Brady kernels of
`research/artifacts/hl-eg-bestvina-brady-2026-09-14.md` lie in this class. Nothing here bears
on the counterexample side.

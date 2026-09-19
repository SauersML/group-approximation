---
rg: 2
id: cubulated-groups-with-torsion-host-proof
kind: route
title: The orbit category of the flagged path category with finite cube stabilizers as units satisfies Li's hypotheses and (F); germs, exits, topological freeness, (Acyc) and minimality survive torsion because exit edges have trivial stabilizers and non-unit loops are hyperbolic
target: cubulated-groups-embed-in-f-infinity-simple-groups
requires:
  - cuntz-garside-coded-actions-embed-in-f-infinity-simple-groups
  - flagged-pointed-cube-category-resynchronizes-cubulated-actions
  - torsion-free-cubulated-groups-embed-in-f-infinity-simple-groups
---

**Lane proof, not independently reviewed.** Notation:
- `P` is the flagged path category of the target on `X'`. Its objects are all pairs `(w,σ)`
  with `σ ⊆ adj(w)`, and its morphisms are all triples `(w,σ;u,τ)`, with no quotient.
- **A morphism of `P` is determined by its endpoints.**
- Lemma C, the lcm formula and the whole of `flagged-pointed-cube-garside-verification` are
  statements about `P` and the geometry of `X'`. They never used freeness.
- "The torsion-free proof" means `torsion-free-cubulated-f-infinity-simple-host-proof`.

We check (C1)–(C4) of `cuntz-garside-coded-actions-embed-in-f-infinity-simple-groups` for
`𝔠 = 𝔠_{G'}`.

## 0. The space

- `X'` is a tree of CAT(0) cube complexes joined by single edges at vertices. It is simply
  connected, and vertex links are links in `X` plus isolated points. So it is a CAT(0) cube
  complex.
- It is locally finite: a vertex `w = g v_i` has `|Stab_G(v_i)|` outgoing and as many
  incoming `c`-edges. It is finite-dimensional.
- `G'` acts properly (stabilizers are conjugates of finite stabilizers of `G`) and
  cocompactly.
- `c`-edges are the edges of `T`, and have **trivial stabilizers**, because the edge groups
  are trivial.
- Every vertex has at least two `c`-edges (one outgoing, one incoming), whose far sides lie in
  different branches of `T`.

## 1. (C1): the orbit category

**Definition.** Composition is `(m,g)(m',g') = (m·gm', gg')`, which is defined since
`g·t(m') = g·r' = 𝐝(m)`. Associativity is clear.

**Cancellation.**
- **Left.** From `(m,g)(m_1,g_1) = (m,g)(m_2,g_2)`: `m·gm_1 = m·gm_2`. Both are composites
  from `r` through `𝐝(m)`, so `gm_1 = gm_2` by endpoints. Hence `m_1 = m_2`, and `g_1 = g_2`.
- **Right.** From `(m_1,g_1)(m,g) = (m_2,g_2)(m,g)`: the second coordinates give `g_1 = g_2`.
  Then `m_1·g_1m = m_2·g_1m` share endpoints and pass through `g_1 t(m)`, so
  `𝐝(m_1) = 𝐝(m_2)` and `m_1 = m_2`.
- **(F).** Right cancellation gives (F) (Li's remark after the definition of (F)).

**Units.** `(m,g)` is invertible iff `m` is an identity. So `𝔠*(r,r) = Stab_{G'}(r)`, which is
finite. There are finitely many objects.

**Disjoint mcms.** For `a = (m_1,g_1)` and `b = (m_2,g_2)` from `r`:
- `(n,h) ∈ a𝔠 ∩ b𝔠` iff `n` factors through both `𝐝(m_1)` and `𝐝(m_2)` in `P`.
- By the lcm formula in `P`, this happens iff `n` factors through the join `(j,τ_j)`.
- So `a𝔠 ∩ b𝔠 = (j, g)𝔠` for any `g` with `g·r_J = (j,τ_j)`, or it is empty.
- Hence `𝔠` is finitely aligned with lcms, in particular with disjoint mcms.

**Right Noetherian** holds as for `P`.

**Garside family.** Take `𝔖 = {(s,g) : s a one-step morphism of P}`, one representative per
right unit class. It is:
- `=*`-transverse, and disjoint from the units;
- locally finite, since `X'` is locally finite;
- closed under mcms and right divisors, since `P`'s one-step morphisms are, and units act
  equivariantly.

So Dehornoy's criterion (as quoted by Li) applies. The norm `‖(m,g)‖ = ‖m‖_P` is
unit-invariant, and `(𝔖^{≤L})^♯` is closed under left divisors, as in `P`.

**The boundary.**
- Infinite paths from the base representative `r_o = (o,∅)`, up to right units, are infinite
  paths of `P` from `(o,∅)`.
- The constructible ideals of the base cone are those of `P`.
- So `X_∞ ∩ cone(r_o) ≅ ∂_R X'`, by §2 of `flagged-pointed-cube-category-proof` (with the
  sink correction) applied to `P`.

## 2. (C2): every element is a global bisection

Fix `g ∈ G'` and a Roller point `ω`. Take `n`, `κ_n`, `M_±` and the neighbourhood `U` as in §3
of `flagged-pointed-cube-category-proof`, and the `P`-morphisms `m_n = o → (z_n, κ_n ∪ g^{-1}M_+)`
and `m' = o → (gz_n, gκ_n ∪ M_+)`.
- **The two morphisms.** Choose `a` with `a·r = 𝐝(m_n)`. Put `λ = (m_n, a)` and
  `μ = (m', ga)`. Both have domain `r`, since `ga·r = g·𝐝(m_n) = 𝐝(m')`.
- **The action on `U`.** The same computation of `H(o, gω')` shows that for `ω' = m_n·ζ ∈ U`
  we have `gω' = m'·gζ`. In `𝔠`-coordinates that reads `λ w ↦ μ w`.

So `g|_U` is one prefix replacement. By compactness `g` is a global bisection.

**Units act as stabilizer elements.** A unit `(id,k)` acts on the cone of `r` as `k`.
- More generally, for `λ = (m,g_1)` and `μ = (m,g_1k)` with the same `P`-part, the bisection
  `λw ↦ μw` equals the restriction of `h = g_1kg_1^{-1} ∈ Stab(𝐝(m))`. The reason is
  `H(o,hξ) = H(o,𝐝m) Δ hH(𝐝m, ζ)`, and the concatenation `o → 𝐝m → hζ` is geodesic because
  `h` preserves the label.
- In general, `λw ↦ μw` is the restriction of `g_2 g_1^{-1}` when `λ = (m_1,g_1)` and
  `μ = (m_2,g_2)`.

## 3. (C4) and faithfulness: topological freeness

- **Lemma E′** of the torsion-free proof holds verbatim in `X'`. It uses only the geometry of
  `X'` and the existence, at the exit vertex `q`, of two `c`-edges into different branches of
  `T` (§0).
- **(TF).** If `k ∈ G'` fixes a nonempty open subset of `∂_R X'` pointwise, then by Lemma E′ it
  fixes every end of `T` beyond some `c`-edge `e` with far vertex `x`.
  - `T` has infinite valence when `G` is infinite. (A finite `G` embeds in `V` anyway.)
  - So `x` lies on a geodesic between two such ends, and `k` fixes `x`.
  - `k` fixes every other edge at `x`, so it fixes `e` too.
  - Edge stabilizers are trivial, so `k = 1`.
- **Effective and Hausdorff.** Every germ `[λμ^{-1}, χ]` acts, by §2, as a group element
  `g_2g_1^{-1}`. That element is trivial only if `λ = μ`: equal group parts force equal
  `P`-parts, because the target and domain are fixed.
  - Right cancellation makes germ equality algebraic, so the unit-germ sets are empty or
    whole.
  - Hence `𝒢|_Y` is Hausdorff and effective.
- **Faithfulness.** Faithfulness of `G'` on `Y` is (TF).

## 4. (C3): (Acyc)

Let `σ = (m,h) ∈ 𝔠(r,r)` be a non-unit, with `r = (w,λ)`.
- **`h` is hyperbolic.** `m` goes from `(w,λ)` to `h·(w,λ)`. If `hw = w`, then `m` is a flag
  with `hλ ⊋ λ`, which is impossible since `|hλ| = |λ|`. So `hw ≠ w`.
- `σ^k = (m·hm·…·h^{k−1}m, h^k)` has a `P`-part that is a geodesic `w → hw → … → h^kw`. So
  `d(w,h^kw) = k·d(w,hw)`, and `h` has infinite order.
- **The trap.** `∩_k σ^k X(r)` consists of points crossing every wall of
  `W = ∪_k H(w,h^kw)`, and `W` is infinite.
- **Escape.** Take a basic open `B ⊆ X(r)`, and `q` and its two `c`-edges as in Lemma E′.
  - If `h` fixes a vertex `X_0` of `T`, the `T`-paths from `w`'s copy to `h^k`(`w`'s copy)
    stay within bounded distance of `X_0`. Take the `c`-edge at `q` whose branch moves away
    from `X_0`.
  - If `h` translates along an axis of `T` towards an end `ξ`, take the branch missing `ξ`.
  - In either case, the escaping point crosses only the finitely many walls of its prefix, and
    finitely many `c`-walls of `W` along its `T`-ray, because that ray leaves every bounded
    neighbourhood of `X_0` (or of the axis end). So it lies in `B` but not in the trap.

## 5. (C4): minimality

The walk of §5 of the torsion-free proof uses only Lemma E′, walks inside fresh copies, the
`c`-edges `c_{v''}` (which exist at every vertex), translates by group elements, and flags. So
`𝒢|_Y` is minimal. `Y ≅ ∂_R X'` has no isolated points.

## 6. Conclusion

(C1)–(C4) hold for `𝔠_{G'}`. By `cuntz-garside-coded-actions-embed-in-f-infinity-simple-groups`,
`G ≤ G'` embeds in the simple `F_∞` group `S`. Item 2 of the target is item 4 there. ∎

## Lesson for general BH

The free quotient was only ever a bookkeeping device. The orbit category, with stabilizers as
units, carries the same Garside structure, because every lattice property lives in the
unquotiented path category `P`. Torsion then touches only two things:
- the finite unit groups, which Li's `lem:Stab` absorbs;
- the dynamics, which free exits with trivial stabilizers make topologically free.

So for any input with finite stabilizers, the recipe is: build `P` on the space, take the
orbit category, add exits.

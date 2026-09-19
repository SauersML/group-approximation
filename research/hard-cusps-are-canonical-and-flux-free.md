---
rg: 2
id: hard-cusps-are-canonical-and-flux-free
kind: claim
title: A free cocompact cusp of a Cantor action is canonically (P × Cantor)^+, and when P is one-ended (every infinite f.g. simple P is) each germ at the cusp that commutes with P is the germ of a P-equivariant homeomorphism; for P = Z the two ends carry independent germs (Houghton flux)
distinct_from:
  free-product-boundary-groupoids-carry-the-vertex-group-homology: that computes dynamics and homology of one family of boundary actions (Z/k * B); this classifies the local structure at ANY free cocompact cusp of a Cantor action and computes the commutant of the cusp group in germs.
  lampshuffler-groups-are-not-fp2-over-q: that is about the branch-permutation subgroup FSym(P) ⋊ P, which is never FP_2; this is about germs at the cusp point itself.
  rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh: that is the open relative Boone–Higman statement, whose gate (RB) asks for germ groups (B)_p × S at parabolic points; this pins down which base germs can realize that shape.
---
**ESTABLISHED** (lane proof, bh-invent-15, 2026-09-18; elementary; not reviewed; no priority
claimed, and parts 1–2 are likely folklore). Part 3 uses two standard theorems that were
not re-read at source: Stallings' ends theorem, and the fact that acylindrically hyperbolic
groups are not simple (Dahmani–Guirardel–Osin).

## Setting
`X` is a Cantor space, `p ∈ X`, and a countable infinite group `P` acts on `X` by
homeomorphisms fixing `p`. Put `Y = X \ {p}`. The action is a **free cocompact cusp** if
`P` acts on `Y` freely and properly, with a compact set `C ⊂ Y` such that `P·C = Y`.
This is exactly a bounded parabolic point (Bowditch) with torsion-free stabilizer. In the
stabilizer engine of `free-product-boundary-groupoids-carry-the-vertex-group-homology` it
is the `B`-vertex `v`, with `Y = ⊔_{b∈B} bH`.

Let `𝒵_p(P)` be the group of germs at `p` of homeomorphisms `f` between neighborhoods
of `p` with `f(p) = p`, such that for every `g ∈ P` the germs of `fg` and `gf` at `p`
are equal. `Homeo_P(Y)` is the group of `P`-equivariant homeomorphisms of `Y`.

## Theorem
1. **Normal form.** There is a compact open `K ⊂ Y` with `Y = ⊔_{g∈P} gK`. The map
   `(g,k) ↦ gk` is a `P`-equivariant homeomorphism `P × K → Y`, and it extends to
   `(P × K)^+ ≅ X` (one-point compactification, `∞ ↦ p`). `K` is a Cantor space. So the
   pointed `P`-space `(X, p)` depends only on `P`: any two free cocompact `P`-cusps of
   Cantor actions are `P`-equivariantly homeomorphic, cusp to cusp.
2. **Commutant.**
   - (a) Every `Ψ ∈ Homeo_P(Y)` extends continuously to `X` with `Ψ(p) = p`, and
     `Ψ ↦ germ_p(Ψ)` is an injective homomorphism `Homeo_P(Y) → 𝒵_p(P)`. Writing
     `Ψ(1,k) = (α(k), φ(k))` gives `Homeo_P(Y) ≅ C(K,P) ⋊ Homeo(K)`, where `α` is locally
     constant and `(g,k) ↦ (g α(k), φ(k))`.
   - (b) **No flux.** If `P` is finitely generated and one-ended, this map is an
     isomorphism: every germ at the cusp commuting with `P` is the germ of a global
     `P`-equivariant homeomorphism.
   - (c) **Flux for `P = Z`.** `𝒵_p(Z) ≅ Homeo_Z(Y) × Homeo_Z(Y)`, with independent
     germs at the two ends, and `Homeo_Z(Y)` is the diagonal. The Houghton germ is right
     translation by `1` on the positive end and the identity on the negative end. It
     commutes with `Z` but is not the germ of an equivariant homeomorphism.
3. **Hard inputs are flux-free.** Every infinite finitely generated simple group is
   one-ended. So at every cusp whose group is such a group, 2(b) applies.
4. **The product shape of gate (RB) exists canonically.** If `a ∈ P` has infinite order
   and `P` has trivial centre, right multiplication `Ψ_a(gk) = gak` is in `Homeo_P(Y)`.
   The germs at `p` of `P` (left) and `Ψ_a` generate `P × Z`. In the stabilizer engine
   `F_B`, `Ψ_a` is locally a `D`-germ away from `v` (on the branch `bH` it is left
   multiplication by `bab^{-1}`). So `⟨F_B, Ψ_a⟩` is a finite germ extension of `F_B`
   with singular set `{v}` whose germ group at `v` contains `B × Z`.

## Proof
**1.**
- `Y` is open in `X`, so it is locally compact, Hausdorff and zero-dimensional.
- **Slices.** For `y ∈ Y` pick a compact open `U_0 ∋ y`. By properness,
  `{g : gU_0 ∩ U_0 ≠ ∅}` is finite. Each such `g ≠ 1` moves `y` (freeness), so we can
  shrink `U_0` to a compact open `U ∋ y` with `gU ∩ U = ∅` for all `g ≠ 1`.
- **The quotient.** `π : Y → Y/P` is open, and it is injective on each such `U`.
  `Y/P = π(C)` is compact. It is Hausdorff by properness, so each `π(U)` is compact open,
  hence clopen.
- **A section.** Finitely many `π(U_1), …, π(U_r)` cover `Y/P`. Put
  `W_i = π(U_i) \ ∪_{j<i} π(U_j)`, which are clopen, and
  `K = ⊔_i (U_i ∩ π^{-1}(W_i))`, which is compact open. Then `π|_K` is a bijection onto
  `Y/P`. By freeness every orbit meets `K` exactly once, so `Y = ⊔_g gK`.
- **The homeomorphism.** `(g,k) ↦ gk` is a continuous bijection `P × K → Y`, and it maps
  each `{g} × K` homeomorphically onto the open set `gK`, so it is a homeomorphism.
- **The point `p`.** `X` is compact, so the neighborhoods of `p` are the complements of
  compact subsets of `Y`, and such a subset meets only finitely many of the disjoint open
  sets `gK`. This is the topology of `(P × K)^+`.
- **`K` is Cantor.** `K` is nonempty (`P` is infinite and `Y ≠ ∅`), compact, metrizable,
  zero-dimensional, and perfect because `X` is.
- **Uniqueness.** Any two Cantor spaces are homeomorphic, so `(P × K)^+ ≅ (P × K')^+`
  equivariantly.

**2(a).**
- A `P`-equivariant homeomorphism has the form `Ψ(g,k) = (g α(k), φ(k))`. Here
  `α : K → P` is continuous, hence locally constant with finitely many values. `φ` is a
  homeomorphism, because `Ψ(1,K)` is again a fundamental domain.
- So `Ψ` maps sets `F × K` with `F` finite to compact sets, and back. It therefore
  extends continuously to `X` with `Ψ(p) = p`, and it commutes with `P` exactly.
- If `germ_p(Ψ) = 1`, then `Ψ` is the identity on `(P \ F) × K` for some finite `F`, and
  by equivariance everywhere.
- The composition law `(α, φ)(α', φ') = (k ↦ α(k) α'(φ(k)), φ' ∘ φ)` is that of
  `C(K,P) ⋊ Homeo(K)`.

**2(b).**
- **Setup.** Let `f` represent a germ in `𝒵_p(P)`: a homeomorphism from
  `N_0 = {p} ∪ (P \ F_0) × K` onto an open neighborhood of `p`. For `g ∉ F_0` write
  `f(g,k) = (g α(g,k), β(g,k))`.
- **Local constancy in `g`.** Fix a finite symmetric generating set `Σ`. For `s ∈ Σ`,
  `fs = sf` near `p`, so there is a finite `F_s` with `α(sg,k) = α(g,k)` and
  `β(sg,k) = β(g,k)` for `g ∉ F_s`.
- **One end.** Let `F ⊇ F_0 ∪ ∪_s F_s` be finite. The graph on `P \ F` with edges
  `g — sg` is the Cayley graph minus a finite set. Since `P` is one-ended, it has one
  infinite component and finitely many finite ones. Add the finite ones to `F`. Then `α`
  and `β` do not depend on `g ∈ P \ F`: `f(g,k) = g Φ(k)`, with `Φ = (α_0, β_0)`
  continuous.
- **`Φ(K)` is a fundamental domain.**
  - *Disjoint translates.* For `h ≠ 1` pick `g ∉ F ∪ F h^{-1}`. Injectivity of `f` gives
    `gΦ(K) ∩ ghΦ(K) = ∅`, so `Φ(K) ∩ hΦ(K) = ∅`.
  - *Covering.* `f(N_0)` contains `(P \ F') × K` for some finite `F'`. Enlarge `F'` so that
    it also avoids the compact set `f((F \ F_0) × K)`. For `y ∈ Y` and `g'` large, `g'y`
    lies in `(P \ F') × K`, so `g'y = gΦ(k)` with `g ∉ F`, and `y = g'^{-1}g Φ(k)`.
  - *Openness.* `gΦ(K) = f({g} × K)` is open, since `f` is a homeomorphism onto an open
    set.
- **Conclusion.** `Ψ(g,k) := gΦ(k)` is a `P`-equivariant homeomorphism of `Y`, and it
  agrees with `f` on `{p} ∪ (P \ F) × K`.

**2(c).** Run the same argument with `F = [−N, N]`. The complement now has two infinite
components, so `f(n,k) = n Φ_+(k)` for `n > N` and `f(n,k) = n Φ_−(k)` for `n < −N`.
- Each `Φ_±(K)` is a fundamental domain. The covering step uses `n ≫ 0` for `Φ_+` and
  `n ≪ 0` for `Φ_−`, and `α` takes finitely many values.
- Conversely, any pair of equivariant homeomorphisms `(Ψ_+, Ψ_−)`, used on the far
  positive and far negative regions, is a homeomorphism between neighborhoods of `p` that
  commutes with `Z`. So `𝒵_p(Z) ≅ Homeo_Z(Y)^2`.
- The Houghton germ `(ρ_1, id)` is off the diagonal.

**3.** Let `S` be infinite, finitely generated and simple.
- `S` is not two-ended: a two-ended group has an infinite cyclic normal subgroup of
  finite index.
- If `S` had infinitely many ends, Stallings would split it over a finite subgroup:
  - an HNN extension maps onto `Z`;
  - an amalgam that is not two-ended acts on its Bass–Serre tree non-elementarily with
    finite edge stabilizers, so it is acylindrically hyperbolic, and such groups are not
    simple (Dahmani–Guirardel–Osin).
- So `S` is one-ended.

**4.**
- *Homeomorphism.* `Ψ_a` is a bijection of `Y` that maps `gK` homeomorphically onto
  `gaK`. It commutes with left multiplication, and it is continuous at `p` because
  `F ↦ Fa^{-1}` preserves finiteness.
- *The germs commute.* Left and right multiplications commute, so the germs of `P` and
  `Ψ_a` at `p` commute.
- *They intersect trivially.* Suppose the germ of left multiplication by `s` equals
  `ρ_a^m`. Then `sb = ba^m`, that is `b^{-1}sb = a^m`, for all `b` outside a finite set.
  The quotients `b'b^{-1}` of such `b, b'` generate `P` and centralize `s`, so `s` is
  central. Hence `s = 1` and then `a^m = 1`, so `m = 0`. So the germs generate `P × Z`.
- *In the engine.* On the branch `bH`, `Ψ_a` sends `bx` to `bax = (bab^{-1})(bx)` for
  `x ∈ H`. That is a `D`-germ at every point other than `v`.

## The geometric route, and where it lands
The seed was to build finitely presented simple hosts from hyperbolic geometry: small
cancellation, Dehn filling, or rotating families over a hyperbolic group containing the
input. Here is where that route ends up.
1. **One-step geometric quotients are never simple.** These are standard facts, not
   re-read.
   - A quotient of a hyperbolic group by finitely many small-cancellation relators is
     hyperbolic.
   - A Dehn filling with finitely many relators (`relatively-hyperbolic-dehn-filling`) is
     relatively hyperbolic.
   - In both cases a non-elementary result is acylindrically hyperbolic, and so not
     simple.
   - Simple quotients come only from infinite towers (Olshanskii), which are infinitely
     presented. For the tower to be finitely presented it would have to be generated by a
     finite recursion. When that recursion is internal to the group, it is exactly the
     self-similarity of a boundary full group.
   - So hyperbolic geometry can enter a finitely presented simple host only as **germs on
     a boundary**. This is Belk–Bleak–Matucci–Zaremsky's mechanism
     (`hyperbolic-groups-satisfy-boone-higman`), not a quotient.
2. **Hard inputs sit at cusps.** An input `S` that is simple with property (FA) and no
   finite quotients cannot act through trees or buildings (SYNTHESIS v5). In a boundary
   picture it must be a parabolic stabilizer, so the host is a full group of a relatively
   hyperbolic boundary action.
   - The smallest instance, `Z/2 * S` on its Bowditch boundary (= the compactified
     Bass–Serre tree), is the stabilizer engine `F_S`.
   - The next instance, `S * T`, contains `S * T` in its derived group (both factors are
     perfect), so it encodes joint embedding.
3. **Every hard cusp is the same cusp** (Theorem 1). In every such construction the germ
   data at an `S`-cusp is `(S × Cantor)^+` with `S` acting on the left. So gate (RB) of
   `rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh` and gate (IE) of
   `simple-inputs-have-finitely-presented-stabilizer-engines` see identical local objects
   at their singular points. They can differ only away from the cusps, where the
   dynamics is hyperbolic and finite state.
4. **The commutant is rigid** (Theorems 2–3). A base group `B` whose germ group at the
   cusp commutes with `S`, as (RB) demands with `(E)_p ≅ (B)_p × S`, must act near the
   cusp by **fundamental-domain changes** `(g,k) ↦ (g α(k), φ(k))`.
   - For a hard `S` there is no other option, since there is no flux.
   - A contracting base germ is therefore an `S`-cocycle whose products escape to
     infinity in `S`. The model case is right multiplication `Ψ_a` (Theorem 4).
   - `V`-type rational contractions are not of this form in the branch coordinates. For
     `P = Z` (Reid's group, MO 339541) the extra Houghton germs exist. That is a
     two-ended accident with no analogue for simple inputs.

## Gate
- **What it does not do.** The geometric route does **not** bypass the emitter gate.
  After the reductions above it lands on it exactly. It replaces (RB) by (IE) at a
  canonical cusp, plus one interface:
- **(RB′)** Find a Cantor coding of the relative boundary, and a base `B` satisfying the
  hypotheses of Belk–Hyde–Matucci's finiteness corollary (arXiv:2407.03149: `F_∞`,
  oligomorphic on the singular set, fixers of type `F_2`). At each cusp, the germ group
  of `B` must be generated by one right multiplication `Ψ_a`, `a ∈ S` of infinite order.
  - Theorem 4 shows that this germ shape `S × Z` is realized canonically inside the
    engine's own dynamics.
  - What is missing is a finite-type base that contains `Ψ_a` but not `S`.
- **Ranking impact (for bh-synth-lead).** Gates 1–2 of SYNTHESIS v5 and the relhyp gate
  (RB) are one gate. Reid's group is the only fluxed case, so a negative answer there
  would not transfer to simple inputs. The flux-free test is the engine of a one-ended,
  finitely presented, decidable group with trivial centre, for example `B = F` or
  `B = V`.

## Lesson for general BH
- Geometry cannot make a finitely presented simple group by quotienting. It can only
  supply boundary germs.
- Hard inputs live at cusps, and every free cocompact cusp is canonically
  `(P × Cantor)^+`.
- For one-ended `P`, which includes every simple input, the germs at the cusp that commute
  with `P` are exactly the `P`-equivariant fundamental-domain changes, with no flux.
- So all relative-boundary routes to BH share one local model. The open part is a
  finite-type base carrying a single right multiplication at the cusp. The Houghton
  (flux) behaviour of Reid's group is special to two ends.

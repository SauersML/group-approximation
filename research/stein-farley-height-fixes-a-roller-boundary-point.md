---
rg: 2
id: stein-farley-height-fixes-a-roller-boundary-point
kind: claim
title: "Thompson's F and V each fix a point of the Roller boundary of their Farley cube complex, with the height function as horofunction; so cube-boundary amenable-action routes to amenability or exactness of F are root-equivalent, and V shows the fixed point carries no amenability information"
distinct_from:
  brin-thompson-nv-stein-farley-complex-is-not-cat0: that shows the nV expansion complex (n >= 2) is not CAT(0); this uses the CAT(0) complexes for F and V (n = 1) and finds a fixed point at infinity.
  thompson-f-folner-function-exceeds-every-tower: that is Moore's lower bound on Følner sets; this pins cube-boundary witnesses to it through the fixed point (item 4).
  f-sandwich-splits-collapse-unless-kernel-is-brin-sapir-exotic: that collapses subgroup and co-amenable splits; this collapses the geometric boundary route through F's one proper cubical action, which involves no split.
---

**ESTABLISHED** (`stein-farley-height-fixes-a-roller-boundary-point-proof`), modulo Farley's CAT(0)
theorems, which are cited.

**Grading Lemma.** Let `X` be a CAT(0) cube complex and `h : X⁽⁰⁾ → Z` a *height* such that:

- (G1) every cube `C` has a vertex `b_C` with `h(w) = h(b_C) + d(b_C, w)` for all vertices `w ∈ C`;
- (G2) the order `x ≤ y` ("some edge path from `x` to `y` raises `h` by 1 at each step") is directed;
- (G3) every vertex has a neighbour of larger height.

Then:

- every hyperplane `H` has an *upper* halfspace `H⁺`, the side holding the higher endpoint of every edge dual
  to `H`;
- `σ_h = {H⁺}` is a non-principal ultrafilter, that is, a point of the Roller boundary `∂X`;
- every automorphism of `X` preserving `h` fixes `σ_h`;
- `h` is the combinatorial horofunction of `σ_h`: `Σ_H (1_{H⁺}(y) − 1_{H⁺}(x)) = h(y) − h(x)` for all
  vertices `x, y`.

**Instances.**

1. **F.** `X_F` is the Stein–Farley complex. Its vertices are the dyadic PL homeomorphisms
   `φ : [0,1] → [0,n]` (`n ≥ 1`) and `h(φ) = n`. Edges and cubes are simultaneous expansions of distinct unit
   intervals. `F` acts by `g·φ = φ∘g⁻¹`; the complex is CAT(0) by Farley (Topology 42, 2003). `F` fixes
   `σ_F`, and it acts **simply transitively** on each horosphere `{h = n}`.
2. **V.** `X_V` is Farley's complex for `V` (vertices: charted partitions of the Cantor set, height = number
   of pieces; CAT(0) and proper, Farley, IMRN 2003). `V` fixes `σ_V` and acts transitively on each horosphere
   `{h = n}` with stabilizer `S_n`. `V` contains `F_2`.

**Class killed** (the invariant is `σ_F`, the up-orientation of expansion hyperplanes).

3. *Amenable boundary actions.* Let `Z` be any compact `F`-space containing an `F`-fixed point. Examples are
   `X̄_F`, `∂X_F`, and every closed invariant subset containing `σ_F`. Then `F ↷ Z` is topologically amenable
   iff `F` is amenable. Zimmer amenability of `(∂X_F, δ_{σ_F})` is likewise equivalent to amenability of `F`.
   - This kills the Brodzki–Campbell–Guentner–Niblo–Wright / Nevo–Sageev template (amenable action on the
     Roller boundary) as a route to amenability of `F`.
   - It also kills that template as a route to **exactness (property A) of F**, which to our knowledge is
     open. Any such proof proves amenability.
   - *Dying step:* evaluate the approximately equivariant maps `Z → Prob(F)` at `σ_F`.
4. *Quantitative pin.* Suppose `m : Z → Prob(F)` has `supp m(z) ⊆ B_r` and `‖g·m(z) − m(gz)‖₁ ≤ ε` for all
   `g ∈ S` (symmetric generating set `S`). Then `m(σ_F)` is an `ε`-Reiter measure supported in `B_r`.
   Namioka's level-set argument gives a level set `A ⊆ B_r` with `Σ_{s∈S} |sA △ A| ≤ |S|ε·|A|`. So
   `Føl_F(⌊1/(|S|ε)⌋) ≤ |B_r| ≤ (2|S|+1)^r`, and by Moore
   (`thompson-f-folner-function-exceeds-every-tower`) `r` is at least a tower of height about
   `log_C(1/(|S|ε)) − 1`. So explicit boundary witnesses cost what Følner sets cost, up to one logarithm.
5. *Non-amenability side.* The Roller-boundary tools that produce free subgroups or non-amenability from
   boundary dynamics assume there is no finite orbit in `X̄`. These are the Chatterji–Fernós–Iozzi Tits
   alternative, Fernós's regular points, and the Nevo–Sageev non-elementary Poisson boundary. `F ↷ X_F` has
   an orbit of size 1, so these tools do not apply, whatever the dimension. Caprace–Sageev rank rigidity is
   stated for finite-dimensional complexes, so it does not apply either. That is a separate failure, not
   this invariant.
6. *Calibration.* `V` satisfies every structural property above: a proper action on a graded CAT(0) cube
   complex, a fixed Roller point whose horofunction is the height, and transitive horosphere actions with
   finite stabilizers. Yet `V` is non-amenable. So no argument that uses only these properties of `F ↷ X_F`
   proves amenability. Such an argument must use what separates `F` from `V`, namely the linear order of the
   pieces (planarity of the forest diagrams).

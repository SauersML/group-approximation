import GroupApproximation.CharClass.ThomKunnethProjective

/-!
# The top line of a product of spheres and projective spaces

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C, hypothesis 8).

`topChernClass_ne_zero_of_chain` needs `absEquiv : H^{2r}(N; F₂) ≃ₗ F₂` for
`N = S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}` at its top degree `2r = 1 + 5 + ∑ⱼ 2dⱼ`.  This file
proves that by pure Mayer–Vietoris, with **no cross product and no Künneth
isomorphism**: only the vanishing-form Künneth factors already in the lane
(`kunnethFactor_sphere`, `kunnethFactor_CP`) and the connecting isomorphism
`mvConnectingIso` of `cc-cohom-api`.

## The shape of the induction

`HasTopLine Z d` bundles the two facts that propagate together: the cohomology
of `Z` vanishes strictly above `d`, and `H^d(Z; F₂)` is one dimensional.  Both
inductive steps are the *same* Mayer–Vietoris move, packaged once as
`prodCoverConnecting`: cross a two-set cover `Y = U ∪ V` with `A`, note that all
four vanishing hypotheses of `mvConnectingIso` hold because `A` has already run
out of cohomology, and read off

```text
H^{m}(A × (U ∩ V); F₂)  ≅  H^{m+1}(A × Y; F₂).
```

* **Sphere step** (`hasTopLine_prod_sphere_succ`): `U, V` the two punctured
  hemispheres, `U ∩ V` the equatorial band `≃ Sⁿ`.  It needs `1 ≤ n`, because
  the piece `A × U` must have vanishing cohomology in degree `p + n`, and
  `p + n > p` only from `n ≥ 1`.
* **Projective step** (`hasTopLine_prod_CP_succ`): `U` the affine chart, `V` the
  complement of the base point, `U ∩ V ≃ S^{2d+1}`.

**Where the induction bottoms out.**  Both steps descend to `A × S¹`, and there
the argument stops: the sphere step at `n = 0` would need `H^p(A; F₂) = 0`,
which is exactly the top line it is trying to produce.  The circle case is
therefore a genuine computation and not formal, so it is carried here as the
named hypothesis `CircleTopLineStep`.  Everything else in this file is
unconditional.  (The base `HasTopLine (Sⁿ) n` itself is *not* affected: it is
`sphereTopEquiv`, which the vendored tree already proves through the mod-2
universal coefficient isomorphism.)

## Main declarations

* `HasTopLine` — the propagated predicate, with `congr` and `congrHomotopy`.
* `hasTopLine_sphere` — the base case `H^n(Sⁿ; F₂) ≃ F₂`, unconditional.
* `prodCoverConnecting` — the single Mayer–Vietoris move both steps use.
* `hasTopLine_prod_sphere_succ`, `hasTopLine_prod_sphere` — the sphere induction.
* `hasTopLine_prod_CP_succ`, `hasTopLine_prod_CP` — the projective induction.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. The predicate -/

/-- **A space with a top line.**  `Z` has no mod-2 cohomology strictly above degree
`d`, and its degree-`d` cohomology is one dimensional.  This is the pair of facts
that propagate together through a product: the vanishing feeds the Mayer–Vietoris
hypotheses of the next factor, and the line is what `absEquiv` asks for. -/
structure HasTopLine (Z : Type) [TopologicalSpace Z] (d : ℕ) : Prop where
  /-- No cohomology strictly above the top degree. -/
  vanish : ∀ k, d < k → IsZero (Hmod2 (TopCat.of Z) k)
  /-- The top cohomology is a line over `F₂`. -/
  line : Nonempty (Hmod2 (TopCat.of Z) d ≃ₗ[ZMod 2] ZMod 2)

/-- A top line transports along a homotopy equivalence. -/
theorem HasTopLine.congrHomotopy {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W]
    {d : ℕ} (h : HasTopLine Z d) (e : ContinuousMap.HomotopyEquiv Z W) : HasTopLine W d := by
  obtain ⟨l⟩ := h.line
  exact ⟨fun k hk => thomIsZero_of_linearEquiv (pullEquivOfHomotopyEquiv e k) (h.vanish k hk),
    ⟨(pullEquivOfHomotopyEquiv e d).trans l⟩⟩

/-- A top line transports along a homeomorphism. -/
theorem HasTopLine.congr {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W]
    {d : ℕ} (h : HasTopLine Z d) (e : Z ≃ₜ W) : HasTopLine W d :=
  h.congrHomotopy e.toHomotopyEquiv

/-! ## 2. The base case: a sphere -/

/-- **`H^n(Sⁿ; F₂) ≃ F₂`, with nothing above.**  Both halves are already proved in
the vendored tree, through the mod-2 universal coefficient isomorphism. -/
theorem hasTopLine_sphere (n : ℕ) (hn : 1 ≤ n) : HasTopLine (Sphere n) n :=
  ⟨fun k hk => sphere_coh_isZero_of_gt n k hk, ⟨sphereTopEquiv n hn⟩⟩

/-! ## 3. The single Mayer–Vietoris move -/

/-- Cohomology transported along an equality of subsets. -/
def cohSetCongr {Y : Type} [TopologicalSpace Y] {S T : Set Y} (h : S = T) (k : ℕ) :
    Hmod2 (TopCat.of ↥S) k ≃ₗ[ZMod 2] Hmod2 (TopCat.of ↥T) k :=
  (pullEquivOfHomeomorph (Homeomorph.setCongr h) k).symm

/-- **The Mayer–Vietoris connecting isomorphism of a product cover.**  Cross a
two-set open cover `Y = U ∪ V` with a space `A`.  If the cohomology of both
`A × U` and `A × V` vanishes in degrees `m` and `m+1`, the connecting map is an
isomorphism, and the intersection is identified through any homotopy equivalence
`U ∩ V ≃ W`:

```text
H^m(A × W; F₂)  ≅  H^{m+1}(A × Y; F₂).
```

Both inductive steps below are this lemma. -/
def prodCoverConnecting (A : Type) [TopologicalSpace A] {Y : Type} [TopologicalSpace Y]
    (U V : Opens Y) (hUV : U ⊔ V = ⊤) {W : Type} [TopologicalSpace W]
    (eW : ContinuousMap.HomotopyEquiv ↥((U ⊓ V : Opens Y) : Set Y) W) (m : ℕ)
    (hU : IsZero (Hmod2 (TopCat.of ↥((prodOpen A U : Opens (A × Y)) : Set (A × Y))) m))
    (hV : IsZero (Hmod2 (TopCat.of ↥((prodOpen A V : Opens (A × Y)) : Set (A × Y))) m))
    (hU' : IsZero (Hmod2 (TopCat.of ↥((prodOpen A U : Opens (A × Y)) : Set (A × Y))) (m + 1)))
    (hV' : IsZero (Hmod2 (TopCat.of ↥((prodOpen A V : Opens (A × Y)) : Set (A × Y))) (m + 1))) :
    Hmod2 (TopCat.of (A × W)) m ≃ₗ[ZMod 2] Hmod2 (TopCat.of (A × Y)) (m + 1) :=
  ((pullEquivOfHomotopyEquiv ((ContinuousMap.HomotopyEquiv.refl A).prodCongr eW) m).trans
      ((prodOpenCohEquiv A (U ⊓ V) m).trans
        (cohSetCongr
          (S := ((prodOpen A (U ⊓ V) : Opens (A × Y)) : Set (A × Y)))
          (T := ((prodOpen A U : Opens (A × Y)) : Set (A × Y))
            ∩ ((prodOpen A V : Opens (A × Y)) : Set (A × Y)))
          (by rw [← prodOpen_inf A U V, Opens.coe_inf]) m))).trans
    (mvConnectingIso (X := TopCat.of (A × Y)) (prodOpen A U) (prodOpen A V)
      (prodOpen_sup A hUV) m hU hV hU' hV').toLinearEquiv

/-! ## 4. The circle step, as a named hypothesis -/

/-- **The one step the Mayer–Vietoris argument does not give.**  Both inductions
descend to `A × S¹`, where the cover of the circle by two arcs has *disconnected*
intersection, so the connecting map is no longer an isomorphism: one has to
compute the rank of the restriction `H^p(A × U) ⊕ H^p(A × V) → H^p(A × S⁰)`.
That is a genuine computation, carried as a hypothesis here. -/
def CircleTopLineStep : Prop :=
  ∀ (A : Type) [TopologicalSpace A] (p : ℕ), HasTopLine A p → HasTopLine (A × Sphere 1) (p + 1)

/-! ## 5. The sphere induction -/

/-- The equatorial band, as a homotopy equivalence out of the intersection of the
two hemispherical opens. -/
def bandInterHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv
      ↥((upperOpens n ⊓ lowerOpens n : Opens ↥(sphereSpace n)) : Set ↥(sphereSpace n))
      (Sphere n) :=
  (Homeomorph.setCongr (by
      rw [Opens.coe_inf]; exact upperOpens_inter_lowerOpens n)).toHomotopyEquiv.trans
    (sphereBandHomotopyEquiv n)

set_option maxHeartbeats 1000000 in
/-- **The sphere step.**  Crossing with `S^{n+1}` raises the top degree by `n+1`,
provided `n ≥ 1`. -/
theorem hasTopLine_prod_sphere_succ (A : Type) [TopologicalSpace A] (p n : ℕ) (hn : 1 ≤ n)
    (hA : HasTopLine A p) (hAn : HasTopLine (A × Sphere n) (p + n)) :
    HasTopLine (A × Sphere (n + 1)) (p + (n + 1)) := by
  obtain ⟨l⟩ := hAn.line
  refine ⟨fun k hk => (kunnethFactor_sphere (n + 1)).prod A p hA.vanish k (by omega), ⟨?_⟩⟩
  have hU : IsZero (Hmod2 (TopCat.of
      ↥((prodOpen A (upperOpens n) : Opens (A × Sphere (n + 1))) : Set (A × Sphere (n + 1))))
      (p + n)) :=
    isZero_prodOpen_of_contractible A (upperOpens n) (p + n) (hA.vanish (p + n) (by omega))
  have hV : IsZero (Hmod2 (TopCat.of
      ↥((prodOpen A (lowerOpens n) : Opens (A × Sphere (n + 1))) : Set (A × Sphere (n + 1))))
      (p + n)) :=
    isZero_prodOpen_of_contractible A (lowerOpens n) (p + n) (hA.vanish (p + n) (by omega))
  have hU' : IsZero (Hmod2 (TopCat.of
      ↥((prodOpen A (upperOpens n) : Opens (A × Sphere (n + 1))) : Set (A × Sphere (n + 1))))
      (p + n + 1)) :=
    isZero_prodOpen_of_contractible A (upperOpens n) (p + n + 1)
      (hA.vanish (p + n + 1) (by omega))
  have hV' : IsZero (Hmod2 (TopCat.of
      ↥((prodOpen A (lowerOpens n) : Opens (A × Sphere (n + 1))) : Set (A × Sphere (n + 1))))
      (p + n + 1)) :=
    isZero_prodOpen_of_contractible A (lowerOpens n) (p + n + 1)
      (hA.vanish (p + n + 1) (by omega))
  exact (prodCoverConnecting A (Y := Sphere (n + 1)) (upperOpens n) (lowerOpens n)
    (upperOpens_sup_lowerOpens n) (bandInterHomotopyEquiv n) (p + n)
    hU hV hU' hV').symm.trans l

/-- **The sphere induction.**  Given the circle step, crossing with any sphere of
positive dimension raises the top degree by that dimension. -/
theorem hasTopLine_prod_sphere (hcirc : CircleTopLineStep) (A : Type) [TopologicalSpace A]
    (p : ℕ) (hA : HasTopLine A p) : ∀ n, 1 ≤ n → HasTopLine (A × Sphere n) (p + n) := by
  intro n
  induction n with
  | zero => intro hn; exact absurd hn (by omega)
  | succ n ih =>
      intro _
      rcases Nat.eq_zero_or_pos n with hz | hpos
      · subst hz
        exact hcirc A p hA
      · exact hasTopLine_prod_sphere_succ A p n hpos hA (ih hpos)

/-! ## 6. The projective induction -/

set_option maxHeartbeats 1000000 in
/-- **The projective step.**  Crossing with `ℂP^{d+1}` raises the top degree by
`2(d+1)`, the input being the top line of `A × S^{2d+1}`. -/
theorem hasTopLine_prod_CP_succ (A : Type) [TopologicalSpace A] (p d : ℕ)
    (hA : HasTopLine A p) (hS : HasTopLine (A × Sphere (2 * d + 1)) (p + (2 * d + 1))) :
    HasTopLine (A × CP (d + 1)) (p + 2 * (d + 1)) := by
  obtain ⟨l⟩ := hS.line
  haveI := contractibleSpace_chartOpen d
  refine ⟨fun k hk => (kunnethFactor_CP (d + 1)).prod A p hA.vanish k (by omega), ⟨?_⟩⟩
  have hU : IsZero (Hmod2 (TopCat.of
      ↥((prodOpen A (chartOpen d) : Opens (A × CP (d + 1))) : Set (A × CP (d + 1))))
      (p + 2 * d + 1)) :=
    isZero_prodOpen_of_contractible A (chartOpen d) (p + 2 * d + 1)
      (hA.vanish (p + 2 * d + 1) (by omega))
  have hU' : IsZero (Hmod2 (TopCat.of
      ↥((prodOpen A (chartOpen d) : Opens (A × CP (d + 1))) : Set (A × CP (d + 1))))
      (p + 2 * d + 1 + 1)) :=
    isZero_prodOpen_of_contractible A (chartOpen d) (p + 2 * d + 1 + 1)
      (hA.vanish (p + 2 * d + 1 + 1) (by omega))
  have hV : IsZero (Hmod2 (TopCat.of
      ↥((prodOpen A (punctOpen d) : Opens (A × CP (d + 1))) : Set (A × CP (d + 1))))
      (p + 2 * d + 1)) :=
    isZero_prodOpen_of_homotopyEquiv A (punctOpen d) (punctOpenHomotopyEquiv d)
      (p + 2 * d + 1) ((kunnethFactor_CP d).prod A p hA.vanish (p + 2 * d + 1) (by omega))
  have hV' : IsZero (Hmod2 (TopCat.of
      ↥((prodOpen A (punctOpen d) : Opens (A × CP (d + 1))) : Set (A × CP (d + 1))))
      (p + 2 * d + 1 + 1)) :=
    isZero_prodOpen_of_homotopyEquiv A (punctOpen d) (punctOpenHomotopyEquiv d)
      (p + 2 * d + 1 + 1)
      ((kunnethFactor_CP d).prod A p hA.vanish (p + 2 * d + 1 + 1) (by omega))
  exact (prodCoverConnecting A (Y := CP (d + 1)) (chartOpen d) (punctOpen d)
    (chartOpen_sup_punctOpen d) (interSphereHomotopyEquiv d) (p + 2 * d + 1)
    hU hV hU' hV').symm.trans l

/-- **The projective induction.**  Given the circle step, crossing with `ℂP^d`
raises the top degree by `2d`. -/
theorem hasTopLine_prod_CP (hcirc : CircleTopLineStep) (A : Type) [TopologicalSpace A]
    (p : ℕ) (hA : HasTopLine A p) : ∀ d, 1 ≤ d → HasTopLine (A × CP d) (p + 2 * d) := by
  intro d
  induction d with
  | zero => intro hd; exact absurd hd (by omega)
  | succ d _ih =>
      intro _
      exact hasTopLine_prod_CP_succ A p d hA
        (hasTopLine_prod_sphere hcirc A p hA (2 * d + 1) (by omega))

end

end GroupApproximation.CharClass

import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefect
import GroupApproximation.Sofic.OpToHSShadowResidual
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Data.Set.Finite.Lattice

/-!
# `K₂(V)` and the shadow residual `R_{∞→2}(G)`

`non_mf_groups_exist.tex`, Section~3 (`eq:shadow-residual`) and
Corollary~`cor:defect-hs`.

The manuscript attaches to an operator-norm asymptotic representation `(V_n)`
of `G` the set

`K₂(V) = {g : ‖V_n(g) - 1‖₂ → 0}`,

where the convergence is **ordinary** convergence of a sequence of reals, and
then defines the shadow residual as the intersection `R_{∞→2}(G) = ⋂_V K₂(V)`
over all such `V`.

The development already carries the residual, but through a different route:
`GroupApproximation.opToHSShadowResidual` quantifies over every
`OpAlmostRepresentation` **and** over every ultrafilter `U ≤ cofinite`, and
asks that the induced homomorphism into the Hilbert--Schmidt metric
ultraproduct kill the element.  This module supplies the missing printed
object and the bridge between the two readings:

* `IsHSNull B g` is the manuscript's ordinary convergence, spelled out;
* `isHSNull_iff_tendsto` identifies it with `Tendsto … atTop (nhds 0)` for the
  unsquared normalized Hilbert--Schmidt displacement `‖V_n(g) - 1‖₂`;
* `isHSNull_iff_forall_ultrafilter` is the bridge, and it is an equivalence:
  a nonnegative real sequence vanishes ordinarily exactly when it vanishes
  along every ultrafilter refining the cofinite filter.  The nontrivial
  direction builds an ultrafilter containing the (necessarily infinite) set of
  indices at which the sequence stays large;
* `hsKernel B` is `K₂(V)` as a subgroup, and it is normal;
* `opToHSShadowResidual_eq_iInf_hsKernel` is `eq:shadow-residual` itself.

The second half of the module places the printed compression--centralizer
defect inside the residual.  That is `cor:defect-hs` together with the
normality of the residual, and it goes through the development's own
`KazhdanAsymptoticCommutant.compressionCentralizerDefect_eq_one_in_hyperlinearHom`,
which already kills the *whole* defect subgroup in every Hilbert--Schmidt
ultraproduct.  The containment is therefore proved for the development's
larger defect first and then restricted to the printed one along
`printedDefect_le_compressionCentralizerDefect`.

Every manuscript-facing statement is a named closed `Prop` with all binders
inside, so `#audit_closed_axioms` accepts it.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

/-! ## `K₂(V)`: ordinary Hilbert--Schmidt vanishing -/

section HSKernel

variable {G : Type} [Group G]

/-- **The membership condition of `K₂(V)`.**  The normalized Hilbert--Schmidt
displacement of `V_n(g)` from the identity tends to zero in the ordinary sense
of sequences, i.e. along `atTop` and not merely along some ultrafilter.

`hsLengthSq Y u` is `‖u - 1‖₂²`, so this is literally `‖V_n(g) - 1‖₂ → 0`;
`isHSNull_iff_tendsto` records the unsquared form. -/
def IsHSNull (B : OpAlmostRepresentation G) (g : G) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    hsLengthSq (B.model n) ((B.map n g : Matrix (B.model n) (B.model n) ℂ)) < ε

/-- The printed form of the defining condition of `K₂(V)`: the sequence of
normalized Hilbert--Schmidt displacements `‖V_n(g) - 1‖₂` converges to `0`. -/
theorem isHSNull_iff_tendsto (B : OpAlmostRepresentation G) (g : G) :
    IsHSNull B g ↔
      Filter.Tendsto
        (fun n ↦ Real.sqrt (hsLengthSq (B.model n)
          ((B.map n g : Matrix (B.model n) (B.model n) ℂ))))
        Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h (ε * ε) (mul_pos hε hε)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hlt := hN n hn
    have hnn := hsLengthSq_nonneg (B.model n)
      ((B.map n g : Matrix (B.model n) (B.model n) ℂ))
    have hsq := Real.sq_sqrt hnn
    have hs := Real.sqrt_nonneg (hsLengthSq (B.model n)
      ((B.map n g : Matrix (B.model n) (B.model n) ℂ)))
    show dist (Real.sqrt (hsLengthSq (B.model n)
      ((B.map n g : Matrix (B.model n) (B.model n) ℂ)))) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [hlt, hsq, hs, hε]
  · intro h ε hε
    obtain ⟨N, hN⟩ := h (Real.sqrt ε) (Real.sqrt_pos.2 hε)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hd : dist (Real.sqrt (hsLengthSq (B.model n)
        ((B.map n g : Matrix (B.model n) (B.model n) ℂ)))) (0 : ℝ) <
          Real.sqrt ε := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.sqrt_nonneg _)] at hd
    have hnn := hsLengthSq_nonneg (B.model n)
      ((B.map n g : Matrix (B.model n) (B.model n) ℂ))
    have hsq := Real.sq_sqrt hnn
    have hse := Real.sq_sqrt hε.le
    have hs := Real.sqrt_nonneg (hsLengthSq (B.model n)
      ((B.map n g : Matrix (B.model n) (B.model n) ℂ)))
    have hes := Real.sqrt_nonneg ε
    nlinarith [hd, hsq, hse, hs, hes]

/-- **The bridge between the printed `K₂(V)` and the development's residual.**
A nonnegative sequence vanishes ordinarily exactly when it vanishes along
every ultrafilter refining the cofinite filter.

The easy direction is `eventually_of_atTop`.  For the other direction, if the
sequence stays `≥ ε` infinitely often, the trace of the cofinite filter on
that index set is proper, and any ultrafilter refining it witnesses a failure
of ultraproduct triviality. -/
theorem isHSNull_iff_forall_ultrafilter (B : OpAlmostRepresentation G) (g : G) :
    IsHSNull B g ↔
      ∀ (U : Ultrafilter ℕ) (hcof : (U : Filter ℕ) ≤ Filter.cofinite),
        (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
          hcof g = 1 := by
  classical
  constructor
  · intro h U hcof
    let S := KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B
    have hnull : (fun n ↦ S.map n g) ∈
        nullUnitarySubgroup U S.model S.modelNonempty := by
      intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      refine eventually_of_atTop hcof N (fun n hn ↦ ?_)
      exact hN n hn
    change QuotientGroup.mk (fun n ↦ S.map n g) = 1
    exact (@QuotientGroup.eq_one_iff _ _
      (nullUnitarySubgroup U S.model S.modelNonempty) _ (fun n ↦ S.map n g)).2 hnull
  · intro h ε hε
    by_contra hcon
    push_neg at hcon
    set T : Set ℕ :=
      {n : ℕ | ε ≤ hsLengthSq (B.model n)
        ((B.map n g : Matrix (B.model n) (B.model n) ℂ))}
    have key : ∀ V ∈ (Filter.cofinite : Filter ℕ), (V ∩ T).Nonempty := by
      intro V hV
      obtain ⟨M, hM⟩ := (Filter.mem_cofinite.mp hV).bddAbove
      obtain ⟨n, hn, hnT⟩ := hcon (M + 1)
      refine ⟨n, ?_, hnT⟩
      by_contra hnV
      have hle : n ≤ M := hM (show n ∈ Vᶜ from hnV)
      omega
    haveI : (Filter.cofinite ⊓ Filter.principal T : Filter ℕ).NeBot :=
      Filter.inf_principal_neBot_iff.mpr key
    obtain ⟨U, hcof, hTU⟩ :
        ∃ U : Ultrafilter ℕ,
          (U : Filter ℕ) ≤ Filter.cofinite ∧ T ∈ (U : Filter ℕ) := by
      refine ⟨Ultrafilter.of (Filter.cofinite ⊓ Filter.principal T), ?_, ?_⟩
      · exact le_trans (Ultrafilter.of_le _) inf_le_left
      · exact Ultrafilter.of_le _
          (Filter.mem_inf_of_right (Filter.mem_principal_self _))
    have hkill := h U hcof
    let S := KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B
    have hmk : (QuotientGroup.mk (fun n ↦ S.map n g) :
        UniversalHyperlinear U S.model S.modelNonempty) = 1 := hkill
    have hnull : (fun n ↦ S.map n g) ∈
        nullUnitarySubgroup U S.model S.modelNonempty :=
      (@QuotientGroup.eq_one_iff _ _
        (nullUnitarySubgroup U S.model S.modelNonempty) _
        (fun n ↦ S.map n g)).1 hmk
    have hnull' : IsNullUnitarySeq U S.model (fun n ↦ S.map n g) := hnull
    have hev : ∀ᶠ n in (U : Filter ℕ),
        hsLengthSq (B.model n)
          ((B.map n g : Matrix (B.model n) (B.model n) ℂ)) < ε := hnull' ε hε
    have hcontra : ∀ᶠ _n in (U : Filter ℕ), False := by
      filter_upwards [hev, hTU] with n h1 h2
      have h2' : ε ≤ hsLengthSq (B.model n)
        ((B.map n g : Matrix (B.model n) (B.model n) ℂ)) := h2
      exact absurd h1 (not_lt.mpr h2')
    obtain ⟨_, hfalse⟩ := hcontra.exists
    exact hfalse

/-- **`K₂(V)` as a subgroup.**  Closure under the group operations is not
proved directly from the operator-norm defects: it is transported from the
ultraproduct description supplied by `isHSNull_iff_forall_ultrafilter`, where
the condition is membership in the kernel of a homomorphism. -/
def hsKernel (B : OpAlmostRepresentation G) : Subgroup G where
  carrier := {g | IsHSNull B g}
  one_mem' := by
    show IsHSNull B 1
    exact (isHSNull_iff_forall_ultrafilter B 1).mpr fun _ _ ↦ map_one _
  mul_mem' := by
    intro x y hx hy
    have hx0 : IsHSNull B x := hx
    have hy0 : IsHSNull B y := hy
    have hx1 := (isHSNull_iff_forall_ultrafilter B x).mp hx0
    have hy1 := (isHSNull_iff_forall_ultrafilter B y).mp hy0
    show IsHSNull B (x * y)
    refine (isHSNull_iff_forall_ultrafilter B (x * y)).mpr ?_
    intro U hcof
    rw [map_mul, hx1 U hcof, hy1 U hcof, mul_one]
  inv_mem' := by
    intro x hx
    have hx0 : IsHSNull B x := hx
    have hx1 := (isHSNull_iff_forall_ultrafilter B x).mp hx0
    show IsHSNull B x⁻¹
    refine (isHSNull_iff_forall_ultrafilter B x⁻¹).mpr ?_
    intro U hcof
    rw [map_inv, hx1 U hcof, inv_one]

/-- Membership in `K₂(V)` is the printed convergence condition. -/
theorem mem_hsKernel_iff (B : OpAlmostRepresentation G) (g : G) :
    g ∈ hsKernel B ↔ IsHSNull B g := Iff.rfl

/-- Membership in `K₂(V)` in the form the development's residual consumes. -/
theorem mem_hsKernel_iff_forall_ultrafilter (B : OpAlmostRepresentation G)
    (g : G) :
    g ∈ hsKernel B ↔
      ∀ (U : Ultrafilter ℕ) (hcof : (U : Filter ℕ) ≤ Filter.cofinite),
        (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
          hcof g = 1 :=
  isHSNull_iff_forall_ultrafilter B g

/-- `K₂(V)` is normal, as asserted in Section~3.  The operator-norm defects
tend to zero in normalized Hilbert--Schmidt norm as well, which is exactly
what makes the ultraproduct description a kernel. -/
instance hsKernel_normal (B : OpAlmostRepresentation G) :
    (hsKernel B).Normal := by
  constructor
  intro x hx g
  rw [mem_hsKernel_iff_forall_ultrafilter] at hx ⊢
  intro U hcof
  rw [map_mul, map_mul, map_inv, hx U hcof]
  group

/-- The development's shadow residual is the printed intersection
`⋂_V K₂(V)`, elementwise. -/
theorem mem_opToHSShadowResidual_iff_forall_hsKernel (x : G) :
    x ∈ opToHSShadowResidual G ↔
      ∀ B : OpAlmostRepresentation G, x ∈ hsKernel B := by
  rw [mem_opToHSShadowResidual_iff]
  constructor
  · intro h B
    rw [mem_hsKernel_iff_forall_ultrafilter]
    intro U hcof
    exact h B U hcof
  · intro h B U hcof
    exact (mem_hsKernel_iff_forall_ultrafilter B x).mp (h B) U hcof

/-- **`eq:shadow-residual`.**  `R_{∞→2}(G) = ⋂_V K₂(V)`. -/
theorem opToHSShadowResidual_eq_iInf_hsKernel :
    opToHSShadowResidual G = ⨅ B : OpAlmostRepresentation G, hsKernel B := by
  ext x
  rw [Subgroup.mem_iInf]
  exact mem_opToHSShadowResidual_iff_forall_hsKernel x

end HSKernel

/-! ## `cor:defect-hs`: the compression defect is universally invisible -/

section DefectContainment

/-- **`cor:defect-hs`, in subgroup form, for the development's defect.**  The
whole compression--centralizer defect of a property-`(T)` image sits inside
the shadow residual.  Every generator `[u c u⁻¹, ℓ]` is killed in every
Hilbert--Schmidt ultraproduct, and the residual is normal, so the normal
closure follows. -/
theorem compressionCentralizerDefect_le_opToHSShadowResidual
    {Gamma G : Type} [Group Gamma] [Group G] (iota : Gamma →* G)
    (hT : HasKazhdanPropertyT.{0, 0} Gamma) :
    compressionCentralizerDefect iota.range ≤ opToHSShadowResidual G := by
  intro x hx
  rw [mem_opToHSShadowResidual_iff]
  intro B U hcof
  exact MonoidHom.mem_ker.mp
    (KazhdanAsymptoticCommutant.compressionCentralizerDefect_eq_one_in_hyperlinearHom
      B iota hT hcof hx)

/-- **`cor:defect-hs` on the printed defect.**  `𝔇_G(L) ≤ R_{∞→2}(G)` for the
manuscript's `𝔇_G(L)`, whose compressors range over the *set* `Comp_G(L)`
rather than over the group it generates. -/
theorem printedDefect_le_opToHSShadowResidual {G : Type} [Group G]
    (L : Subgroup G) (hT : HasKazhdanPropertyT.{0, 0} ↥L) :
    printedDefect L ≤ opToHSShadowResidual G := by
  have h := compressionCentralizerDefect_le_opToHSShadowResidual L.subtype hT
  rw [L.range_subtype] at h
  exact (printedDefect_le_compressionCentralizerDefect L).trans h

end DefectContainment

/-! ## Manuscript-facing endpoints -/

/-- **Section~3's definition of `K₂(V)` together with `eq:shadow-residual`.**
Membership in `K₂(V)` is ordinary convergence `‖V_n(g) - 1‖₂ → 0`; `K₂(V)` is a
normal subgroup; and the shadow residual is the intersection of the `K₂(V)`
over all operator-norm asymptotic representations. -/
def ShadowResidualIsIntersectionOfHSKernels : Prop :=
  ∀ (G : Type) [Group G],
    (∀ (B : OpAlmostRepresentation G) (g : G),
        g ∈ hsKernel B ↔
          Filter.Tendsto
            (fun n ↦ Real.sqrt (hsLengthSq (B.model n)
              ((B.map n g : Matrix (B.model n) (B.model n) ℂ))))
            Filter.atTop (nhds 0)) ∧
      (∀ B : OpAlmostRepresentation G, (hsKernel B).Normal) ∧
      (∀ x : G, x ∈ opToHSShadowResidual G ↔
        ∀ B : OpAlmostRepresentation G, x ∈ hsKernel B)

/-- Closed proof of the manuscript's shadow-residual definition. -/
theorem manuscriptShadowResidualIsIntersectionOfHSKernels :
    ShadowResidualIsIntersectionOfHSKernels := by
  intro G _
  refine ⟨fun B g ↦ (mem_hsKernel_iff B g).trans (isHSNull_iff_tendsto B g),
    fun B ↦ hsKernel_normal B, fun x ↦ ?_⟩
  exact mem_opToHSShadowResidual_iff_forall_hsKernel x

/-- **Normality of `R_{∞→2}(G)`**, as asserted after `eq:shadow-residual`,
together with the strictly stronger full invariance the development proves:
the residual is carried into itself by *every* endomorphism, not only by the
inner ones. -/
def ShadowResidualIsNormal : Prop :=
  ∀ (G : Type) [Group G],
    (opToHSShadowResidual G).Normal ∧
      ∀ f : G →* G, (opToHSShadowResidual G).map f ≤ opToHSShadowResidual G

/-- Closed proof of normality and full invariance of the shadow residual. -/
theorem manuscriptShadowResidualIsNormal : ShadowResidualIsNormal := by
  intro G _
  exact ⟨opToHSShadowResidual_normal, opToHSShadowResidual_isFullyInvariant G⟩

/-- **One universally Hilbert--Schmidt trivial word drags its whole normal
closure into the residual.**  This is the form in which normality of
`R_{∞→2}(G)` is used in Section~4. -/
def ShadowResidualCoversNormalClosure : Prop :=
  ∀ (G : Type) [Group G] (w : G),
    w ∈ opToHSShadowResidual G →
      Subgroup.normalClosure ({w} : Set G) ≤ opToHSShadowResidual G

/-- Closed proof that the shadow residual absorbs normal closures. -/
theorem manuscriptShadowResidualCoversNormalClosure :
    ShadowResidualCoversNormalClosure := by
  intro G _ w hw
  exact normalClosure_le_opToHSShadowResidual hw

/-- **`Rad_MF(G) ≤ R_{∞→2}(G)`.**  Operator-norm MF invisibility implies
normalized Hilbert--Schmidt invisibility, since `‖X‖₂ ≤ ‖X‖`.  Both the
manuscript's literal natural-dimension radical and the basis-free
genuine-corona radical are covered. -/
def MFResidualLeShadowResidual : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    manuscriptCoronaMFResidual G ≤ opToHSShadowResidual G ∧
      actualCoronaMFResidual G ≤ opToHSShadowResidual G

/-- Closed proof that the MF radical is contained in the shadow residual. -/
theorem manuscriptMFResidualLeShadowResidual : MFResidualLeShadowResidual := by
  intro G _ _
  have h : actualCoronaMFResidual G ≤ opToHSShadowResidual G := by
    rw [actualCoronaMFResidual_eq_coronaMFResidual,
      coronaMFResidual_eq_normMFResidual]
    exact normMFResidual_le_opToHSShadowResidual
  refine ⟨?_, h⟩
  rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
  exact h

/-- **Corollary `cor:defect-hs`, as printed.**  For a property-`(T)` subgroup
`L`, the whole printed compression--centralizer defect `𝔇_G(L)` lies in the
shadow residual `R_{∞→2}(G)`. -/
def PrintedDefectLeShadowResidual : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
      printedDefect L ≤ opToHSShadowResidual G

/-- Closed proof of `cor:defect-hs` on the printed defect subgroup. -/
theorem manuscriptPrintedDefectLeShadowResidual :
    PrintedDefectLeShadowResidual := by
  intro G _ L hT
  exact printedDefect_le_opToHSShadowResidual L hT

end OneSidedMFRadical
end Manuscript
end GroupApproximation

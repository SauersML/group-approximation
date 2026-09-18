import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegKernel
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVarTransport
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Meta.AxiomGuard

/-!
# Degree reduction for `K₂(F_p[X])`, part 4: the constants and the parabolic agree

Lane `bh-met-91c`.  Notation of `ElemFPK2PolyDegSpans`.  Put `ev = C ∘ ev₀ : F[X] → F[X]`, the
retraction onto the constants.  Main result (`k2PolyDeg_eq_of_const_of_mem_P`): if both the
constants `C(St_I(F_p))` and the parabolic `P` meet `K₂` trivially, then an element `a` of the
constants and an element `b ∈ P` with the same matrix are equal.

Truth check (paper).  `ev` fixes the constants.  It also maps `P` into `P`: it fixes the torus,
which is constant, and preserves every root span.  Now `b` and `ev b` both lie in `P`, and
`π(ev b) = ev(π b) = ev(π a) = π(ev a) = π a = π b`.  So `(ev b)⁻¹ b ∈ P ∩ K₂ = 1`, and
`b = ev b = C(ev₀ b)` is constant.  Then `a⁻¹ b` is a constant element of `K₂`, hence `1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (h)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  x_mem_rootSpan rootSpan_induction)

section Ring

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A ring map sends a root span into the root span of the same shape. -/
theorem k2PolyDeg_ringMap_mem_rootSpan {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    {q : I → I → Prop} {g : SteinbergGroup I R} (hg : g ∈ rootSpan (R := R) q) :
    ringMap f g ∈ rootSpan (R := S) q :=
  rootSpan_induction (Q := fun g => ringMap f g ∈ rootSpan (R := S) q)
    (fun i j hij a hq => show ringMap f (x i j hij a) ∈ rootSpan (R := S) q by
      rw [ringMap_x]
      exact x_mem_rootSpan hij (f a) hq)
    (show ringMap f 1 ∈ rootSpan (R := S) q by
      rw [map_one]
      exact Subgroup.one_mem _)
    (fun g k _ _ hg hk => show ringMap f (g * k) ∈ rootSpan (R := S) q by
      rw [map_mul]
      exact Subgroup.mul_mem _ hg hk) hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_ringMap_mem_rootSpan

end Ring

section Ev

variable (F : Type*) [CommRing F]

/-- The retraction `ev = C ∘ ev₀` of `F[X]` onto the constants. -/
noncomputable def k2PolyDeg_ev : Polynomial F →+* Polynomial F :=
  Polynomial.C.comp (Polynomial.evalRingHom 0)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_ev

/-- `ev ∘ C = C`. -/
theorem k2PolyDeg_ev_comp_C : (k2PolyDeg_ev F).comp Polynomial.C = Polynomial.C := by
  rw [k2PolyDeg_ev, RingHom.comp_assoc, evalRingHom_zero_comp_C, RingHom.comp_id]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_ev_comp_C

variable {F}

/-- `ev` fixes the constants of the Steinberg group. -/
theorem k2PolyDeg_ev_ringMap_C {I : Type*} [Fintype I] [DecidableEq I]
    (y : SteinbergGroup I F) :
    ringMap (k2PolyDeg_ev F) (ringMap (Polynomial.C : F →+* Polynomial F) y) =
      ringMap (Polynomial.C : F →+* Polynomial F) y := by
  rw [ringMap_ringMap, k2PolyDeg_ev_comp_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_ev_ringMap_C

end Ev

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- `ev` maps the parabolic `P` into itself. -/
theorem k2PolyDeg_ev_mem_P {K : Finset I} {m L n : I} (hmL : m ≠ L) (hmn : m ≠ n)
    (hLn : L ≠ n) {g : SteinbergGroup I (Polynomial (ZMod p))}
    (hg : g ∈ k2PolyDeg_P p K m L n hmL hmn hLn) :
    ringMap (k2PolyDeg_ev (ZMod p)) g ∈ k2PolyDeg_P p K m L n hmL hmn hLn := by
  have hle : k2PolyDeg_P p K m L n hmL hmn hLn ≤
      (k2PolyDeg_P p K m L n hmL hmn hLn).comap (ringMap (k2PolyDeg_ev (ZMod p))) := by
    refine sup_le ?_ (sup_le ?_ ?_)
    · intro t ht
      obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp ht
      have e : ringMap (k2PolyDeg_ev (ZMod p)) (k2PolyDeg_torus p m L n hmL hmn hLn c) =
          k2PolyDeg_torus p m L n hmL hmn hLn c := k2PolyDeg_ev_ringMap_C (h m L hmL c)
      refine Subgroup.mem_comap.mpr ?_
      rw [e]
      exact Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨c, rfl⟩)
    · intro s hs
      exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_right (Subgroup.mem_sup_left
        (k2PolyDeg_ringMap_mem_rootSpan (k2PolyDeg_ev (ZMod p))
          (q := fun i j => i ∈ K ∧ j ∈ K) hs)))
    · intro v hv
      exact Subgroup.mem_comap.mpr (Subgroup.mem_sup_right (Subgroup.mem_sup_right
        (k2PolyDeg_ringMap_mem_rootSpan (k2PolyDeg_ev (ZMod p))
          (q := fun i j => i = L ∧ j ∈ K) hv)))
  exact hle hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_ev_mem_P

/-- **Constants lemma.** If the constants and `P` both meet `K₂` trivially, then a constant `a`
and an element `b ∈ P` with the same matrix are equal. -/
theorem k2PolyDeg_eq_of_const_of_mem_P {K : Finset I} {m L n : I} (hmL : m ≠ L)
    (hmn : m ≠ n) (hLn : L ≠ n)
    (hC : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    (hP : ∀ g ∈ k2PolyDeg_P p K m L n hmL hmn hLn, g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    {a b : SteinbergGroup I (Polynomial (ZMod p))}
    (ha : a ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range)
    (hb : b ∈ k2PolyDeg_P p K m L n hmL hmn hLn) (hab : projection a = projection b) :
    a = b := by
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp ha
  have hb' := k2PolyDeg_ev_mem_P hmL hmn hLn hb
  have hpb : projection (ringMap (k2PolyDeg_ev (ZMod p)) b) = projection b := by
    rw [projection_ringMap, ← hab, ← projection_ringMap, k2PolyDeg_ev_ringMap_C]
  have h1 := hP _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hb') hb)
    ((mem_K2_iff _).mpr (by rw [map_mul, map_inv, hpb, inv_mul_cancel]))
  have hbb : ringMap (k2PolyDeg_ev (ZMod p)) b = b := inv_mul_eq_one.mp h1
  have hbC : b ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range := by
    rw [← hbb]
    exact MonoidHom.mem_range.mpr ⟨ringMap (Polynomial.evalRingHom 0) b, ringMap_ringMap _ _ b⟩
  have h2 := hC _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hbC)
    ((mem_K2_iff _).mpr (by rw [map_mul, map_inv, ← hab, inv_mul_cancel]))
  exact inv_mul_eq_one.mp h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_eq_of_const_of_mem_P

end GroupApproximation.BooneHigman.Metabelian.ElemFP

import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPresElt
import GroupApproximation.Steinberg.Functoriality

/-!
# Functoriality of Tulenbaev's relative Steinberg group (k2-poly, H.L1)

For a ring map `f : A →+* B` with `f(𝔄) ⊆ 𝔅`, the generators `X_{v,w}` of `St(A, 𝔄)` go to
`X_{f v, f w}` of `St(B, 𝔅)`, and the relations (1.1)–(1.3) go to relations. This gives
`relMap f h𝔄 : St(A, 𝔄) →* St(B, 𝔅)` (`relMap_X`). If the elements `X(v, w)` over `A` and `B`
are natural in `f`, the canonical maps to `St(A)` and `St(B)` commute with `relMap` and `ringMap`
(`can_relMap`).

These are the maps in the commutative diagrams of Tulenbaev's Lemma 3.2 and Corollary 4.2.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks
namespace HL1

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Found
open GroupApproximation.BooneHigmanLinear.K2Found.RelPres
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (conjPair)

variable {I A B : Type*} [Fintype I] [DecidableEq I] [CommRing A] [CommRing B]

/-- `(v, w) ↦ (f ∘ v, f ∘ w)`. -/
abbrev mapPair (f : A →+* B) (p : (I → A) × (I → A)) : (I → B) × (I → B) :=
  (f ∘ p.1, f ∘ p.2)

theorem comp_mulVec (f : A →+* B) (M : Matrix I I A) (v : I → A) :
    (f ∘ (M *ᵥ v) : I → B) = M.map f *ᵥ (f ∘ v) :=
  funext fun i => RingHom.map_mulVec f M v i

theorem comp_single_one (f : A →+* B) (i : I) :
    (f ∘ (Pi.single i (1 : A) : I → A) : I → B) = Pi.single i 1 := by
  funext t
  by_cases h : t = i
  · rw [h, Function.comp_apply, Pi.single_eq_same, Pi.single_eq_same, map_one]
  · rw [Function.comp_apply, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

theorem isEColumn_map (f : A →+* B) {v : I → A} (hv : IsEColumn v) : IsEColumn (f ∘ v) := by
  obtain ⟨g, hg, i, rfl⟩ := hv
  refine ⟨elementaryMatrixUnitMap f g,
    elementaryGroup_map_le f (Subgroup.mem_map_of_mem _ hg), i, ?_⟩
  rw [comp_mulVec, comp_single_one]
  rfl

theorem rmem_map (f : A →+* B) {𝔄 : Ideal A} {𝔅 : Ideal B} (h𝔄 : 𝔄 ≤ 𝔅.comap f)
    {p : (I → A) × (I → A)} (hp : RMem 𝔄 p) : RMem 𝔅 (mapPair f p) := by
  refine ⟨isEColumn_map f hp.1, fun k => Ideal.mem_comap.1 (h𝔄 (hp.2.1 k)), ?_⟩
  change (f ∘ p.2) ⬝ᵥ (f ∘ p.1) = 0
  rw [← RingHom.map_dotProduct, hp.2.2, map_zero]

theorem mapPair_conjPair (f : A →+* B) (p q : (I → A) × (I → A)) :
    mapPair f (conjPair p q) = conjPair (mapPair f p) (mapPair f q) := by
  have h1 : f (p.2 ⬝ᵥ q.1) = (f ∘ p.2) ⬝ᵥ (f ∘ q.1) := RingHom.map_dotProduct f p.2 q.1
  have h2 : f (q.2 ⬝ᵥ p.1) = (f ∘ q.2) ⬝ᵥ (f ∘ p.1) := RingHom.map_dotProduct f q.2 p.1
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · show f (q.1 k + (p.2 ⬝ᵥ q.1) * p.1 k) = f (q.1 k) + ((f ∘ p.2) ⬝ᵥ (f ∘ q.1)) * f (p.1 k)
    rw [map_add, map_mul, h1]
  · show f (q.2 k - (q.2 ⬝ᵥ p.1) * p.2 k) = f (q.2 k) - ((f ∘ q.2) ⬝ᵥ (f ∘ p.1)) * f (p.2 k)
    rw [map_sub, map_mul, h2]

/-- **Functoriality.** `St(A, 𝔄) →* St(B, 𝔅)`, `X_{v,w} ↦ X_{f v, f w}`, when `f(𝔄) ⊆ 𝔅`. -/
noncomputable def relMap (f : A →+* B) {𝔄 : Ideal A} {𝔅 : Ideal B} (h𝔄 : 𝔄 ≤ 𝔅.comap f) :
    RelSt I A 𝔄 →* RelSt I B 𝔅 :=
  PresentedGroup.toGroup (f := fun g : RGen I A 𝔄 => X (mapPair f g.1) (rmem_map f h𝔄 g.2)) (by
    intro r hr
    change IsRel 𝔄 r at hr
    cases hr with
    | add v w w' h₁ h₂ h₃ =>
        simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
        rw [mul_inv_eq_one]
        have e : mapPair f (v, w + w') = (f ∘ v, f ∘ w + f ∘ w') :=
          Prod.ext rfl (funext fun k => map_add f (w k) (w' k))
        have k₃ : RMem 𝔅 (f ∘ v, f ∘ w + f ∘ w') := by
          rw [← e]
          exact rmem_map f h𝔄 h₃
        exact (X_add (f ∘ v) (f ∘ w) (f ∘ w') (rmem_map f h𝔄 h₁) (rmem_map f h𝔄 h₂) k₃).trans
          (X_congr e.symm k₃ (rmem_map f h𝔄 h₃))
    | conj p q hp hq hc =>
        simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
        rw [mul_inv_eq_one]
        have k : RMem 𝔅 (conjPair (mapPair f p) (mapPair f q)) := by
          rw [← mapPair_conjPair]
          exact rmem_map f h𝔄 hc
        exact (X_conj (mapPair f p) (mapPair f q) (rmem_map f h𝔄 hp) (rmem_map f h𝔄 hq) k).trans
          (X_congr (mapPair_conjPair f p q).symm k (rmem_map f h𝔄 hc))
    | frame v v' w u b hu hu' hw h₁ h₂ h₃ =>
        simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
        rw [mul_inv_eq_one]
        have e1 : mapPair f (b • v + v', w) = (f b • (f ∘ v) + f ∘ v', f ∘ w) := by
          refine Prod.ext (funext fun k => ?_) rfl
          show f (b * v k + v' k) = f b * f (v k) + f (v' k)
          rw [map_add, map_mul]
        have e2 : mapPair f (v, b • w) = (f ∘ v, f b • (f ∘ w)) := by
          refine Prod.ext rfl (funext fun k => ?_)
          show f (b * w k) = f b * f (w k)
          rw [map_mul]
        have hu₂ : (f ∘ u) ⬝ᵥ (f ∘ v) = 0 := by rw [← RingHom.map_dotProduct, hu, map_zero]
        have hu₂' : (f ∘ u) ⬝ᵥ (f ∘ v') = 1 := by rw [← RingHom.map_dotProduct, hu', map_one]
        have hw₂ : (f ∘ w) ⬝ᵥ (f ∘ v) = 0 := by rw [← RingHom.map_dotProduct, hw, map_zero]
        have k₁ : RMem 𝔅 (f b • (f ∘ v) + f ∘ v', f ∘ w) := by
          rw [← e1]
          exact rmem_map f h𝔄 h₁
        have k₂ : RMem 𝔅 (f ∘ v, f b • (f ∘ w)) := by
          rw [← e2]
          exact rmem_map f h𝔄 h₂
        exact (X_congr e1 (rmem_map f h𝔄 h₁) k₁).trans
          ((X_frame (f ∘ v) (f ∘ v') (f ∘ w) (f ∘ u) (f b) hu₂ hu₂' hw₂ k₁ k₂
            (rmem_map f h𝔄 h₃)).trans
            (congrArg (· * X (f ∘ v', f ∘ w) (rmem_map f h𝔄 h₃))
              (X_congr e2.symm k₂ (rmem_map f h𝔄 h₂)))))

theorem relMap_X (f : A →+* B) {𝔄 : Ideal A} {𝔅 : Ideal B} (h𝔄 : 𝔄 ≤ 𝔅.comap f)
    (p : (I → A) × (I → A)) (hp : RMem 𝔄 p) :
    relMap f h𝔄 (X p hp) = X (mapPair f p) (rmem_map f h𝔄 hp) :=
  PresentedGroup.toGroup.of _

/-- **Naturality of the canonical maps.** If the elements `X(v, w)` over `A` and `B` are natural
in `f`, then `can ∘ relMap f = ringMap f ∘ can`. -/
theorem can_relMap (hA : VdK.Elements I A) (hB : VdK.Elements I B) (f : A →+* B)
    {𝔄 : Ideal A} {𝔅 : Ideal B} (h𝔄 : 𝔄 ≤ 𝔅.comap f)
    (hnat : ∀ (p : (I → A) × (I → A)) (hp : p ∈ VdK.U I A) (hp' : mapPair f p ∈ VdK.U I B),
      ringMap f (hA.elt p hp) = hB.elt (mapPair f p) hp') :
    (can hB 𝔅).comp (relMap f h𝔄) = (ringMap f).comp (can hA 𝔄) := by
  apply PresentedGroup.ext
  rintro ⟨p, hp⟩
  change can hB 𝔅 (relMap f h𝔄 (X p hp)) = ringMap f (can hA 𝔄 (X p hp))
  rw [relMap_X, can_X, can_X]
  exact (hnat p _ _).symm

#audit_axioms can_relMap

end HL1
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation

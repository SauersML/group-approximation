import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSuperperfect.Superperfect
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStability.Lifts

/-!
# `hsp` from relative perfectness of `K₂(n, L)`

Step 3 of the stability route for leaf T1b.iii (`simple_kazhdan_sofic_group.tex`, l.733-735,
`sec:questions`, binder `hsp`; Khanh, arXiv:2609.08428, proof of Prop. 3.2).

* `isSuperperfect_of_ker_le_relCommutator`: if `π : St_n(R) ↠ H`, `n ≥ 5`, satisfies
  `ker π ≤ ⁅St_n(R), ker π⁆`, then `H` is superperfect.  Indeed a perfect central extension
  `P : E ↠ H` receives a Kervaire lift `F : St_n(R) → E` of `π`; `F` kills `⁅St_n(R), ker π⁆`
  (its values on `ker π` are central), hence kills `ker π`, so it descends to a section of `P`.
* `gl_isSuperperfect_of_le_commutator`: for `L = L_k(1,2)` and `n ≥ 5`,
  `K₂(n, L) ≤ ⁅St_n(L), K₂(n, L)⁆` makes `GL_n(L)` superperfect.
* `binaryLeavittUnits_isSuperperfect_of_le_commutator`: over `𝔽₂` this gives `hsp` for `Lˣ`.
-/

namespace GroupApproximation
namespace Full
namespace LVStability

open SteinbergGroup

universe u

/-- If `π : St_n(R) ↠ H` with `n ≥ 5` has `ker π ≤ ⁅St_n(R), ker π⁆`, then `H` is
superperfect. -/
theorem isSuperperfect_of_ker_le_relCommutator {n : ℕ} (hn : 5 ≤ n) {R : Type*} [Ring R]
    {H : Type u} [Group H] (π : SteinbergGroup (Fin n) R →* H) (hπ : Function.Surjective π)
    (h : π.ker ≤ relCommutator π) : LVSuperperfect.IsSuperperfect H := by
  intro E _ P hE
  obtain ⟨F, hF⟩ := exists_lift_of_ker_le_center hn P.projection P.surjective
    P.ker_le_center π
  have hFx : ∀ x, P.projection (F x) = π x := fun x => DFunLike.congr_fun hF x
  have hle : relCommutator π ≤ F.ker := by
    refine commutator_ker_le_ker π F ?_
    intro x hx
    apply P.ker_le_center
    rw [MonoidHom.mem_ker, hFx x]
    exact MonoidHom.mem_ker.1 hx
  let s : H →* E := π.liftOfRightInverse (Function.surjInv hπ)
    (Function.rightInverse_surjInv hπ) ⟨F, h.trans hle⟩
  have hs : P.projection.comp s = MonoidHom.id H := by
    apply MonoidHom.ext
    intro g
    obtain ⟨x, rfl⟩ := hπ g
    have h1 : s (π x) = F x :=
      MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
        (Function.rightInverse_surjInv hπ) ⟨F, h.trans hle⟩ x
    change P.projection (s (π x)) = π x
    rw [h1]
    exact hFx x
  exact LVSuperperfect.projection_injective_of_section P s hs hE

section Leavitt

variable (k : Type) [Field k]

/-- For `L = L_k(1,2)` and `n ≥ 5`: `K₂(n, L) ≤ ⁅St_n(L), K₂(n, L)⁆` implies that `GL_n(L)`
is superperfect. -/
theorem gl_isSuperperfect_of_le_commutator {n : ℕ} (hn : 5 ≤ n)
    (h : (projection (I := Fin n) (R := BinaryLeavitt.BinaryLeavittAlgebra k)).ker ≤
      ⁅(⊤ : Subgroup (SteinbergGroup (Fin n) (BinaryLeavitt.BinaryLeavittAlgebra k))),
        (projection (I := Fin n) (R := BinaryLeavitt.BinaryLeavittAlgebra k)).ker⁆) :
    LVSuperperfect.IsSuperperfect
      ((Matrix (Fin n) (Fin n) (BinaryLeavitt.BinaryLeavittAlgebra k))ˣ) := by
  refine isSuperperfect_of_ker_le_relCommutator hn (LVEGen.steinbergToGL k n)
    (LVEGen.steinbergToGL_surjective k (by omega)) ?_
  show (LVEGen.steinbergToGL k n).ker ≤
    ⁅(⊤ : Subgroup (SteinbergGroup (Fin n) (BinaryLeavitt.BinaryLeavittAlgebra k))),
      (LVEGen.steinbergToGL k n).ker⁆
  rw [LVEGen.steinbergToGL_ker]
  exact h

end Leavitt

/-- **`hsp` from relative perfectness.**  If `K₂(n, L) ≤ ⁅St_n(L), K₂(n, L)⁆` for some
`n ≥ 5`, where `L = L_{𝔽₂}(1,2)`, then `Lˣ` is superperfect
(`simple_kazhdan_sofic_group.tex` l.733-735, binder `hsp`). -/
theorem binaryLeavittUnits_isSuperperfect_of_le_commutator {n : ℕ} (hn : 5 ≤ n)
    (h : (projection (I := Fin n) (R := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).ker ≤
      ⁅(⊤ : Subgroup (SteinbergGroup (Fin n) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))),
        (projection (I := Fin n) (R := BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).ker⁆) :
    LVSuperperfect.IsSuperperfect ((BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ) :=
  LVSuperperfect.binaryLeavittUnits_isSuperperfect_of_gl (r := n) (by omega)
    (gl_isSuperperfect_of_le_commutator (ZMod 2) hn h)

end LVStability
end Full
end GroupApproximation

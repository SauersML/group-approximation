import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindTen
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: cyclic list bookkeeping for lobes

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-70.

List facts behind `gfaceWindEleven_Statement` (file `GFaceWindEleven`). They read a lobe `W` of
the cyclic walk `c` as a prefix of a rotation `X₂ ++ X₁ = W ++ T` of `c = X₁ ++ X₂`.
* `gfaceWindEleven_rotate`: a rotation of a rotation is a rotation.
* `gfaceWindEleven_segLobe`: a simple closed stretch of a rotation of `c` is a lobe of `c`.
* `gfaceWindEleven_cycChain`: a rotation of a balanced chain walk is a chain walk
  (`gfaceWindSix_bal_iff`).
* `gfaceWindEleven_rest`: every lobe `W` with rest `R` has a rotation `W ++ T` of `c` with
  `T` and `R` having the same darts.

## Truth check

Pure list facts; no model check needed.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **A rotation of a rotation is a rotation.** -/
theorem gfaceWindEleven_rotate {α : Type*} {X₁ X₂ U V : List α} (h : X₂ ++ X₁ = U ++ V) :
    ∃ Y₁ Y₂ : List α, X₁ ++ X₂ = Y₁ ++ Y₂ ∧ Y₂ ++ Y₁ = V ++ U := by
  rcases List.append_eq_append_iff.mp h with ⟨a, rfl, rfl⟩ | ⟨b, rfl, rfl⟩
  · exact ⟨a, V ++ X₂, by simp only [List.append_assoc], by simp only [List.append_assoc]⟩
  · exact ⟨X₁ ++ U, b, by simp only [List.append_assoc], by simp only [List.append_assoc]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_rotate

/-- **A simple closed stretch of a rotation of `c` is a lobe of `c`.** -/
theorem gfaceWindEleven_segLobe {M : CombMap.{v}} {c X₁ X₂ P L S : List M.Dart}
    (hc : c = X₁ ++ X₂) (h : X₂ ++ X₁ = P ++ L ++ S) (hL : IsSimpleClosedWalk M L) :
    ∃ R : List M.Dart, gfaceWindEight_Lobe M c L R := by
  subst hc
  rw [List.append_assoc] at h
  rcases List.append_eq_append_iff.mp h with ⟨a, rfl, rfl⟩ | ⟨b, rfl, hb⟩
  · exact ⟨a ++ (S ++ X₂), a, L, S ++ X₂, by simp only [List.append_assoc],
      Or.inl ⟨hL, rfl, rfl⟩⟩
  · rcases List.append_eq_append_iff.mp hb with ⟨a, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
    · exact ⟨X₁ ++ P ++ a, X₁ ++ P, L, a, by simp only [List.append_assoc],
        Or.inl ⟨hL, rfl, rfl⟩⟩
    · exact ⟨S ++ P, e, S ++ P, b, by simp only [List.append_assoc],
        Or.inr ⟨hL, rfl, rfl⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_segLobe

/-- **A rotation of a balanced chain walk is a chain walk.** -/
theorem gfaceWindEleven_cycChain {M : CombMap.{v}} {X₁ X₂ : List M.Dart}
    (hch : (X₁ ++ X₂).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hbal : gfaceWindSix_Bal M (X₁ ++ X₂)) :
    (X₂ ++ X₁).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e := by
  rcases eq_or_ne X₁ [] with h1 | h1
  · subst h1
    rw [List.append_nil]
    rw [List.nil_append] at hch
    exact hch
  rcases eq_or_ne X₂ [] with h2 | h2
  · subst h2
    rw [List.nil_append]
    rw [List.append_nil] at hch
    exact hch
  have hne : X₁ ++ X₂ ≠ [] := List.append_ne_nil_of_left_ne_nil h1 X₂
  have hcl := (gfaceWindSix_bal_iff hne hch).mp hbal
  rw [List.getLast_append_of_ne_nil hne h2, List.head_append_of_ne_nil h1] at hcl
  refine List.IsChain.append hch.right_of_append hch.left_of_append ?_
  intro x hx y hy
  rw [List.getLast?_eq_getLast h2, Option.mem_def, Option.some_inj] at hx
  rw [List.head?_eq_head h1, Option.mem_def, Option.some_inj] at hy
  subst hx
  subst hy
  exact hcl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_cycChain

/-- **The rest of a lobe as the tail of a rotation**: `c = X₁ ++ X₂`, `X₂ ++ X₁ = W ++ T`, and
`T` has the darts of the rest `R`. -/
theorem gfaceWindEleven_rest {M : CombMap.{v}} {c W R : List M.Dart}
    (hl : gfaceWindEight_Lobe M c W R) :
    ∃ X₁ X₂ T : List M.Dart, c = X₁ ++ X₂ ∧ X₂ ++ X₁ = W ++ T ∧ ∀ x, x ∈ R ↔ x ∈ T := by
  obtain ⟨p, A, q, hc, ⟨-, hW, hR⟩ | ⟨-, hW, hR⟩⟩ := hl
  · refine ⟨p, A ++ q, q ++ p, by rw [hc, List.append_assoc], ?_, fun x => ?_⟩
    · rw [hW, List.append_assoc]
    · rw [hR]
      exact List.perm_append_comm.mem_iff
  · refine ⟨p ++ A, q, A, hc, ?_, fun x => ?_⟩
    · rw [hW, List.append_assoc]
    · rw [hR]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_rest

/-- **The head of a list lies in a nonempty prefix.** -/
theorem gfaceWindEleven_head_mem {α : Type*} {l s u : List α} (h : l ≠ []) (hl : l = s ++ u)
    (hs : s ≠ []) : l.head h ∈ s := by
  subst hl
  rw [List.head_append_of_ne_nil hs]
  exact List.head_mem hs

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_head_mem

/-- **The head of `a :: u`.** -/
theorem gfaceWindEleven_head_eq {α : Type*} {l u : List α} {a : α} (h : l ≠ [])
    (hl : l = a :: u) : l.head h = a := by
  subst hl
  rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_head_eq

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

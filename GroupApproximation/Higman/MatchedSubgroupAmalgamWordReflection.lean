import GroupApproximation.Higman.MatchedSubgroupAmalgam

/-!
# Carry traces for amalgam word normalization

Normalizing a reduced amalgam word transfers explicit edge elements from
right to left.  Recording those transfers gives the comparison theorem used
to reflect a reduced spelling from a matched sub-amalgam.
-/

namespace GroupApproximation

open Monoid

namespace MatchedSubgroupAmalgamWordReflection

universe uι uH uG

variable {ι : Type uι} {H : Type uH} {G : ι → Type uG}
  [Group H] [∀ i, Group (G i)]

/-- A right-to-left normalization trace.  The final carry is `1`; at each
letter the equation `g * φ tail = φ head * n` records the edge element
transferred across that letter. -/
inductive RightNormalizeTrace (φ : ∀ i, H →* G i) :
    List (Σ i, G i) → List (Σ i, G i) → H → Prop
  | nil : RightNormalizeTrace φ [] [] 1
  | cons (i : ι) (g n : G i) (raw normal : List (Σ i, G i))
      (head tail : H)
      (heq : g * φ i tail = φ i head * n)
      (htrace : RightNormalizeTrace φ raw normal tail) :
      RightNormalizeTrace φ
        (⟨i, g⟩ :: raw) (⟨i, n⟩ :: normal) head

/-- A right-to-left edge-carry comparison between two reduced spellings with
the same factor pattern. -/
inductive RightCarryComparison (φ : ∀ i, H →* G i) :
    List (Σ i, G i) → List (Σ i, G i) → H → Prop
  | nil : RightCarryComparison φ [] [] 1
  | cons (i : ι) (g s : G i) (raw small : List (Σ i, G i))
      (head tail : H)
      (heq : g * φ i tail = φ i head * s)
      (hcompare : RightCarryComparison φ raw small tail) :
      RightCarryComparison φ
        (⟨i, g⟩ :: raw) (⟨i, s⟩ :: small) head

/-- The normal-form construction for a reduced word, strengthened by the
complete finite carry trace relating its original and normalized letters. -/
theorem Reduced.exists_normalWord_prod_eq_with_trace
    (φ : ∀ i, H →* G i)
    (d : PushoutI.NormalWord.Transversal φ) :
    ∀ {w : CoprodI.Word G}, PushoutI.Reduced φ w →
      ∃ w' : PushoutI.NormalWord d,
        w'.prod = PushoutI.ofCoprodI w.prod ∧
        w'.toList.map Sigma.fst = w.toList.map Sigma.fst ∧
        RightNormalizeTrace φ w.toList w'.toList w'.head := by
  classical
  intro w hw
  induction w using CoprodI.Word.consRecOn with
  | empty =>
      refine ⟨PushoutI.NormalWord.empty, ?_, rfl, ?_⟩
      · simp [PushoutI.NormalWord.prod, CoprodI.Word.empty,
          CoprodI.Word.prod]
      exact RightNormalizeTrace.nil
  | @cons i g w hidx hg ih =>
      obtain ⟨w', hwprod, hwidx, hwtrace⟩ :=
        ih (fun l hl ↦ hw l (List.mem_cons_of_mem _ hl))
      let n := (d.compl i).equiv (g * φ i w'.head)
      let nw := PushoutI.NormalWord.cons g w' (by
        rwa [CoprodI.Word.fstIdx, ← List.head?_map, hwidx,
          List.head?_map]) (hw ⟨i, g⟩ List.mem_cons_self)
      refine ⟨nw, ?_, ?_, ?_⟩
      · change (PushoutI.NormalWord.cons g w' _ _).prod = _
        rw [PushoutI.NormalWord.prod_cons, hwprod]
        simp [CoprodI.Word.prod]
      · simp [nw, hwidx]
      · have hnprod : (n.1 : G i) * (n.2 : G i) =
            g * φ i w'.head :=
          (d.compl i).equiv_fst_mul_equiv_snd _
        have hnhead : nw.head =
            (MonoidHom.ofInjective (d.injective i)).symm n.1 := rfl
        have hphiHead : φ i nw.head = (n.1 : G i) := by
          rw [hnhead, MonoidHom.apply_ofInjective_symm]
        have hnlist : nw.toList =
            ⟨i, (n.2 : G i)⟩ :: w'.toList := rfl
        rw [hnlist]
        exact RightNormalizeTrace.cons i g (n.2 : G i)
          w.toList w'.toList nw.head w'.head
          (hnprod.symm.trans (by rw [hphiHead])) hwtrace

/-- Two normalization traces ending in the same normal word compose to an
explicit carry comparison between the original spellings. -/
theorem RightNormalizeTrace.compare
    (φ : ∀ i, H →* G i) :
    ∀ {raw small normal : List (Σ i, G i)} {a b : H},
      RightNormalizeTrace φ raw normal a →
      RightNormalizeTrace φ small normal b →
      RightCarryComparison φ raw small (a * b⁻¹) := by
  intro raw small normal a b hraw
  induction hraw generalizing small b with
  | nil =>
      intro hsmall
      cases hsmall
      simpa using RightCarryComparison.nil (φ := φ)
  | cons i g n raw normal head tail heq htrace ih =>
      intro hsmall
      cases hsmall with
      | cons _ s _ small _ _ btail hsmallEq hsmallTrace =>
          have htail := ih hsmallTrace
          have hsmallSolve : n =
              (φ i b)⁻¹ * s * φ i btail := by
            calc
              n = (φ i b)⁻¹ * (φ i b * n) := by group
              _ = (φ i b)⁻¹ * (s * φ i btail) := by rw [← hsmallEq]
              _ = (φ i b)⁻¹ * s * φ i btail := by group
          apply RightCarryComparison.cons i g s raw small
            (head * b⁻¹) (tail * btail⁻¹) _ htail
          calc
            g * φ i (tail * btail⁻¹) =
                (g * φ i tail) * (φ i btail)⁻¹ := by
              rw [map_mul, map_inv, mul_assoc]
            _ = (φ i head * n) * (φ i btail)⁻¹ := by rw [heq]
            _ = (φ i head *
                ((φ i b)⁻¹ * s * φ i btail)) *
                  (φ i btail)⁻¹ := by rw [hsmallSolve]
            _ = φ i (head * b⁻¹) * s := by
              rw [map_mul, map_inv]
              group

end MatchedSubgroupAmalgamWordReflection
end GroupApproximation

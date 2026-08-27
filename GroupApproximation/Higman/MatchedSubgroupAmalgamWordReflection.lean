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

/-- Equality of two base-prefixed reduced words produces an explicit carry
comparison.  The initial carry is the discrepancy between their displayed
base prefixes, and the terminal carry is `1`. -/
theorem Reduced.rightCarryComparison_of_eq
    (φ : ∀ i, H →* G i)
    (hφ : ∀ i, Function.Injective (φ i))
    {raw small : CoprodI.Word G}
    (hrawReduced : PushoutI.Reduced φ raw)
    (hsmallReduced : PushoutI.Reduced φ small)
    (rawHead smallHead : H)
    (heq : PushoutI.base φ rawHead * PushoutI.ofCoprodI raw.prod =
      PushoutI.base φ smallHead * PushoutI.ofCoprodI small.prod) :
    RightCarryComparison φ raw.toList small.toList
      (rawHead⁻¹ * smallHead) := by
  classical
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty φ hφ
  obtain ⟨rw, hrwprod, -, hrwtrace⟩ :=
    Reduced.exists_normalWord_prod_eq_with_trace φ d hrawReduced
  obtain ⟨sw, hswprod, -, hswtrace⟩ :=
    Reduced.exists_normalWord_prod_eq_with_trace φ d hsmallReduced
  have hnormal : rawHead • rw = smallHead • sw := by
    apply PushoutI.NormalWord.prod_injective
    rw [PushoutI.NormalWord.prod_base_smul,
      PushoutI.NormalWord.prod_base_smul, hrwprod, hswprod]
    exact heq
  have hheads : rawHead * rw.head = smallHead * sw.head := by
    exact congrArg PushoutI.NormalWord.head hnormal
  have hlists : rw.toList = sw.toList := by
    exact congrArg (fun w ↦ w.toList) hnormal
  rw [hlists] at hrwtrace
  have hcompare := hrwtrace.compare φ hswtrace
  have hcarry : rw.head * sw.head⁻¹ = rawHead⁻¹ * smallHead := by
    calc
      rw.head * sw.head⁻¹ =
          rawHead⁻¹ * (rawHead * rw.head) * sw.head⁻¹ := by group
      _ = rawHead⁻¹ * (smallHead * sw.head) * sw.head⁻¹ := by
        rw [hheads]
      _ = rawHead⁻¹ * smallHead := by group
  rwa [hcarry] at hcompare

/-! ## Matched sub-amalgam specialization -/

open Higman

variable {M₀ A B : Type}
  [Group M₀] [Group A] [Group B]

/-- If a base-prefixed reduced word lies in a matched sub-amalgam, it admits
a carry comparison with the factorwise image of a genuine word in the small
amalgam. -/
theorem Reduced.exists_rightCarryComparison_of_mem_matchedMap_range
    (eA : M₀ →* A) (eB : M₀ →* B)
    (Z : Subgroup A) (Q : Subgroup B) (Delta : Subgroup M₀)
    (heA : Function.Injective eA) (heB : Function.Injective eB)
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta)
    (raw : CoprodI.Word (Amalgam.fam A B))
    (hraw : PushoutI.Reduced (Amalgam.famHom eA eB) raw)
    (rawHead : M₀)
    (hmem : PushoutI.base (Amalgam.famHom eA eB) rawHead *
        PushoutI.ofCoprodI raw.prod ∈
      (Higman.MatchedSubgroupAmalgam.matchedMap
        eA eB Z Q Delta hZ hQ).range) :
    ∃ (d : PushoutI.NormalWord.Transversal
          (Higman.MatchedSubgroupAmalgam.smallEdge
            eA eB Z Q Delta hZ hQ))
      (w : PushoutI.NormalWord d),
      RightCarryComparison (Amalgam.famHom eA eB) raw.toList
        (PushoutEmbedding.wordMap
          (Higman.MatchedSubgroupAmalgam.factorInclusion Z Q)
          (fun i ↦ by cases i <;> exact Subtype.val_injective)
          w.toWord).toList
        (rawHead⁻¹ *
          Higman.MatchedSubgroupAmalgam.edgeInclusion Delta w.head) := by
  classical
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty
    (Higman.MatchedSubgroupAmalgam.smallEdge
      eA eB Z Q Delta hZ hQ)
    (Higman.MatchedSubgroupAmalgam.smallEdge_injective
      eA eB Z Q Delta heA heB hZ hQ)
  let w : PushoutI.NormalWord d := PushoutI.NormalWord.equiv y
  have hwprod : w.prod = y :=
    (PushoutI.NormalWord.equiv (d := d)).symm_apply_apply y
  let wm := PushoutEmbedding.wordMap
    (Higman.MatchedSubgroupAmalgam.factorInclusion Z Q)
    (fun i ↦ by cases i <;> exact Subtype.val_injective) w.toWord
  have hwred : PushoutI.Reduced
      (Higman.MatchedSubgroupAmalgam.smallEdge
        eA eB Z Q Delta hZ hQ) w.toWord :=
    PushoutEmbedding.normalWord_reduced _ d w
  have hwmred : PushoutI.Reduced (Amalgam.famHom eA eB) wm := by
    intro l hl
    obtain ⟨l', hl', heq⟩ := List.mem_map.mp hl
    cases heq
    exact fun hrange ↦ hwred l' hl'
      (Higman.MatchedSubgroupAmalgam.factorInclusion_reflects_range
        eA eB Z Q Delta hZ hQ l'.1 l'.2 hrange)
  have hprodImage :
      Higman.MatchedSubgroupAmalgam.matchedMap
          eA eB Z Q Delta hZ hQ w.prod =
        PushoutI.base (Amalgam.famHom eA eB)
            (Higman.MatchedSubgroupAmalgam.edgeInclusion Delta w.head) *
          PushoutI.ofCoprodI wm.prod := by
    rw [PushoutI.NormalWord.prod, map_mul,
      Higman.MatchedSubgroupAmalgam.matchedMap,
      PushoutBaseChange.map_base, PushoutBaseChange.map_ofCoprodI_prod]
  have heqProd : PushoutI.base (Amalgam.famHom eA eB) rawHead *
        PushoutI.ofCoprodI raw.prod =
      PushoutI.base (Amalgam.famHom eA eB)
          (Higman.MatchedSubgroupAmalgam.edgeInclusion Delta w.head) *
        PushoutI.ofCoprodI wm.prod := by
    rw [← hprodImage, hwprod, hy]
  refine ⟨d, w, ?_⟩
  exact Reduced.rightCarryComparison_of_eq
    (Amalgam.famHom eA eB)
    (Amalgam.famHom_injective eA eB heA heB)
    hraw hwmred rawHead
    (Higman.MatchedSubgroupAmalgam.edgeInclusion Delta w.head) heqProd

end MatchedSubgroupAmalgamWordReflection
end GroupApproximation

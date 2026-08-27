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

/-- Two carry comparisons of the same raw word against words in matched
factor subgroups have edge carries differing in the matched edge subgroup.
The induction runs from the common terminal carry `1`. -/
theorem RightCarryComparison.head_div_mem
    (φ : ∀ i, H →* G i)
    (S : ∀ i, Subgroup (G i)) (Delta : Subgroup H)
    (hcomap : ∀ i, (S i).comap (φ i) = Delta) :
    ∀ {raw small₁ small₂ : List (Σ i, G i)} {a b : H},
      RightCarryComparison φ raw small₁ a →
      RightCarryComparison φ raw small₂ b →
      (∀ l ∈ small₁, l.2 ∈ S l.1) →
      (∀ l ∈ small₂, l.2 ∈ S l.1) →
      a⁻¹ * b ∈ Delta := by
  intro raw small₁ small₂ a b h₁
  induction h₁ generalizing small₂ b with
  | nil =>
      intro h₂ _ _
      cases h₂
      simp
  | cons i g s₁ raw small₁ head₁ tail₁ heq₁ htail₁ ih =>
      intro h₂ hsmall₁ hsmall₂
      cases h₂ with
      | cons i₂ g₂ s₂ raw₂ small₂ head₂ tail₂ heq₂ htail₂ =>
          have htailDelta : tail₁⁻¹ * tail₂ ∈ Delta :=
            ih htail₂
              (fun l hl ↦ hsmall₁ l (List.mem_cons_of_mem _ hl))
              (fun l hl ↦ hsmall₂ l (List.mem_cons_of_mem _ hl))
          have hs₁ : s₁ ∈ S i := hsmall₁ _ List.mem_cons_self
          have hs₂ : s₂ ∈ S i := hsmall₂ _ List.mem_cons_self
          have htailImage : φ i (tail₁⁻¹ * tail₂) ∈ S i := by
            have : tail₁⁻¹ * tail₂ ∈ (S i).comap (φ i) := by
              rwa [hcomap i]
            exact this
          have hfactor : φ i (head₁⁻¹ * b) =
              s₁ * φ i (tail₁⁻¹ * tail₂) * s₂⁻¹ := by
            rw [map_mul, map_inv, map_mul, map_inv]
            have heq₁' : φ i head₁ * s₁ = g * φ i tail₁ := heq₁.symm
            have heq₂' : φ i b * s₂ = g * φ i tail₂ := heq₂.symm
            calc
              (φ i head₁)⁻¹ * φ i b =
                  (φ i head₁)⁻¹ * (φ i b * s₂) * s₂⁻¹ := by
                group
              _ = (φ i head₁)⁻¹ * (g * φ i tail₂) * s₂⁻¹ := by
                rw [heq₂']
              _ = (φ i head₁)⁻¹ *
                    (g * φ i tail₁) *
                    ((φ i tail₁)⁻¹ * φ i tail₂) * s₂⁻¹ := by
                group
              _ = (φ i head₁)⁻¹ *
                    (φ i head₁ * s₁) *
                    ((φ i tail₁)⁻¹ * φ i tail₂) * s₂⁻¹ := by
                rw [heq₁']
              _ = s₁ * ((φ i tail₁)⁻¹ * φ i tail₂) * s₂⁻¹ := by
                group
          rw [← hcomap i]
          change φ i (head₁⁻¹ * b) ∈ S i
          rw [hfactor]
          exact (S i).mul_mem ((S i).mul_mem hs₁ htailImage)
            ((S i).inv_mem hs₂)

/-- Expose the comparison equation and residual comparison at a prescribed
letter position in the raw word. -/
theorem RightCarryComparison.exists_at_append
    (φ : ∀ i, H →* G i) :
    ∀ {pre : List (Σ i, G i)} {i : ι} {g : G i}
      {rest small : List (Σ i, G i)} {head : H},
      RightCarryComparison φ (pre ++ ⟨i, g⟩ :: rest) small head →
      ∃ (smallPre : List (Σ i, G i)) (s : G i)
          (smallRest : List (Σ i, G i)) (current tail : H),
        small = smallPre ++ ⟨i, s⟩ :: smallRest ∧
        g * φ i tail = φ i current * s ∧
        RightCarryComparison φ rest smallRest tail := by
  intro pre
  induction pre with
  | nil =>
      intro i g rest small head hcompare
      cases hcompare with
      | cons j rawHead smallHead rawTail smallTail current tail heq htail =>
          exact ⟨[], smallHead, smallTail, head, tail, rfl, heq, htail⟩
  | cons p pre ih =>
      intro i g rest small head hcompare
      cases hcompare with
      | cons j rawHead smallHead rawTail smallTail current₀ tail₀ heq₀ htail₀ =>
          obtain ⟨smallPre, s, smallRest, current, tail,
            hsmall, heq, htail⟩ := ih htail₀
          refine ⟨⟨j, smallHead⟩ :: smallPre, s, smallRest, current, tail,
            ?_, heq, htail⟩
          simp [hsmall]

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

/-! ## Indexed matched subgroups -/

namespace IndexedMatched

variable {I : Type} {M : Type} {F : I → Type}
  [Group M] [∀ i, Group (F i)]

/-- The exact-comap restriction of an indexed edge map. -/
def smallEdge (phi : ∀ i, M →* F i) (S : ∀ i, Subgroup (F i))
    (Delta : Subgroup M) (hcomap : ∀ i, (S i).comap (phi i) = Delta) :
    ∀ i, Delta →* S i := fun i ↦
  ((phi i).comp Delta.subtype).codRestrict (S i) fun d ↦ by
    have hd : (d : M) ∈ (S i).comap (phi i) := by
      rw [hcomap i]
      exact d.property
    exact hd

/-- The factorwise subtype inclusion. -/
def factorInclusion (S : ∀ i, Subgroup (F i)) :
    ∀ i, S i →* F i := fun i ↦ (S i).subtype

theorem factorInclusion_commutes
    (phi : ∀ i, M →* F i) (S : ∀ i, Subgroup (F i))
    (Delta : Subgroup M) (hcomap : ∀ i, (S i).comap (phi i) = Delta) :
    ∀ i, ((factorInclusion S i).comp
        (smallEdge phi S Delta hcomap i)) =
      (phi i).comp Delta.subtype := by
  intro i
  rfl

/-- The indexed matched-subgroup map. -/
def matchedMap
    (phi : ∀ i, M →* F i) (S : ∀ i, Subgroup (F i))
    (Delta : Subgroup M) (hcomap : ∀ i, (S i).comap (phi i) = Delta) :
    PushoutI (smallEdge phi S Delta hcomap) →* PushoutI phi :=
  PushoutBaseChange.map
    (smallEdge phi S Delta hcomap) phi Delta.subtype
    (factorInclusion S)
    (factorInclusion_commutes phi S Delta hcomap)

/-- The literal factor generator set in the large indexed pushout. -/
def generatorSet (phi : ∀ i, M →* F i)
    (S : ∀ i, Subgroup (F i)) : Set (PushoutI phi) :=
  {x | ∃ i, ∃ s : S i, x = PushoutI.of (φ := phi) i s}

@[simp] theorem matchedMap_of
    (phi : ∀ i, M →* F i) (S : ∀ i, Subgroup (F i))
    (Delta : Subgroup M) (hcomap : ∀ i, (S i).comap (phi i) = Delta)
    (i : I) (s : S i) :
    matchedMap phi S Delta hcomap
        (PushoutI.of (φ := smallEdge phi S Delta hcomap) i s) =
      PushoutI.of (φ := phi) i (s : F i) := by
  exact PushoutBaseChange.map_of _ _ _ _ _ _ _

theorem matchedMap_range_eq_closure
    [Nonempty I]
    (phi : ∀ i, M →* F i) (S : ∀ i, Subgroup (F i))
    (Delta : Subgroup M) (hcomap : ∀ i, (S i).comap (phi i) = Delta) :
    (matchedMap phi S Delta hcomap).range =
      Subgroup.closure (generatorSet phi S) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using PushoutI.induction_on with
    | of i s =>
        exact Subgroup.subset_closure ⟨i, s, (matchedMap_of
          phi S Delta hcomap i s).symm⟩
    | base d =>
        have hfactor : PushoutI.base
            (smallEdge phi S Delta hcomap) d =
          PushoutI.of (φ := smallEdge phi S Delta hcomap)
            (Classical.choice (inferInstance : Nonempty I))
            (smallEdge phi S Delta hcomap
              (Classical.choice (inferInstance : Nonempty I)) d) := by
          exact (PushoutI.of_apply_eq_base _ _ d).symm
        rw [hfactor, matchedMap_of]
        exact Subgroup.subset_closure ⟨_, _, rfl⟩
    | mul x y hx hy =>
        rw [map_mul]
        exact Subgroup.mul_mem _ hx hy
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨i, s, rfl⟩
    exact ⟨PushoutI.of (φ := smallEdge phi S Delta hcomap) i s,
      matchedMap_of phi S Delta hcomap i s⟩

/-- Exact comaps ensure factor inclusions reflect the large edge range. -/
theorem factorInclusion_reflects_range
    (phi : ∀ i, M →* F i) (S : ∀ i, Subgroup (F i))
    (Delta : Subgroup M) (hcomap : ∀ i, (S i).comap (phi i) = Delta)
    (i : I) (s : S i)
    (hs : (s : F i) ∈ (phi i).range) :
    s ∈ (smallEdge phi S Delta hcomap i).range := by
  obtain ⟨m, hm⟩ := hs
  have hmDelta : m ∈ Delta := by
    rw [← hcomap i]
    change phi i m ∈ S i
    rw [hm]
    exact s.property
  refine ⟨⟨m, hmDelta⟩, ?_⟩
  apply Subtype.ext
  exact hm

/-- An indexed matched-map element landing in one large factor already lies
in the corresponding small factor. -/
theorem matchedMap_reflects_factor_range
    (phi : ∀ i, M →* F i) (S : ∀ i, Subgroup (F i))
    (Delta : Subgroup M) (hphi : ∀ i, Function.Injective (phi i))
    (hcomap : ∀ i, (S i).comap (phi i) = Delta) :
    ∀ i x, matchedMap phi S Delta hcomap x ∈
        (PushoutI.of (φ := phi) i).range →
      x ∈ (PushoutI.of (φ := smallEdge phi S Delta hcomap) i).range := by
  classical
  intro i x hx
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty
    (smallEdge phi S Delta hcomap) (fun j ↦ by
      intro a b hab
      exact Subtype.ext (hphi j (congrArg Subtype.val hab)))
  let w : PushoutI.NormalWord d := PushoutI.NormalWord.equiv x
  have hxprod : w.prod = x :=
    (PushoutI.NormalWord.equiv (d := d)).symm_apply_apply x
  let wm := PushoutEmbedding.wordMap (factorInclusion S)
    (fun _ ↦ Subtype.val_injective) w.toWord
  have hredSource : PushoutI.Reduced
      (smallEdge phi S Delta hcomap) w.toWord :=
    PushoutEmbedding.normalWord_reduced _ d w
  have hredTarget : PushoutI.Reduced phi wm := by
    intro l hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
    exact fun hrange ↦ hredSource l' hl'
      (factorInclusion_reflects_range phi S Delta hcomap l'.1 l'.2 hrange)
  have hprodImage : matchedMap phi S Delta hcomap w.prod =
      PushoutI.base phi (Delta.subtype w.head) *
        PushoutI.ofCoprodI wm.prod := by
    rw [PushoutI.NormalWord.prod, map_mul, matchedMap,
      PushoutBaseChange.map_base, PushoutBaseChange.map_ofCoprodI_prod]
  have hbaseFactor : PushoutI.base phi (Delta.subtype w.head) ∈
      (PushoutI.of (φ := phi) i).range := by
    refine ⟨phi i (Delta.subtype w.head), ?_⟩
    exact PushoutI.of_apply_eq_base _ i (Delta.subtype w.head)
  have hwordFactor : PushoutI.ofCoprodI wm.prod ∈
      (PushoutI.of (φ := phi) i).range := by
    have heq : PushoutI.ofCoprodI wm.prod =
        (PushoutI.base phi (Delta.subtype w.head))⁻¹ *
          matchedMap phi S Delta hcomap x := by
      rw [← hxprod, hprodImage]
      simp
    rw [heq]
    exact (PushoutI.of (φ := phi) i).range.mul_mem
      ((PushoutI.of (φ := phi) i).range.inv_mem hbaseFactor) hx
  obtain ⟨hmtail, hmfst⟩ :=
    Higman.MatchedSubgroupAmalgam.reduced_factor_shape
      phi hphi i wm hredTarget hwordFactor
  cases hlist : w.toWord.toList with
  | nil =>
      refine ⟨smallEdge phi S Delta hcomap i w.head, ?_⟩
      calc
        PushoutI.of (φ := smallEdge phi S Delta hcomap) i
            (smallEdge phi S Delta hcomap i w.head) =
            PushoutI.base (smallEdge phi S Delta hcomap) w.head :=
          PushoutI.of_apply_eq_base _ i w.head
        _ = w.prod := by
          rw [PushoutI.NormalWord.prod]
          have hwordOne : w.toWord.prod = 1 := by
            simp [Monoid.CoprodI.Word.prod, hlist]
          rw [hwordOne, map_one, mul_one]
        _ = x := hxprod
  | cons a rest =>
      have hrest : rest = [] := by
        have ht := hmtail
        simp only [wm, PushoutEmbedding.wordMap_toList, hlist,
          List.map_cons, List.tail_cons] at ht
        cases rest with
        | nil => rfl
        | cons c cs => simp at ht
      subst rest
      rcases a with ⟨j, g⟩
      have hwmne : wm.toList ≠ [] := by
        simp [wm, PushoutEmbedding.wordMap, hlist]
      have hwmidx := hmfst hwmne
      have hji : j = i := by
        simpa [wm, PushoutEmbedding.wordMap, hlist,
          Monoid.CoprodI.Word.fstIdx] using hwmidx
      subst j
      refine ⟨smallEdge phi S Delta hcomap i w.head * g, ?_⟩
      calc
        PushoutI.of (φ := smallEdge phi S Delta hcomap) i
            (smallEdge phi S Delta hcomap i w.head * g) =
            PushoutI.base (smallEdge phi S Delta hcomap) w.head *
              PushoutI.of (φ := smallEdge phi S Delta hcomap) i g := by
          rw [map_mul, PushoutI.of_apply_eq_base]
        _ = w.prod := by
          rw [PushoutI.NormalWord.prod]
          simp [Monoid.CoprodI.Word.prod, hlist]
        _ = x := hxprod

/-- The indexed matched closure meets each large factor in exactly its
displayed matched subgroup. -/
theorem generatorClosure_inf_factorRange
    [Nonempty I]
    (phi : ∀ i, M →* F i) (S : ∀ i, Subgroup (F i))
    (Delta : Subgroup M) (hphi : ∀ i, Function.Injective (phi i))
    (hcomap : ∀ i, (S i).comap (phi i) = Delta) (i : I) :
    Subgroup.closure (generatorSet phi S) ⊓
        (PushoutI.of (φ := phi) i).range =
      (S i).map (PushoutI.of (φ := phi) i) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxGen, hxFactor⟩ := Subgroup.mem_inf.mp hx
    rw [← matchedMap_range_eq_closure phi S Delta hcomap] at hxGen
    obtain ⟨y, hy⟩ := hxGen
    have hyFactor : matchedMap phi S Delta hcomap y ∈
        (PushoutI.of (φ := phi) i).range := by rwa [hy]
    obtain ⟨s, hs⟩ := matchedMap_reflects_factor_range
      phi S Delta hphi hcomap i y hyFactor
    refine Subgroup.mem_map.mpr ⟨(s : F i), s.property, ?_⟩
    rw [← hy, ← hs]
    exact matchedMap_of phi S Delta hcomap i s
  · rintro x ⟨s, hs, rfl⟩
    exact Subgroup.mem_inf.mpr ⟨
      Subgroup.subset_closure ⟨i, ⟨s, hs⟩, rfl⟩,
      ⟨s, rfl⟩⟩

/-- Indexed-family version of matched-range carry reflection. -/
theorem exists_rightCarryComparison_of_mem_range
    (phi : ∀ i, M →* F i) (S : ∀ i, Subgroup (F i))
    (Delta : Subgroup M) (hphi : ∀ i, Function.Injective (phi i))
    (hcomap : ∀ i, (S i).comap (phi i) = Delta)
    (raw : CoprodI.Word F) (hraw : PushoutI.Reduced phi raw)
    (rawHead : M)
    (hmem : PushoutI.base phi rawHead * PushoutI.ofCoprodI raw.prod ∈
      (matchedMap phi S Delta hcomap).range) :
    ∃ (d : PushoutI.NormalWord.Transversal
          (smallEdge phi S Delta hcomap))
      (w : PushoutI.NormalWord d),
      RightCarryComparison phi raw.toList
        (PushoutEmbedding.wordMap (factorInclusion S)
          (fun _ ↦ Subtype.val_injective) w.toWord).toList
        (rawHead⁻¹ * (Delta.subtype w.head)) := by
  classical
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty
    (smallEdge phi S Delta hcomap) (fun i ↦ by
      intro x y hxy
      exact Subtype.ext (hphi i (congrArg Subtype.val hxy)))
  let w : PushoutI.NormalWord d := PushoutI.NormalWord.equiv y
  have hwprod : w.prod = y :=
    (PushoutI.NormalWord.equiv (d := d)).symm_apply_apply y
  let wm := PushoutEmbedding.wordMap (factorInclusion S)
    (fun _ ↦ Subtype.val_injective) w.toWord
  have hwred : PushoutI.Reduced (smallEdge phi S Delta hcomap) w.toWord :=
    PushoutEmbedding.normalWord_reduced _ d w
  have hwmred : PushoutI.Reduced phi wm := by
    intro l hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
    exact fun hrange ↦ hwred l' hl'
      (factorInclusion_reflects_range phi S Delta hcomap l'.1 l'.2 hrange)
  have hprodImage : matchedMap phi S Delta hcomap w.prod =
      PushoutI.base phi (Delta.subtype w.head) *
        PushoutI.ofCoprodI wm.prod := by
    rw [PushoutI.NormalWord.prod, map_mul, matchedMap,
      PushoutBaseChange.map_base, PushoutBaseChange.map_ofCoprodI_prod]
  have heqProd : PushoutI.base phi rawHead *
        PushoutI.ofCoprodI raw.prod =
      PushoutI.base phi (Delta.subtype w.head) *
        PushoutI.ofCoprodI wm.prod := by
    rw [← hprodImage, hwprod, hy]
  exact ⟨d, w, Reduced.rightCarryComparison_of_eq
    phi hphi hraw hwmred rawHead (Delta.subtype w.head) heqProd⟩

end IndexedMatched

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

/-- Every letter of a factorwise mapped word lies in the corresponding
factor-map range. -/
theorem wordMap_letter_mem_range
    {G' : ι → Type*} [∀ i, Group (G' i)]
    (f : ∀ i, G i →* G' i) (hf : ∀ i, Function.Injective (f i))
    (w : CoprodI.Word G) :
    ∀ l ∈ (PushoutEmbedding.wordMap f hf w).toList,
      l.2 ∈ (f l.1).range := by
  intro l hl
  obtain ⟨l₀, -, rfl⟩ := List.mem_map.mp hl
  exact ⟨l₀.2, rfl⟩

end MatchedSubgroupAmalgamWordReflection
end GroupApproximation

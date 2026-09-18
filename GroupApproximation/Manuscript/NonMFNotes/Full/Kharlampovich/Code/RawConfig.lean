import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Code.GenIndex
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Code.RawWord
import GroupApproximation.Computability.PresentationCodeCompleteness
import Mathlib.Computability.Primrec.List

/-!
# Coded configuration words

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`, in the
form of the coding step for the Kharlampovich group `KMS.KhGroup M`.

For the letter numbering `genEquiv K N`, we build the coded word
`rawConfig K N gl st` of the configuration word
`x_{q_st A_0} * a_1^{(m_1)} * ⋯ * a_K^{(m_K)} * A_1 * ⋯ * A_K` (KMS Theorem `tmm`(b)).
We show that reading it back in `FreeGroup (KhGen K N)` gives `KMS.configWord`, and that
the coded word of the input configuration `(s; α, β, 0, …, 0)` depends primitive
recursively on `(α, β)`.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

open PresentationCodes

variable {K N : ℕ}

/-! ## Generic folds -/

theorem foldl_map_hom {α β γ : Type*} (h : α → β) (RF : α → γ → α) (F : β → γ → β)
    (hstep : ∀ a x, h (RF a x) = F (h a) x) (l : List γ) (a : α) :
    h (l.foldl RF a) = l.foldl F (h a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => exact (ih (RF a x)).trans (congrArg (fun z ↦ l.foldl F z) (hstep a x))

theorem iterate_map_hom {α β : Type*} (h : α → β) (RF : α → α) (F : β → β)
    (hstep : ∀ a, h (RF a) = F (h a)) (k : ℕ) (a : α) : h (RF^[k] a) = F^[k] (h a) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => exact (ih (RF a)).trans (congrArg (F^[k]) (hstep a))

/-- A fold over a fixed list, with primitive recursive steps, is primitive recursive. -/
theorem primrec_foldl_fixed {α β γ : Type*} [Primcodable α] [Primcodable β] (l : List γ)
    {RF : α → β → γ → β} (hRF : ∀ n, Primrec₂ fun a H ↦ RF a H n) :
    ∀ {f : α → β}, Primrec f → Primrec fun a ↦ l.foldl (RF a) (f a) := by
  induction l with
  | nil => exact fun hf ↦ hf
  | cons n l ih => exact fun hf ↦ ih ((hRF n).comp Primrec.id hf)

/-! ## Coded letters and configurations -/

/-- The coded one-letter word of a generator. -/
noncomputable def rawLetter (g : KhGen K N) : List (ℕ × Bool) :=
  [((genEquiv K N g : ℕ), true)]

/-- The coded step `f ↦ f * a_{n+1}`. -/
noncomputable def rawStarStep (K N : ℕ) (n : Fin K) (F : List (ℕ × Bool)) :
    List (ℕ × Bool) :=
  rawStar F (rawLetter (KhGen.a n : KhGen K N)) (rawLetter (KhGen.a' n : KhGen K N))

/-- The coded step `f ↦ f * a_{n+1}^{(m_{n+1})}`. -/
noncomputable def rawGlassFold (K N : ℕ) (gl : Fin K → ℕ) (H : List (ℕ × Bool)) (n : Fin K) :
    List (ℕ × Bool) :=
  Nat.iterate (rawStarStep K N n) (gl n) H

/-- The coded step `f ↦ f * A_{n+1}`. -/
noncomputable def rawCommFold (K N : ℕ) (H : List (ℕ × Bool)) (n : Fin K) :
    List (ℕ × Bool) :=
  rawComm H (rawLetter (KhGen.bigA n.succ : KhGen K N))

/-- The coded configuration word of `(st; gl)`. -/
noncomputable def rawConfig (K N : ℕ) (gl : Fin K → ℕ) (st : Fin (N + 1)) :
    List (ℕ × Bool) :=
  (List.finRange K).foldl (rawCommFold K N)
    ((List.finRange K).foldl (rawGlassFold K N gl) (rawLetter (KhGen.x st {0} : KhGen K N)))

/-- The group step `f ↦ f * a_{n+1}^{(m_{n+1})}`. -/
def glassFold (K N : ℕ) (gl : Fin K → ℕ) (h : FreeGroup (KhGen K N)) (n : Fin K) :
    FreeGroup (KhGen K N) :=
  Nat.iterate (fun f : FreeGroup (KhGen K N) ↦ khStar f (ga n) (ga' n)) (gl n) h

/-- The group step `f ↦ f * A_{n+1}`. -/
def commFold (K N : ℕ) (h : FreeGroup (KhGen K N)) (n : Fin K) : FreeGroup (KhGen K N) :=
  khComm h (gA n.succ)

theorem configWord_eq (st : Fin (N + 1)) (gl : Fin K → ℕ) :
    configWord (⟨st, gl⟩ : Minsky.Cfg K N) =
      (List.finRange K).foldl (commFold K N)
        ((List.finRange K).foldl (glassFold K N gl) (gxA0 st)) :=
  rfl

/-! ## Reading coded words back in `FreeGroup (KhGen K N)` -/

/-- A coded word read in `FreeGroup (KhGen K N)` through the letter numbering. -/
noncomputable def rawEval (K N : ℕ) (l : List (List (ℕ × Bool))) (L : List (ℕ × Bool)) :
    FreeGroup (KhGen K N) :=
  FreeGroup.map (genEquiv K N).symm (wordOf (genIndexCount K N, l) L)

theorem rawEval_append (l : List (List (ℕ × Bool))) (L₁ L₂ : List (ℕ × Bool)) :
    rawEval K N l (L₁ ++ L₂) = rawEval K N l L₁ * rawEval K N l L₂ := by
  simp only [rawEval, wordOf_append, map_mul]

theorem rawEval_rawInv (l : List (List (ℕ × Bool))) (L : List (ℕ × Bool)) :
    rawEval K N l (rawInv L) = (rawEval K N l L)⁻¹ := by
  simp only [rawEval, wordOf_rawInv, map_inv]

theorem rawEval_rawComm (l : List (List (ℕ × Bool))) (U V : List (ℕ × Bool)) :
    rawEval K N l (rawComm U V) = khComm (rawEval K N l U) (rawEval K N l V) := by
  simp only [rawEval, wordOf_rawComm, map_khComm]

theorem rawEval_rawStar (l : List (List (ℕ × Bool))) (F A A' : List (ℕ × Bool)) :
    rawEval K N l (rawStar F A A') =
      khStar (rawEval K N l F) (rawEval K N l A) (rawEval K N l A') := by
  simp only [rawEval, wordOf_rawStar, map_khStar]

theorem rawEval_rawLetter (l : List (List (ℕ × Bool))) (g : KhGen K N) :
    rawEval K N l (rawLetter g) = FreeGroup.of g := by
  have h : wordOf (genIndexCount K N, l) (rawLetter g) = FreeGroup.of (genEquiv K N g) := by
    show FreeGroup.mk [(letterOf (genIndexCount K N, l) ((genEquiv K N g : ℕ)), true)] =
      FreeGroup.mk [(genEquiv K N g, true)]
    rw [letterOf_val]
  rw [rawEval, h, FreeGroup.map.of, Equiv.symm_apply_apply]

theorem rawEval_rawCommFold (l : List (List (ℕ × Bool))) (H : List (ℕ × Bool)) (n : Fin K) :
    rawEval K N l (rawCommFold K N H n) = commFold K N (rawEval K N l H) n := by
  rw [rawCommFold, commFold, rawEval_rawComm, rawEval_rawLetter]

theorem rawEval_rawStarStep (l : List (List (ℕ × Bool))) (n : Fin K) (F : List (ℕ × Bool)) :
    rawEval K N l (rawStarStep K N n F) = khStar (rawEval K N l F) (ga n) (ga' n) := by
  rw [rawStarStep, rawEval_rawStar, rawEval_rawLetter, rawEval_rawLetter]

theorem rawEval_rawGlassFold (l : List (List (ℕ × Bool))) (gl : Fin K → ℕ)
    (H : List (ℕ × Bool)) (n : Fin K) :
    rawEval K N l (rawGlassFold K N gl H n) = glassFold K N gl (rawEval K N l H) n :=
  iterate_map_hom (rawEval K N l) (rawStarStep K N n)
    (fun f : FreeGroup (KhGen K N) ↦ khStar f (ga n) (ga' n)) (rawEval_rawStarStep l n) (gl n) H

/-- Reading the coded configuration word gives the configuration word. -/
theorem rawEval_rawConfig (l : List (List (ℕ × Bool))) (gl : Fin K → ℕ) (st : Fin (N + 1)) :
    rawEval K N l (rawConfig K N gl st) = configWord (⟨st, gl⟩ : Minsky.Cfg K N) := by
  rw [rawConfig, configWord_eq,
    foldl_map_hom (rawEval K N l) (rawCommFold K N) (commFold K N) (rawEval_rawCommFold l),
    foldl_map_hom (rawEval K N l) (rawGlassFold K N gl) (glassFold K N gl)
      (rawEval_rawGlassFold l gl)]
  exact congrArg
    (fun z : FreeGroup (KhGen K N) ↦
      (List.finRange K).foldl (commFold K N) ((List.finRange K).foldl (glassFold K N gl) z))
    (rawEval_rawLetter l (KhGen.x st {0} : KhGen K N))

/-- The coded word `(configuration word of (s; α, β, 0, …, 0)) * (stop word)⁻¹`. -/
noncomputable def configCode (K N : ℕ) (s : Fin (N + 1)) (p : ℕ × ℕ) : List (ℕ × Bool) :=
  rawConfig K N (Minsky.initGlasses K p.1 p.2) s ++ rawInv (rawConfig K N (fun _ ↦ 0) 0)

theorem rawEval_configCode (l : List (List (ℕ × Bool))) (s : Fin (N + 1)) (p : ℕ × ℕ) :
    rawEval K N l (configCode K N s p) =
      configWord (⟨s, Minsky.initGlasses K p.1 p.2⟩ : Minsky.Cfg K N) *
        (configWord (⟨0, fun _ ↦ 0⟩ : Minsky.Cfg K N))⁻¹ := by
  rw [configCode, rawEval_append, rawEval_rawInv, rawEval_rawConfig, rawEval_rawConfig]

/-! ## Primitive recursiveness -/

theorem primrec_initGlasses (K : ℕ) (n : Fin K) :
    Primrec fun p : ℕ × ℕ ↦ Minsky.initGlasses K p.1 p.2 n := by
  by_cases h0 : n.val = 0
  · exact Primrec.fst.of_eq fun _ ↦ by simp only [Minsky.initGlasses, if_pos h0]
  · by_cases h1 : n.val = 1
    · exact Primrec.snd.of_eq fun _ ↦ by simp only [Minsky.initGlasses, if_neg h0, if_pos h1]
    · exact (Primrec.const 0).of_eq fun _ ↦ by
        simp only [Minsky.initGlasses, if_neg h0, if_neg h1]

theorem primrec_rawGlassFold (n : Fin K) :
    Primrec₂ fun (p : ℕ × ℕ) (H : List (ℕ × Bool)) ↦
      rawGlassFold K N (Minsky.initGlasses K p.1 p.2) H n := by
  have hstep : Primrec₂ fun (_ : (ℕ × ℕ) × List (ℕ × Bool)) (F : List (ℕ × Bool)) ↦
      rawStarStep K N n F := by
    show Primrec fun q : ((ℕ × ℕ) × List (ℕ × Bool)) × List (ℕ × Bool) ↦
      rawStar q.2 (rawLetter (KhGen.a n : KhGen K N)) (rawLetter (KhGen.a' n : KhGen K N))
    exact primrec_rawStar Primrec.snd (Primrec.const _) (Primrec.const _)
  show Primrec fun q : (ℕ × ℕ) × List (ℕ × Bool) ↦
    (rawStarStep K N n)^[Minsky.initGlasses K q.1.1 q.1.2 n] q.2
  exact Primrec.nat_iterate ((primrec_initGlasses K n).comp Primrec.fst) Primrec.snd hstep

theorem primrec_rawCommFold (n : Fin K) :
    Primrec₂ fun (_ : ℕ × ℕ) (H : List (ℕ × Bool)) ↦ rawCommFold K N H n := by
  show Primrec fun q : (ℕ × ℕ) × List (ℕ × Bool) ↦
    rawComm q.2 (rawLetter (KhGen.bigA n.succ : KhGen K N))
  exact primrec_rawComm.comp Primrec.snd (Primrec.const _)

theorem primrec_rawConfig (s : Fin (N + 1)) :
    Primrec fun p : ℕ × ℕ ↦ rawConfig K N (Minsky.initGlasses K p.1 p.2) s := by
  have hinner : Primrec fun p : ℕ × ℕ ↦ (List.finRange K).foldl
      (fun H n ↦ rawGlassFold K N (Minsky.initGlasses K p.1 p.2) H n)
      (rawLetter (KhGen.x s {0} : KhGen K N)) :=
    primrec_foldl_fixed
      (RF := fun (p : ℕ × ℕ) H n ↦ rawGlassFold K N (Minsky.initGlasses K p.1 p.2) H n)
      (List.finRange K) (fun n ↦ primrec_rawGlassFold (N := N) n) (Primrec.const _)
  exact primrec_foldl_fixed (RF := fun (_ : ℕ × ℕ) H n ↦ rawCommFold K N H n)
    (List.finRange K) (fun n ↦ primrec_rawCommFold (N := N) n) hinner

theorem primrec_configCode (s : Fin (N + 1)) : Primrec (configCode K N s) := by
  show Primrec fun p : ℕ × ℕ ↦
    rawConfig K N (Minsky.initGlasses K p.1 p.2) s ++ rawInv (rawConfig K N (fun _ ↦ 0) 0)
  exact Primrec.list_append.comp (primrec_rawConfig (K := K) s) (Primrec.const _)

end KMS

end GroupApproximation.Full.Kharlampovich

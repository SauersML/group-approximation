import GroupApproximation.Computability.PerfectEnumeratedHardness
import GroupApproximation.Computability.TrivialEnumeratedPi02
import Mathlib.Algebra.Group.Commutator

/-!
# Perfectness of an enumerated presentation is `Π⁰₂`-complete

A group is perfect iff every generator is a product of commutators, and
"generator `n` is the product of the commutators listed by `l`" is one
instance of the r.e. word problem of the presentation.  So perfectness is
`Π⁰₂`, and with the switch lower bound of
`Computability.PerfectEnumeratedHardness` it is `Π⁰₂`-complete.  Research
node `perfectness-and-bounded-solvability-are-pi2-complete`.
-/

namespace GroupApproximation
namespace PerfectEnumeratedPi02

open ArithmeticalHierarchy EnumeratedPresentationCodes Higman
open PerfectEnumeratedHardness

/-- The raw commutator of two raw words. -/
def commRaw (u v : RawWord) : RawWord := u ++ v ++ invRaw u ++ invRaw v

theorem evalRaw_commRaw {A : Type} [Group A] (x : ℕ → A) (u v : RawWord) :
    evalRaw x (commRaw u v) =
      evalRaw x u * evalRaw x v * (evalRaw x u)⁻¹ * (evalRaw x v)⁻¹ := by
  simp [commRaw, evalRaw_append, evalRaw_invRaw, mul_assoc]

/-- The raw word spelling a product of commutators. -/
def commProdRaw : List (RawWord × RawWord) → RawWord
  | [] => []
  | p :: l => commRaw p.1 p.2 ++ commProdRaw l

theorem evalRaw_commProdRaw {A : Type} [Group A] (x : ℕ → A) :
    ∀ l : List (RawWord × RawWord),
      evalRaw x (commProdRaw l) =
        (l.map fun p ↦ evalRaw x p.1 * evalRaw x p.2 *
          (evalRaw x p.1)⁻¹ * (evalRaw x p.2)⁻¹).prod
  | [] => by simp [commProdRaw]
  | p :: l => by
      rw [commProdRaw, evalRaw_append, evalRaw_commRaw, evalRaw_commProdRaw x l]
      simp

/-- Generator `n` is a product of commutators, witnessed by a list and a
word-problem certificate. -/
def GenInCommutator (z : PresentationCode × ℕ) : Prop :=
  ∃ w : List (RawWord × RawWord) × WordCertificate,
    wordCheck (z.1, invRaw (commProdRaw w.1) ++ [(z.2, true)]) w.2 = true

/-- Every element of the presented group is the value of a raw word. -/
theorem exists_evalRaw (c : PresentationCode) (a : Carrier c) :
    ∃ u : RawWord, evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c)) u = a := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective a
  refine FreeGroup.induction_on
    (C := fun w : FreeGroup ℕ => ∃ u : RawWord,
      evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c)) u =
        PresentedGroup.mk (relatorSet c) w) w ?_ ?_ ?_ ?_
  · exact ⟨[], by simp⟩
  · intro n
    exact ⟨[(n, true)], by simp [PresentedGroup.of]⟩
  · rintro n ⟨u, hu⟩
    exact ⟨invRaw u, by rw [evalRaw_invRaw, hu, map_inv]⟩
  · rintro x y ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u ++ v, by rw [evalRaw_append, hu, hv, map_mul]⟩

/-- Elements of the commutator subgroup are exactly the values of the
commutator-product words. -/
theorem exists_commProdRaw_of_mem_commutator (c : PresentationCode) :
    ∀ y : Carrier c, y ∈ commutator (Carrier c) →
      ∃ l : List (RawWord × RawWord),
        evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c)) (commProdRaw l) = y := by
  intro y hy
  rw [commutator_eq_closure] at hy
  refine Subgroup.closure_induction (p := fun y _ ↦ ∃ l : List (RawWord × RawWord),
      evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c)) (commProdRaw l) = y)
    ?_ ?_ ?_ ?_ hy
  · rintro z ⟨a, b, rfl⟩
    obtain ⟨u, hu⟩ := exists_evalRaw c a
    obtain ⟨v, hv⟩ := exists_evalRaw c b
    refine ⟨[(u, v)], ?_⟩
    rw [commProdRaw, evalRaw_append, evalRaw_commRaw]
    simp only [commProdRaw, evalRaw_nil, mul_one]
    rw [show evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c)) u = a from hu,
      show evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c)) v = b from hv]
    simp [commutatorElement_def, mul_assoc]
  · exact ⟨[], by simp [commProdRaw]⟩
  · rintro z w _ _ ⟨lz, hlz⟩ ⟨lw, hlw⟩
    refine ⟨lz ++ lw, ?_⟩
    have happ : ∀ a b : List (RawWord × RawWord),
        commProdRaw (a ++ b) = commProdRaw a ++ commProdRaw b := by
      intro a b
      induction a with
      | nil => simp [commProdRaw]
      | cons q r ihr => simp [commProdRaw, ihr, List.append_assoc]
    rw [happ, evalRaw_append, hlz, hlw]
  · rintro z _ ⟨l, hl⟩
    refine ⟨(l.map fun p ↦ (p.2, p.1)).reverse, ?_⟩
    have key : ∀ m : List (RawWord × RawWord),
        evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c))
            (commProdRaw ((m.map fun p ↦ (p.2, p.1)).reverse)) =
          (evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c)) (commProdRaw m))⁻¹ := by
      intro m
      induction m with
      | nil => simp [commProdRaw]
      | cons p l ih =>
          have happ : ∀ a b : List (RawWord × RawWord),
              commProdRaw (a ++ b) = commProdRaw a ++ commProdRaw b := by
            intro a b
            induction a with
            | nil => simp [commProdRaw]
            | cons q r ihr => simp [commProdRaw, ihr, List.append_assoc]
          simp only [List.map_cons, List.reverse_cons]
          rw [happ, evalRaw_append, ih, commProdRaw, evalRaw_append, evalRaw_commRaw,
            commProdRaw, evalRaw_nil, mul_one, commProdRaw, evalRaw_append,
            evalRaw_commRaw]
          group
    rw [key l, hl]

/-- The challenge predicate is the word problem at a commutator-product
word, hence recursively enumerable. -/
theorem genInCommutator_iff (c : PresentationCode) (n : ℕ) :
    GenInCommutator (c, n) ↔ (PresentedGroup.of n : Carrier c) ∈ commutator (Carrier c) := by
  constructor
  · rintro ⟨⟨l, cert⟩, hcert⟩
    have h1 : evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c))
        (invRaw (commProdRaw l) ++ [(n, true)]) = 1 :=
      (wordCheck_complete c _).2 ⟨cert, hcert⟩
    rw [evalRaw_append, evalRaw_invRaw] at h1
    have h2 : (PresentedGroup.of n : Carrier c) =
        evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c)) (commProdRaw l) := by
      have := congrArg (fun t ↦ evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c))
        (commProdRaw l) * t) h1
      simpa [mul_assoc] using this
    rw [h2]
    -- the value of a commutator-product word lies in the commutator subgroup
    clear h1 h2 hcert
    induction l with
    | nil => simp [commProdRaw]
    | cons p l ih =>
        rw [commProdRaw, evalRaw_append, evalRaw_commRaw]
        refine mul_mem ?_ ih
        set a := evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c)) p.1 with ha
        set b := evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c)) p.2 with hb
        have hset : a * b * a⁻¹ * b⁻¹ ∈ commutatorSet (Carrier c) := ⟨a, b, rfl⟩
        rw [commutator_eq_closure]
        exact Subgroup.subset_closure hset
  · intro hmem
    obtain ⟨l, hl⟩ := exists_commProdRaw_of_mem_commutator c _ hmem
    have h1 : evalRaw (fun k ↦ (PresentedGroup.of k : Carrier c))
        (invRaw (commProdRaw l) ++ [(n, true)]) = 1 := by
      rw [evalRaw_append, evalRaw_invRaw, hl]
      simp [PresentedGroup.of]
    obtain ⟨cert, hcert⟩ := (wordCheck_complete c _).1 h1
    exact ⟨(l, cert), hcert⟩

/-- Perfectness of an enumerated code, as a universal challenge. -/
theorem isPerfect_iff_forall (c : PresentationCode) :
    IsPerfectGroup (Carrier c) ↔ ∀ n, GenInCommutator (c, n) := by
  constructor
  · intro h n
    exact (genInCommutator_iff c n).2 (h _)
  · intro h x
    have hgen : ∀ n, (PresentedGroup.of n : Carrier c) ∈ commutator (Carrier c) :=
      fun n ↦ (genInCommutator_iff c n).1 (h n)
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective x
    rw [← hw]
    refine FreeGroup.induction_on
      (C := fun w : FreeGroup ℕ => (PresentedGroup.mk (relatorSet c) w : Carrier c) ∈
        commutator (Carrier c)) w ?_ ?_ ?_ ?_
    · simp
    · intro n
      simpa [PresentedGroup.of] using hgen n
    · intro n ih
      rw [map_inv]
      exact inv_mem ih
    · intro u v ihu ihv
      rw [map_mul]
      exact mul_mem ihu ihv

/-- The challenge is recursively enumerable: it is one instance of the
uniform word-problem checker. -/
theorem primrec_commProdRaw : Primrec commProdRaw := by
  have hcomm : Primrec fun p : RawWord × RawWord => commRaw p.1 p.2 := by
    have h1 : Primrec fun p : RawWord × RawWord => invRaw p.1 ++ invRaw p.2 :=
      Primrec.list_append.comp (primrec_invRaw.comp Primrec.fst)
        (primrec_invRaw.comp Primrec.snd)
    have h2 : Primrec fun p : RawWord × RawWord => p.2 ++ (invRaw p.1 ++ invRaw p.2) :=
      Primrec.list_append.comp Primrec.snd h1
    have h3 : Primrec fun p : RawWord × RawWord =>
        p.1 ++ (p.2 ++ (invRaw p.1 ++ invRaw p.2)) :=
      Primrec.list_append.comp Primrec.fst h2
    exact h3.of_eq fun p => by simp [commRaw, List.append_assoc]

  have hstep : Primrec₂ fun (_ : List (RawWord × RawWord))
      (z : (RawWord × RawWord) × RawWord) => commRaw z.1.1 z.1.2 ++ z.2 :=
    (Primrec.list_append.comp (hcomm.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const ([] : RawWord)) hstep).of_eq
    (by
      intro l
      induction l with
      | nil => rfl
      | cons p l ih => simpa [commProdRaw] using congrArg (fun t => commRaw p.1 p.2 ++ t) ih)

/-- The challenge is recursively enumerable: it is one instance of the
uniform word-problem checker. -/
theorem rePred_genInCommutator : REPred GenInCommutator := by
  have hprim : Primrec₂ fun (z : PresentationCode × ℕ)
      (w : List (RawWord × RawWord) × WordCertificate) =>
      wordCheck (z.1, invRaw (commProdRaw w.1) ++ [(z.2, true)]) w.2 := by
    have hinv : Primrec fun w : List (RawWord × RawWord) × WordCertificate =>
        invRaw (commProdRaw w.1) :=
      primrec_invRaw.comp (primrec_commProdRaw.comp Primrec.fst)
    exact primrec_wordCheck.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.list_append.comp (hinv.comp Primrec.snd)
          (Primrec.list_cons.comp
            (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.const true))
            (Primrec.const []))))
      (Primrec.snd.comp Primrec.snd)
  exact (WordProblemRE.rePred_exists_eq_true hprim.to_comp).of_eq fun _ => Iff.rfl

/-- **Perfectness of enumerated presentation codes is `Π⁰₂`.** -/
theorem pi02_isPerfect :
    Pi02 (fun c : PresentationCode ↦ IsPerfectGroup (Carrier c)) :=
  ⟨GenInCommutator, rePred_genInCommutator, fun c ↦ isPerfect_iff_forall c⟩

/-- **Perfectness of enumerated presentation codes is `Π⁰₂`-complete.** -/
theorem perfect_enum_pi02Complete :
    Pi02Complete (fun c : PresentationCode ↦ IsPerfectGroup (Carrier c)) :=
  ⟨pi02_isPerfect, PerfectEnumeratedHardness.perfectCode_pi02Hard⟩

end PerfectEnumeratedPi02
end GroupApproximation

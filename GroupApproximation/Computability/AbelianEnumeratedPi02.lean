import GroupApproximation.Computability.IsoInvariantSwitchHardness
import GroupApproximation.Computability.TrivialEnumeratedPi02
import Mathlib.GroupTheory.Perm.Basic

/-!
# Commutativity of an enumerated presentation is `Π⁰₂`-complete

The presented group is abelian iff every pair of generators commutes, each
instance an r.e. word-problem question, so commutativity is `Π⁰₂`; the
isomorphism-invariant switch with `F_2` as forbidden seed (non-abelian
because two transpositions of `S_3` do not commute) gives `Π⁰₂`-hardness.
Research node `arithmetical-complexity-table-of-group-properties`.
-/

namespace GroupApproximation
namespace AbelianEnumeratedPi02

open ArithmeticalHierarchy EnumeratedPresentationCodes Higman IsoInvariantSwitchHardness

/-- Generators `m` and `n` commute in the presented group, through the uniform
word checker applied to the commutator word. -/
def GenComm (z : PresentationCode × ℕ) : Prop :=
  ∃ cert : WordCertificate,
    wordCheck (z.1, [((Nat.unpair z.2).1, true), ((Nat.unpair z.2).2, true),
      ((Nat.unpair z.2).1, false), ((Nat.unpair z.2).2, false)]) cert = true

/-- The commutator word evaluates to `1` iff the two elements commute. -/
theorem comm_word_iff {G : Type} [Group G] (a b : G) :
    a * (b * (a⁻¹ * b⁻¹)) = 1 ↔ a * b = b * a := by
  constructor
  · intro h
    have h' : a * b * a⁻¹ * b⁻¹ = 1 := by simpa only [mul_assoc] using h
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h'
    exact h'
  · intro h
    rw [← mul_assoc, ← mul_assoc, h]
    group

theorem genComm_iff (c : PresentationCode) (k : ℕ) :
    GenComm (c, k) ↔
      (PresentedGroup.of (Nat.unpair k).1 : Carrier c) * PresentedGroup.of (Nat.unpair k).2 =
        PresentedGroup.of (Nat.unpair k).2 * PresentedGroup.of (Nat.unpair k).1 := by
  unfold GenComm
  rw [← wordCheck_complete]
  change (PresentedGroup.of (Nat.unpair k).1 : Carrier c) *
      (PresentedGroup.of (Nat.unpair k).2 * ((PresentedGroup.of (Nat.unpair k).1)⁻¹ *
        ((PresentedGroup.of (Nat.unpair k).2)⁻¹ * 1))) = 1 ↔ _
  rw [mul_one]
  exact comm_word_iff _ _

/-- If all generators commute pairwise, the presented group is commutative. -/
theorem comm_of_forall_generators (c : PresentationCode)
    (h : ∀ m n, (PresentedGroup.of m : Carrier c) * PresentedGroup.of n =
      PresentedGroup.of n * PresentedGroup.of m) :
    ∀ x y : Carrier c, x * y = y * x := by
  have inv_step : ∀ (a x : Carrier c), a * x = x * a → a * x⁻¹ = x⁻¹ * a := by
    intro a x ih
    exact mul_inv_eq_iff_eq_mul.mpr
      (by rw [mul_assoc, ih, ← mul_assoc, inv_mul_cancel, one_mul])
  have mul_step : ∀ (a u v : Carrier c), a * u = u * a → a * v = v * a →
      a * (u * v) = u * v * a := by
    intro a u v ihu ihv
    rw [← mul_assoc, ihu, mul_assoc, ihv, mul_assoc]
  have gen : ∀ (m : ℕ) (y : Carrier c),
      (PresentedGroup.of m : Carrier c) * y = y * PresentedGroup.of m := by
    intro m y
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective y
    rw [← hw]
    change (PresentedGroup.of m : Carrier c) * PresentedGroup.mk (relatorSet c) w =
      PresentedGroup.mk (relatorSet c) w * PresentedGroup.of m
    refine FreeGroup.induction_on
      (C := fun w : FreeGroup ℕ => (PresentedGroup.of m : Carrier c) *
        PresentedGroup.mk (relatorSet c) w = PresentedGroup.mk (relatorSet c) w *
        PresentedGroup.of m) w ?_ ?_ ?_ ?_
    · rw [map_one, mul_one, one_mul]
    · intro n
      exact h m n
    · intro n ih
      rw [map_inv]
      exact inv_step _ _ ih
    · intro u v ihu ihv
      rw [map_mul]
      exact mul_step _ _ _ ihu ihv
  intro x y
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective x
  rw [← hw]
  change PresentedGroup.mk (relatorSet c) w * y = y * PresentedGroup.mk (relatorSet c) w
  refine FreeGroup.induction_on
    (C := fun w : FreeGroup ℕ => PresentedGroup.mk (relatorSet c) w * y =
      y * PresentedGroup.mk (relatorSet c) w) w ?_ ?_ ?_ ?_
  · rw [map_one, mul_one, one_mul]
  · intro n
    exact gen n y
  · intro n ih
    rw [map_inv]
    exact (inv_step y _ ih.symm).symm
  · intro u v ihu ihv
    rw [map_mul]
    exact (mul_step y _ _ ihu.symm ihv.symm).symm

/-- Commutativity, as a predicate on codes. -/
def IsCommCode (c : PresentationCode) : Prop := ∀ x y : Carrier c, x * y = y * x

theorem isCommCode_iff (c : PresentationCode) : IsCommCode c ↔ ∀ k, GenComm (c, k) := by
  constructor
  · intro h k
    rw [genComm_iff]
    exact h _ _
  · intro h
    exact comm_of_forall_generators c fun m n ↦ by
      have := (genComm_iff c (Nat.pair m n)).1 (h (Nat.pair m n))
      simpa using this

theorem rePred_genComm : REPred GenComm := by
  have : Primrec₂ fun (z : PresentationCode × ℕ) (cert : WordCertificate) =>
      wordCheck (z.1, [((Nat.unpair z.2).1, true), ((Nat.unpair z.2).2, true),
        ((Nat.unpair z.2).1, false), ((Nat.unpair z.2).2, false)]) cert := by
    have hu1 : Primrec fun z : PresentationCode × ℕ => (Nat.unpair z.2).1 :=
      Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
    have hu2 : Primrec fun z : PresentationCode × ℕ => (Nat.unpair z.2).2 :=
      Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
    have hlist : Primrec fun z : PresentationCode × ℕ =>
        ([((Nat.unpair z.2).1, true), ((Nat.unpair z.2).2, true),
          ((Nat.unpair z.2).1, false), ((Nat.unpair z.2).2, false)] : RawWord) :=
      Primrec.list_cons.comp (Primrec.pair hu1 (Primrec.const true))
        (Primrec.list_cons.comp (Primrec.pair hu2 (Primrec.const true))
          (Primrec.list_cons.comp (Primrec.pair hu1 (Primrec.const false))
            (Primrec.list_cons.comp (Primrec.pair hu2 (Primrec.const false))
              (Primrec.const []))))
    exact primrec_wordCheck.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) (hlist.comp Primrec.fst))
      Primrec.snd
  exact (WordProblemRE.rePred_exists_eq_true this.to_comp).of_eq fun _ => Iff.rfl

/-- **Commutativity of enumerated presentation codes is `Π⁰₂`.** -/
theorem pi02_isCommCode : Pi02 IsCommCode :=
  ⟨GenComm, rePred_genComm, fun c ↦ isCommCode_iff c⟩

/-- Two transpositions of a three-element set do not commute. -/
theorem swap_not_comm :
    (Equiv.swap (0 : Fin 3) 1) * Equiv.swap (1 : Fin 3) 2 ≠
      Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 := by
  decide

/-- The free group on two generators is not commutative. -/
theorem freeGroup_two_not_comm :
    ¬ ∀ x y : FreeGroup (Fin 2), x * y = y * x := by
  intro h
  let φ : FreeGroup (Fin 2) →* Equiv.Perm (Fin 3) :=
    FreeGroup.lift fun i => if i = 0 then Equiv.swap (0 : Fin 3) 1 else Equiv.swap (1 : Fin 3) 2
  have this := congrArg φ (h (FreeGroup.of 0) (FreeGroup.of 1))
  have e0 : φ (FreeGroup.of 0) = Equiv.swap (0 : Fin 3) 1 := by simp [φ]
  have e1 : φ (FreeGroup.of 1) = Equiv.swap (1 : Fin 3) 2 := by simp [φ]
  rw [map_mul, map_mul, e0, e1] at this
  exact swap_not_comm this

/-- **Commutativity of enumerated presentation codes is `Π⁰₂`-hard.** -/
theorem commCode_pi02Hard : Pi02Hard IsCommCode := by
  obtain ⟨seed, ⟨e⟩⟩ := PresentationCodes.exists_code_mulEquiv (FreeGroup (Fin 2))
  exact enumeratedCodeProperty_pi02Hard
    (P := fun (H : Type) (_ : Group H) ↦ ∀ x y : H, x * y = y * x)
    { invariant := fun e h x y ↦ by
        have := h (e x) (e y)
        rw [← map_mul, ← map_mul] at this
        exact e.injective this
      trivial := fun x y ↦ Subsingleton.elim _ _
      forbidden := seed
      forbidden_not := fun h ↦ freeGroup_two_not_comm fun x y ↦ by
        have := h (e.symm x) (e.symm y)
        rw [← map_mul, ← map_mul] at this
        exact e.symm.injective this }

/-- **Commutativity of enumerated presentation codes is `Π⁰₂`-complete.** -/
theorem comm_enum_pi02Complete : Pi02Complete IsCommCode :=
  ⟨pi02_isCommCode, commCode_pi02Hard⟩

end AbelianEnumeratedPi02
end GroupApproximation

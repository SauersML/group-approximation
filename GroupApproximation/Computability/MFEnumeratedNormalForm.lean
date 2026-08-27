import GroupApproximation.Computability.MFEnumeratedMicrostate

/-!
# The `∀∃` normal form for MF-ness of a recursively enumerated presentation

`MFMicrostate.isOperatorMF_iff_forall_answers` is the oracle-free normal form
for *finite* presentation codes.  This file proves the same equivalence for
the standard recursively enumerated codes of
`Computability.EnumeratedPresentationCodes`: MF-ness of the coded group is
exactly the assertion that every challenge `(W, N, k)` is answered, where a
challenge now also names a prefix length `N` of the relator stream.

The two directions are the finite-code proofs, transported to the countable
alphabet exactly as `SoficEnumeratedPi02.isSofic_iff_forall_answersN`
transports the sofic ones.

* Forward, a microstate is read off a separation-one `NormModel` of a finite
  set: the generator at a letter below a chosen bound is the model's value on
  that letter, and the identity above it; the word induction `approxWordM`
  bounds the gap between evaluating a word in the microstate and in the model
  linearly in the word's length.  The bound is chosen past every letter of the
  listed words and of the first `N + 1` relators, so no listed word ever
  meets a truncated generator.
* Backward, a `NormModel` is read off microstates by evaluating chosen words
  for group elements; multiplicativity is `exists_matrix_area_bound_list`,
  the area bound relative to a relator prefix, which is what lets the
  challenge name only finitely many relators.

The open variant (`isOperatorMF_iff_forall_openAnswersM`) is the shape the
rational matrix certificates decide; it follows by querying the closed form
at scale `2k+1`, as in `MFRecognitionPi02.isOperatorMF_iff_forall_openAnswers`.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace MFEnumeratedPi02

open Higman EnumeratedPresentationCodes
open SoficEnumeratedPi02 (relatorAt relatorAt_mem_relatorSet EnumWordProblem
  evalCode evalCode_append evalCode_invRaw evalCode_letter_pos
  evalCode_letter_neg evalCode_eq_one_iff evalCode_surjective
  evalRaw_cons' evalRaw_letter_pos evalRaw_letter_neg letterBound lt_letterBound)

noncomputable section

namespace NatMatrixMicrostate

@[simp] theorem hlen_one (M : NatMatrixMicrostate) : M.hlen 1 = 0 := by
  rw [hlen, map_one, opLength_one]

theorem hlen_nonneg (M : NatMatrixMicrostate) (x : FreeGroup ℕ) :
    0 ≤ M.hlen x :=
  opLength_nonneg _ _

/-- Displacement is subadditive. -/
theorem hlen_mul_le (M : NatMatrixMicrostate) (x y : FreeGroup ℕ) :
    M.hlen (x * y) ≤ M.hlen x + M.hlen y := by
  rw [hlen, hlen, hlen, map_mul]
  exact opLength_mul_le _ _ _

/-- Displacement is inversion-invariant. -/
theorem hlen_inv (M : NatMatrixMicrostate) (x : FreeGroup ℕ) :
    M.hlen x⁻¹ = M.hlen x := by
  rw [hlen, hlen, map_inv]
  exact opLength_inv _ _

/-- Displacement is conjugation-invariant. -/
theorem hlen_conj (M : NatMatrixMicrostate) (t x : FreeGroup ℕ) :
    M.hlen (t * x * t⁻¹) = M.hlen x := by
  rw [hlen, hlen, map_mul, map_mul, map_inv]
  exact opLength_conj _ _ _

theorem len_nonneg (M : NatMatrixMicrostate) (w : List (ℕ × Bool)) :
    0 ≤ M.len w :=
  hlen_nonneg _ _

end NatMatrixMicrostate

/-! ## The area bound, relative to a relator prefix -/

/-- **Bounded area relative to a prefix.**  A free-group element carries a
prefix length `N` and an area count `A` such that its displacement is at most
`A · δ` in every microstate displacing the first `N + 1` enumerated relators
by at most `δ`. -/
def MatrixAreaBounded (c : PresentationCode) (x : FreeGroup ℕ) : Prop :=
  ∃ N A : ℕ, ∀ (M : NatMatrixMicrostate) (δ : ℝ), 0 ≤ δ →
    (∀ j, j ≤ N → M.hlen (relatorAt c j) ≤ δ) → M.hlen x ≤ (A : ℝ) * δ

/-- The elements of bounded area form a subgroup. -/
def matrixAreaSubgroup (c : PresentationCode) : Subgroup (FreeGroup ℕ) where
  carrier := {x | MatrixAreaBounded c x}
  one_mem' := by
    refine ⟨0, 0, fun M δ _ _ => ?_⟩
    rw [M.hlen_one, Nat.cast_zero, zero_mul]
  mul_mem' := by
    rintro x y ⟨Nx, Ax, hx⟩ ⟨Ny, Ay, hy⟩
    refine ⟨max Nx Ny, Ax + Ay, fun M δ hδ hrel => ?_⟩
    have hx' := hx M δ hδ fun j hj => hrel j (hj.trans (le_max_left _ _))
    have hy' := hy M δ hδ fun j hj => hrel j (hj.trans (le_max_right _ _))
    refine (M.hlen_mul_le x y).trans ?_
    have hsum := add_le_add hx' hy'
    rwa [← add_mul, ← Nat.cast_add] at hsum
  inv_mem' := by
    rintro x ⟨N, A, hx⟩
    refine ⟨N, A, fun M δ hδ hrel => ?_⟩
    rw [M.hlen_inv]
    exact hx M δ hδ hrel

/-- Displacement is conjugation-invariant, so the area subgroup is normal. -/
instance matrixAreaSubgroup_normal (c : PresentationCode) :
    (matrixAreaSubgroup c).Normal where
  conj_mem := by
    rintro x ⟨N, A, hx⟩ g
    refine ⟨N, A, fun M δ hδ hrel => ?_⟩
    rw [M.hlen_conj]
    exact hx M δ hδ hrel

theorem mem_matrixAreaSubgroup_iff {c : PresentationCode} {x : FreeGroup ℕ} :
    x ∈ matrixAreaSubgroup c ↔ MatrixAreaBounded c x := Iff.rfl

theorem subset_matrixAreaSubgroup (c : PresentationCode) :
    relatorSet c ⊆ (matrixAreaSubgroup c : Set (FreeGroup ℕ)) := by
  rintro r ⟨j, rfl⟩
  refine mem_matrixAreaSubgroup_iff.2 ⟨j, 1, fun M δ _ hrel => ?_⟩
  rw [Nat.cast_one, one_mul]
  exact hrel j le_rfl

/-- **Approximate relators force approximate triviality.**  Every element of
the normal closure of the enumerated relator set carries a prefix length and
an area count that bound its displacement in every unitary microstate. -/
theorem exists_matrix_area_bound (c : PresentationCode) {x : FreeGroup ℕ}
    (hx : x ∈ Subgroup.normalClosure (relatorSet c)) : MatrixAreaBounded c x :=
  mem_matrixAreaSubgroup_iff.1
    (Subgroup.normalClosure_le_normal (N := matrixAreaSubgroup c)
      (subset_matrixAreaSubgroup c) hx)

/-- **The area bound, for a finite list of trivial words at once.** -/
theorem exists_matrix_area_bound_list (c : PresentationCode)
    (L : List (List (ℕ × Bool))) (hL : ∀ u ∈ L, evalCode c u = 1) :
    ∃ N A : ℕ, ∀ (M : NatMatrixMicrostate) (δ : ℝ), 0 ≤ δ →
      (∀ j, j ≤ N → M.hlen (relatorAt c j) ≤ δ) →
        ∀ u ∈ L, M.len u ≤ (A : ℝ) * δ := by
  induction L with
  | nil => exact ⟨0, 0, by simp⟩
  | cons a t ih =>
      obtain ⟨Nt, At, hNt⟩ := ih fun u hu => hL u (List.mem_cons_of_mem _ hu)
      obtain ⟨Na, Aa, hNa⟩ := exists_matrix_area_bound c
        ((evalCode_eq_one_iff c a).1 (hL a List.mem_cons_self))
      refine ⟨max Na Nt, max Aa At, fun M δ hδ hrel u hu => ?_⟩
      have hmono : ∀ A : ℕ, A ≤ max Aa At →
          ∀ y : ℝ, y ≤ (A : ℝ) * δ → y ≤ ((max Aa At : ℕ) : ℝ) * δ := by
        intro A hA y hy
        refine hy.trans (mul_le_mul_of_nonneg_right ?_ hδ)
        exact_mod_cast hA
      rcases List.mem_cons.1 hu with rfl | hu'
      · exact hmono Aa (le_max_left _ _) _
          (hNa M δ hδ fun j hj => hrel j (hj.trans (le_max_left _ _)))
      · exact hmono At (le_max_right _ _) _
          (hNt M δ hδ (fun j hj => hrel j (hj.trans (le_max_right _ _))) u hu')

/-! ## Reading a microstate off a norm model -/

section Forward

variable {c : PresentationCode} {F : Finset (Carrier c)} {ε : ℝ}

/-- A norm model's value, as an element of the unitary group. -/
def umapM (NM : NormModel (Carrier c) F 1 ε) (g : Carrier c) :
    Matrix.unitaryGroup NM.carrier ℂ :=
  ⟨NM.map g, NM.isUnitary g⟩

@[simp] theorem umapM_coe (NM : NormModel (Carrier c) F 1 ε) (g : Carrier c) :
    ((umapM NM g : Matrix.unitaryGroup NM.carrier ℂ) :
      Matrix NM.carrier NM.carrier ℂ) = NM.map g := rfl

/-- Multiplicativity, in displacement form. -/
theorem umapM_mul_le (NM : NormModel (Carrier c) F 1 ε) {g h : Carrier c}
    (hg : g ∈ F) (hh : h ∈ F) :
    opLength NM.carrier ((umapM NM g * umapM NM h)⁻¹ * umapM NM (g * h)) ≤ ε := by
  rw [opLength_inv_mul]
  simpa using NM.multiplicative g hg h hh

/-- The value at the identity is small. -/
theorem umapM_one_le (NM : NormModel (Carrier c) F 1 ε)
    (h1 : (1 : Carrier c) ∈ F) :
    opLength NM.carrier (umapM NM 1) ≤ ε := by
  have h := umapM_mul_le NM h1 h1
  rw [mul_one] at h
  have hrw : (umapM NM 1 * umapM NM 1)⁻¹ * umapM NM 1 = (umapM NM 1)⁻¹ := by group
  rw [hrw, opLength_inv] at h
  exact h

/-- The value at an inverse is close to the inverse of the value. -/
theorem umapM_inv_le (NM : NormModel (Carrier c) F 1 ε)
    (h1 : (1 : Carrier c) ∈ F) {g : Carrier c} (hg : g ∈ F) (hg' : g⁻¹ ∈ F) :
    opLength NM.carrier ((umapM NM g⁻¹)⁻¹ * (umapM NM g)⁻¹) ≤ 2 * ε := by
  have h := umapM_mul_le NM hg hg'
  rw [mul_inv_cancel] at h
  have hsplit : (umapM NM g * umapM NM g⁻¹)⁻¹
      = ((umapM NM g * umapM NM g⁻¹)⁻¹ * umapM NM 1) * (umapM NM 1)⁻¹ := by group
  have hone : opLength NM.carrier (umapM NM 1)⁻¹ ≤ ε := by
    rw [opLength_inv]; exact umapM_one_le NM h1
  have hbound : opLength NM.carrier (umapM NM g * umapM NM g⁻¹)⁻¹ ≤ ε + ε := by
    rw [hsplit]
    exact (opLength_mul_le _ _ _).trans (add_le_add h hone)
  have hEq : (umapM NM g⁻¹)⁻¹ * (umapM NM g)⁻¹
      = (umapM NM g * umapM NM g⁻¹)⁻¹ := by rw [mul_inv_rev]
  rw [hEq]
  linarith

/-- The generator family a norm model provides, truncated at a bound: the
model's value on the letter below the bound, the identity above it. -/
def truncGenM (NM : NormModel (Carrier c) F 1 ε) (b i : ℕ) :
    Matrix.unitaryGroup NM.carrier ℂ :=
  if i < b then umapM NM (evalCode c [(i, true)]) else 1

theorem truncGenM_of_lt (NM : NormModel (Carrier c) F 1 ε) {b i : ℕ}
    (hi : i < b) :
    truncGenM NM b i = umapM NM (evalCode c [(i, true)]) := by
  rw [truncGenM, if_pos hi]

/-- The microstate a norm model determines, once a letter bound is chosen. -/
def modelMicrostateM (NM : NormModel (Carrier c) F 1 ε) (b : ℕ) :
    NatMatrixMicrostate where
  model := NM.carrier
  card_pos := NM.nonempty
  gen := truncGenM NM b

@[simp] theorem modelMicrostateM_len (NM : NormModel (Carrier c) F 1 ε) (b : ℕ)
    (w : List (ℕ × Bool)) :
    (modelMicrostateM NM b).len w
      = opLength NM.carrier (evalRaw (truncGenM NM b) w) :=
  (modelMicrostateM NM b).len_def w

/-- The microstate's value on a one-letter word is within `2ε` of the model's,
provided the letter is below the bound. -/
theorem letter_gapM (NM : NormModel (Carrier c) F 1 ε) (b : ℕ) (hε : 0 ≤ ε)
    (h1 : (1 : Carrier c) ∈ F)
    (hgen : ∀ i, i < b → ∀ s : Bool, evalCode c [(i, s)] ∈ F)
    (p : ℕ × Bool) (hp : p.1 < b) :
    opLength NM.carrier
        ((umapM NM (evalCode c [p]))⁻¹ * evalRaw (truncGenM NM b) [p])
      ≤ 2 * ε := by
  obtain ⟨i, s⟩ := p
  have hi : i < b := hp
  cases s with
  | true =>
      rw [evalRaw_letter_pos, truncGenM_of_lt NM hi, inv_mul_cancel, opLength_one]
      linarith
  | false =>
      have hgF : evalCode c [(i, true)] ∈ F := hgen i hi true
      have hgF' : (evalCode c [(i, true)])⁻¹ ∈ F := by
        have h := hgen i hi false
        rwa [evalCode_letter_neg, ← evalCode_letter_pos c i] at h
      rw [evalRaw_letter_neg, truncGenM_of_lt NM hi, evalCode_letter_neg,
        ← evalCode_letter_pos c i]
      exact umapM_inv_le NM h1 hgF hgF'

/-- **The word induction.**  Evaluating a raw word in the microstate and
evaluating it in the model differ by at most a multiple of the accuracy,
linear in the word's length, provided every letter is below the bound. -/
theorem approxWordM (NM : NormModel (Carrier c) F 1 ε) (b : ℕ) (hε : 0 ≤ ε)
    (h1 : (1 : Carrier c) ∈ F)
    (hgen : ∀ i, i < b → ∀ s : Bool, evalCode c [(i, s)] ∈ F) :
    ∀ (u : List (ℕ × Bool)), (∀ p ∈ u, p.1 < b) →
      (∀ t ∈ u.tails, evalCode c t ∈ F) →
        opLength NM.carrier
            ((umapM NM (evalCode c u))⁻¹ * evalRaw (truncGenM NM b) u)
          ≤ (3 * (u.length : ℝ) + 1) * ε
  | [], _, _ => by
      have hnil : evalCode c ([] : List (ℕ × Bool)) = 1 := rfl
      have hnil' : evalRaw (truncGenM NM b) ([] : List (ℕ × Bool)) = 1 := rfl
      rw [hnil, hnil', mul_one, opLength_inv]
      have h := umapM_one_le NM h1
      simp only [List.length_nil, Nat.cast_zero, mul_zero, zero_add, one_mul]
      exact h
  | p :: t, hlet, hsuf => by
      have htail : ∀ s ∈ t.tails, evalCode c s ∈ F := by
        intro s hs
        exact hsuf s (by rw [List.tails_cons]; exact List.mem_cons_of_mem _ hs)
      have hlett : ∀ q ∈ t, q.1 < b := fun q hq =>
        hlet q (List.mem_cons_of_mem _ hq)
      have ih := approxWordM NM b hε h1 hgen t hlett htail
      have hpb : p.1 < b := hlet p List.mem_cons_self
      have hmemp : evalCode c [p] ∈ F := hgen p.1 hpb p.2
      have hmemt : evalCode c t ∈ F := hsuf t (by
        rw [List.tails_cons]
        exact List.mem_cons_of_mem _ (MFMicrostate.self_mem_tails t))
      have hevcons : evalCode c (p :: t) = evalCode c [p] * evalCode c t :=
        evalRaw_cons' _ p t
      have hgcons : evalRaw (truncGenM NM b) (p :: t)
          = evalRaw (truncGenM NM b) [p] * evalRaw (truncGenM NM b) t :=
        evalRaw_cons' _ p t
      set a := umapM NM (evalCode c [p]) with ha
      set bb := umapM NM (evalCode c t) with hbb
      set A := evalRaw (truncGenM NM b) [p] with hA
      set B := evalRaw (truncGenM NM b) t with hB
      have hsplit :
          (umapM NM (evalCode c (p :: t)))⁻¹ * evalRaw (truncGenM NM b) (p :: t)
            = ((umapM NM (evalCode c (p :: t)))⁻¹ * (a * bb))
                * ((bb⁻¹ * (a⁻¹ * A) * bb) * (bb⁻¹ * B)) := by
        rw [hgcons]; group
      have hfirst :
          opLength NM.carrier ((umapM NM (evalCode c (p :: t)))⁻¹ * (a * bb)) ≤ ε := by
        have h := umapM_mul_le NM hmemp hmemt
        rw [← hevcons, ← ha, ← hbb] at h
        have hinv : (umapM NM (evalCode c (p :: t)))⁻¹ * (a * bb)
            = ((a * bb)⁻¹ * umapM NM (evalCode c (p :: t)))⁻¹ := by group
        rw [hinv, opLength_inv]
        exact h
      have hconj : opLength NM.carrier (bb⁻¹ * (a⁻¹ * A) * bb)
          = opLength NM.carrier (a⁻¹ * A) := by
        have hc := opLength_conj NM.carrier bb⁻¹ (a⁻¹ * A)
        rwa [inv_inv] at hc
      have hletter : opLength NM.carrier (a⁻¹ * A) ≤ 2 * ε := by
        rw [ha, hA]; exact letter_gapM NM b hε h1 hgen p hpb
      have hbound :
          opLength NM.carrier
              ((umapM NM (evalCode c (p :: t)))⁻¹ * evalRaw (truncGenM NM b) (p :: t))
            ≤ ε + (2 * ε + (3 * (t.length : ℝ) + 1) * ε) := by
        rw [hsplit]
        refine (opLength_mul_le _ _ _).trans (add_le_add hfirst ?_)
        refine (opLength_mul_le _ _ _).trans (add_le_add ?_ ih)
        rw [hconj]; exact hletter
      refine hbound.trans (le_of_eq ?_)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

end Forward

/-! ## Reading a norm model off microstates -/

/-- **The backward direction, at any positive separation.**  If every
challenge is answered with separation `δ`, the coded group is MF: a
`NormModel` on a finite set is read off the microstate answering the
challenge whose words separate the set's distinct pairs, at the scale the
area bound of the multiplication words prescribes. -/
theorem isOperatorMF_of_answers (c : PresentationCode) (δ : ℝ) (hδ : 0 < δ)
    (h : ∀ (W : List (List (ℕ × Bool))) (N k : ℕ),
      (∃ w ∈ W, EnumWordProblem c w) ∨
      ∃ M : NatMatrixMicrostate,
        (∀ j, j ≤ N → M.hlen (relatorAt c j) ≤ 1 / ((k : ℝ) + 1)) ∧
          ∀ w ∈ W, δ ≤ M.len w) :
    IsOperatorMF (Carrier c) := by
  classical
  haveI : Countable (Carrier c) := (evalCode_surjective c).countable
  refine (show IsWeakMF (Carrier c) from ⟨δ, hδ, ?_⟩).isOperatorMF
  intro F ε hε
  set wd : Carrier c → List (ℕ × Bool) :=
    Function.surjInv (evalCode_surjective c) with hwd
  have hwdspec : ∀ g : Carrier c, evalCode c (wd g) = g := fun g =>
    Function.surjInv_eq (evalCode_surjective c) g
  set pairs : Finset (Carrier c × Carrier c) :=
    (F ×ˢ F).filter fun q => q.1 ≠ q.2 with hpairs
  set W : List (List (ℕ × Bool)) :=
    pairs.toList.map fun q => invRaw (wd q.1) ++ wd q.2 with hW
  set mulWords : List (List (ℕ × Bool)) :=
    (F ×ˢ F).toList.map fun q =>
      invRaw (wd q.1 ++ wd q.2) ++ wd (q.1 * q.2) with hmul
  have hmultriv : ∀ u ∈ mulWords, evalCode c u = 1 := by
    intro u hu
    rw [hmul, List.mem_map] at hu
    obtain ⟨q, _hq, rfl⟩ := hu
    rw [evalCode_append, evalCode_invRaw, evalCode_append, hwdspec, hwdspec,
      hwdspec, inv_mul_cancel]
  obtain ⟨N, A, hNA⟩ := exists_matrix_area_bound_list c mulWords hmultriv
  obtain ⟨k, hk⟩ := exists_nat_gt ((A : ℝ) / ε)
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hAk : (A : ℝ) * (1 / ((k : ℝ) + 1)) ≤ ε := by
    have h1 : (A : ℝ) / ε < (k : ℝ) + 1 := by linarith
    have h2 : (A : ℝ) < ε * ((k : ℝ) + 1) := by
      have := (div_lt_iff₀ hε).1 h1
      linarith
    rw [mul_one_div]
    exact (div_le_iff₀ hkpos).2 (by linarith)
  rcases h W N k with hvoid | ⟨M, hrel, hsep⟩
  · exfalso
    obtain ⟨w, hw, hwtriv⟩ := hvoid
    rw [hW, List.mem_map] at hw
    obtain ⟨q, hq, rfl⟩ := hw
    rw [Finset.mem_toList, hpairs, Finset.mem_filter] at hq
    have hwt : evalCode c (invRaw (wd q.1) ++ wd q.2) = 1 := hwtriv
    rw [evalCode_append, evalCode_invRaw, hwdspec, hwdspec,
      inv_mul_eq_one] at hwt
    exact hq.2 hwt
  refine ⟨{
    carrier := M.model
    nonempty := M.card_pos
    map := fun g => ((evalRaw M.gen (wd g) : Matrix.unitaryGroup M.model ℂ) :
      Matrix M.model M.model ℂ)
    isUnitary := fun g => (evalRaw M.gen (wd g)).2
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg h' hh'
    have hmemword :
        (invRaw (wd g ++ wd h') ++ wd (g * h')) ∈ mulWords := by
      rw [hmul, List.mem_map]
      refine ⟨(g, h'), ?_, rfl⟩
      rw [Finset.mem_toList, Finset.mem_product]
      exact ⟨hg, hh'⟩
    have hval : M.len (invRaw (wd g ++ wd h') ++ wd (g * h'))
        = opLength M.model
            ((evalRaw M.gen (wd g) * evalRaw M.gen (wd h'))⁻¹
              * evalRaw M.gen (wd (g * h'))) := by
      rw [M.len_def, evalRaw_append, evalRaw_invRaw, evalRaw_append]
    have hbound := hNA M (1 / ((k : ℝ) + 1)) (by positivity) hrel _ hmemword
    rw [hval] at hbound
    have hfinal := hbound.trans hAk
    rw [opLength_inv_mul] at hfinal
    simpa using hfinal
  · intro g hg h' hh' hne
    have hmemword : (invRaw (wd h') ++ wd g) ∈ W := by
      rw [hW, List.mem_map]
      refine ⟨(h', g), ?_, rfl⟩
      rw [Finset.mem_toList, hpairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hh', hg⟩, Ne.symm hne⟩
    have hval : M.len (invRaw (wd h') ++ wd g)
        = opLength M.model
            ((evalRaw M.gen (wd h'))⁻¹ * evalRaw M.gen (wd g)) := by
      rw [M.len_def, evalRaw_append, evalRaw_invRaw]
    have hbound := hsep _ hmemword
    rw [hval, opLength_inv_mul] at hbound
    simpa using hbound

/-! ## The closed equivalence -/

/-- **MF-ness of a recursively enumerated coded group is exactly the assertion
that every closed challenge is answered.**  The right-hand side mentions the
coded group only through `EnumWordProblem`, a recursively enumerable
predicate; the microstate disjunct mentions it not at all. -/
theorem isOperatorMF_iff_forall_answersM (c : PresentationCode) :
    IsOperatorMF (Carrier c) ↔ ∀ W N k, AnswersM c W N k := by
  classical
  constructor
  · -- Forward: read a microstate off a separation-one model of a large ball.
    intro hMF W N k
    by_cases hvoid : ∃ w ∈ W, EnumWordProblem c w
    · exact Or.inl hvoid
    refine Or.inr ?_
    have hNA : IsNormApproximable (Carrier c) 1 :=
      OperatorMFLocalNormalization.isNormApproximable_one hMF
    set relWords : List (List (ℕ × Bool)) :=
      (List.range (N + 1)).map (rawRelator c) with hrelW
    set allWords : List (List (ℕ × Bool)) := W ++ relWords with hall
    set L : ℕ := (allWords.map List.length).foldr max 0 with hL
    set B : ℕ := 3 * L + 2 with hB
    have hBpos : (0 : ℝ) < (B : ℝ) := by rw [hB]; positivity
    set m : ℝ := min (1 / 2) (1 / ((k : ℝ) + 1)) with hm
    have hmpos : 0 < m := by
      rw [hm]; refine lt_min (by norm_num) ?_; positivity
    set ε : ℝ := m / (B : ℝ) with hεdef
    have hεpos : 0 < ε := div_pos hmpos hBpos
    have hBε : (B : ℝ) * ε = m := by rw [hεdef]; field_simp
    set bnd : ℕ := (allWords.map letterBound).foldr max 0 with hbnd
    set sufs : List (List (ℕ × Bool)) := allWords.flatMap List.tails with hsufs
    set gens : List (List (ℕ × Bool)) :=
      (List.range bnd).flatMap fun i => [[(i, true)], [(i, false)]] with hgens
    set F : Finset (Carrier c) :=
      ((([] : List (ℕ × Bool)) :: (sufs ++ gens)).map (evalCode c)).toFinset
      with hF
    have hmemF : ∀ u ∈ ([] : List (ℕ × Bool)) :: (sufs ++ gens),
        evalCode c u ∈ F := by
      intro u hu
      rw [hF, List.mem_toFinset, List.mem_map]
      exact ⟨u, hu, rfl⟩
    have h1F : (1 : Carrier c) ∈ F := by
      have h := hmemF [] List.mem_cons_self
      exact h
    have hgenF : ∀ i, i < bnd → ∀ s : Bool, evalCode c [(i, s)] ∈ F := by
      intro i hi s
      refine hmemF _ (List.mem_cons_of_mem _ (List.mem_append_right _ ?_))
      rw [hgens, List.mem_flatMap]
      exact ⟨i, List.mem_range.2 hi, by cases s <;> simp⟩
    have hsufF : ∀ u ∈ allWords, ∀ t ∈ u.tails, evalCode c t ∈ F := by
      intro u hu t ht
      refine hmemF _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))
      rw [hsufs, List.mem_flatMap]
      exact ⟨u, hu, ht⟩
    have hletF : ∀ u ∈ allWords, ∀ p ∈ u, p.1 < bnd := by
      intro u hu p hp
      have hb : letterBound u ≤ bnd := by
        rw [hbnd]; exact MFMicrostate.le_foldr_max letterBound allWords u hu
      exact lt_of_lt_of_le (lt_letterBound hp) hb
    obtain ⟨NM⟩ := hNA F ε hεpos
    have hone := umapM_one_le NM h1F
    refine ⟨modelMicrostateM NM bnd, ?_, ?_⟩
    · intro j hj
      have hrall : rawRelator c j ∈ allWords := by
        rw [hall]
        refine List.mem_append_right _ ?_
        rw [hrelW, List.mem_map]
        exact ⟨j, List.mem_range.2 (Nat.lt_succ_of_le hj), rfl⟩
      have htriv : evalCode c (rawRelator c j) = 1 :=
        (evalCode_eq_one_iff c (rawRelator c j)).2
          (Subgroup.subset_normalClosure (relatorAt_mem_relatorSet c j))
      have hgap := approxWordM NM bnd hεpos.le h1F hgenF (rawRelator c j)
        (hletF _ hrall) (hsufF _ hrall)
      rw [htriv] at hgap
      have hstep := MFMicrostate.Microstate.opLength_le_gap
        (evalRaw (truncGenM NM bnd) (rawRelator c j)) (umapM NM 1)
      rw [MFMicrostate.Microstate.opLength_gap_symm] at hstep
      have hlen : (rawRelator c j).length ≤ L := by
        rw [hL]
        exact MFMicrostate.le_foldr_max List.length allWords _ hrall
      have hb : 3 * ((rawRelator c j).length : ℝ) + 2 ≤ (B : ℝ) := by
        have hLle : ((rawRelator c j).length : ℝ) ≤ (L : ℝ) := by
          exact_mod_cast hlen
        rw [hB]; push_cast; linarith
      have hcoef : ε + (3 * ((rawRelator c j).length : ℝ) + 1) * ε
          ≤ (B : ℝ) * ε := by
        calc ε + (3 * ((rawRelator c j).length : ℝ) + 1) * ε
            = (3 * ((rawRelator c j).length : ℝ) + 2) * ε := by ring
          _ ≤ (B : ℝ) * ε := mul_le_mul_of_nonneg_right hb hεpos.le
      have hfinal : (B : ℝ) * ε ≤ 1 / ((k : ℝ) + 1) := by
        rw [hBε, hm]; exact min_le_right _ _
      have hval : (modelMicrostateM NM bnd).hlen (relatorAt c j)
          = opLength NM.carrier
              (evalRaw (truncGenM NM bnd) (rawRelator c j)) :=
        (modelMicrostateM NM bnd).len_def (rawRelator c j)
      rw [hval]
      linarith
    · intro w hw
      have hwall : w ∈ allWords := by
        rw [hall]; exact List.mem_append_left _ hw
      have hne : evalCode c w ≠ 1 := fun hcon => hvoid ⟨w, hw, hcon⟩
      have hwF : evalCode c w ∈ F :=
        hsufF w hwall w (MFMicrostate.self_mem_tails w)
      have hgap := approxWordM NM bnd hεpos.le h1F hgenF w (hletF w hwall)
        (hsufF w hwall)
      have hsep : (1 : ℝ)
          ≤ opLength NM.carrier ((umapM NM 1)⁻¹ * umapM NM (evalCode c w)) := by
        rw [opLength_inv_mul]
        simpa using NM.separated (evalCode c w) hwF 1 h1F hne
      have hsplit := MFMicrostate.Microstate.opLength_le_gap
        ((umapM NM 1)⁻¹ * umapM NM (evalCode c w)) (umapM NM (evalCode c w))
      have hgapsmall : opLength NM.carrier
          (((umapM NM 1)⁻¹ * umapM NM (evalCode c w))⁻¹ * umapM NM (evalCode c w))
            ≤ ε := by
        have hEq : ((umapM NM 1)⁻¹ * umapM NM (evalCode c w))⁻¹
              * umapM NM (evalCode c w)
            = (umapM NM (evalCode c w))⁻¹ * umapM NM 1
                * ((umapM NM (evalCode c w))⁻¹)⁻¹ := by
          group
        rw [hEq, opLength_conj]
        exact hone
      have hbig : (1 : ℝ) - ε ≤ opLength NM.carrier (umapM NM (evalCode c w)) := by
        linarith
      have hstep := MFMicrostate.Microstate.opLength_le_gap
        (umapM NM (evalCode c w)) (evalRaw (truncGenM NM bnd) w)
      have hlen : w.length ≤ L := by
        rw [hL]; exact MFMicrostate.le_foldr_max List.length allWords w hwall
      have hb : 3 * (w.length : ℝ) + 2 ≤ (B : ℝ) := by
        have hLle : (w.length : ℝ) ≤ (L : ℝ) := by exact_mod_cast hlen
        rw [hB]; push_cast; linarith
      have hcoef : ε + (3 * (w.length : ℝ) + 1) * ε ≤ (B : ℝ) * ε := by
        calc ε + (3 * (w.length : ℝ) + 1) * ε
            = (3 * (w.length : ℝ) + 2) * ε := by ring
          _ ≤ (B : ℝ) * ε := mul_le_mul_of_nonneg_right hb hεpos.le
      have hhalf : (B : ℝ) * ε ≤ 1 / 2 := by
        rw [hBε, hm]; exact min_le_left _ _
      rw [modelMicrostateM_len]
      linarith
  · -- Backward: read a fixed-separation model off microstates.
    intro h
    exact isOperatorMF_of_answers c (1 / 2) (by norm_num) h

/-! ## The open equivalence -/

theorem finer_scale_lt_M (k : ℕ) :
    1 / ((((2 * k + 1 : ℕ) : ℝ)) + 1) < 1 / ((k : ℝ) + 1) := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hrewrite : ((((2 * k + 1 : ℕ) : ℝ)) + 1) =
      2 * ((k : ℝ) + 1) := by push_cast; ring
  rw [hrewrite]
  calc
    1 / (2 * ((k : ℝ) + 1)) = (1 / 2 : ℝ) * (1 / ((k : ℝ) + 1)) := by
      field_simp
    _ < 1 * (1 / ((k : ℝ) + 1)) :=
      mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ = 1 / ((k : ℝ) + 1) := one_mul _

/-- **MF-ness is exactly the assertion that every strict-open challenge is
answered.**  Forward, query the closed form at scale `2k+1`; backward, the
closed argument at separation `1/3`. -/
theorem isOperatorMF_iff_forall_openAnswersM (c : PresentationCode) :
    IsOperatorMF (Carrier c) ↔ ∀ W N k, AnswersOpenM c W N k := by
  classical
  constructor
  · intro hMF W N k
    rcases (isOperatorMF_iff_forall_answersM c).1 hMF W N (2 * k + 1) with
      hvoid | ⟨M, hrel, hsep⟩
    · exact Or.inl hvoid
    · refine Or.inr ⟨M, ?_, ?_⟩
      · intro j hj
        exact (hrel j hj).trans_lt (finer_scale_lt_M k)
      · intro w hw
        have := hsep w hw
        linarith
  · intro h
    refine isOperatorMF_of_answers c (1 / 3) (by norm_num) ?_
    intro W N k
    rcases h W N k with hvoid | ⟨M, hrel, hsep⟩
    · exact Or.inl hvoid
    · exact Or.inr ⟨M, fun j hj => (hrel j hj).le, fun w hw => (hsep w hw).le⟩

end

end MFEnumeratedPi02
end GroupApproximation

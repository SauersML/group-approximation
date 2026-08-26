import GroupApproximation.Computability.MicrostateNormalForm
import GroupApproximation.Sofic.SoficAmplification

/-!
# The oracle-free `∀∃` normal form for soficity of a presentation code

`Computability.MicrostateNormalForm` removes the coded group from the
statement of operator-MF-ness by replacing norm models with *microstates*:
finite data consisting of a nonempty finite model together with one unitary
per generator.  This file does the same for **soficity**, with permutations in
place of unitaries.

The change of carrier is not cosmetic.  A microstate of unitaries is
witnessed by complex matrices, and the two inequalities a challenge asks about
are comparisons of operator norms; making them decidable is the whole content
of `Computability.MFRecognitionPi02`, and it needs Gaussian-rational
approximants.  A microstate of *permutations* of `Fin (m+1)` is finite
combinatorial data, and the normalized Hamming distance of a product of
permutations from the identity is an exact rational number computed by
counting moved points.  So the second disjunct of the normal form below is not
merely an existential over a `Primcodable` type: it is an existential over a
`Primcodable` type with a **decidable** matrix, which is what makes the full
`Π⁰₂` statement reachable (`Computability.SoficRecognitionPi02`).

## The normal form

A challenge is a finite list `W` of raw words together with an accuracy index
`k`.  It is *answered* when either

* some word of `W` is trivial in the coded group --- in which case the
  challenge asked for the impossible and is void --- or
* a permutation microstate displaces every listed relator by at most
  `1/(k+1)` and every word of `W` by at least `1/2`.

`isSofic_iff_forall_answers` says soficity is exactly the assertion that every
challenge is answered.

## The two directions

Forward, a permutation microstate is read off a `SoficModel` on a ball large
enough to contain every subword of every listed word: its generators are the
model's values on the one-letter words, and the word induction `approxWord`
bounds the gap between evaluating a word in the microstate and evaluating it
in the model by a multiple of the model's accuracy, linear in the word's
length.  Separation survives with room to spare, which is why the threshold is
`1/2` rather than `1 - ε`.

Backward, a model is read off a microstate by sending a group element to the
microstate's value on a chosen word for it.  Separation is immediate but only
at the fixed constant `1/2`; `SoficAmplification.isSofic_of_isSoficWeak`
converts that into the sharp definition by passing to a tensor power, so the
fixed threshold costs nothing.  Multiplicativity is the substantive half: two
words for the same element must land close together, and that is exactly what
`exists_area_bound_list` supplies, with the accuracy index chosen after the
area count.

## Research nodes

* `research/sofic-recognition-has-a-pi2-upper-bound.md` --- the claim, whose
  displayed normal form `(SOF1)` this file is.
* `research/sofic-recognition-finite-presentations-arithmetical-position.md`
  --- the position statement this upper bound is the upper half of.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace SoficMicrostateNormalForm

open PresentationCodes AdianRabinWordProblem RawWord MFMicrostate

/-! ## Hamming distance as a bi-invariant length

Every estimate below is run through displacement from the identity, so the
first thing to record is that the normalized Hamming distance *is* such a
displacement: it is the length of the quotient.  This is one application of
left invariance, and it is what lets the four properties an area bound needs
be stated about a single-argument function. -/

theorem hammingDistance_eq_displacement (Y : FiniteModel) (p q : Equiv.Perm Y) :
    hammingDistance Y p q = hammingDistance Y (q⁻¹ * p) 1 := by
  have h := hammingDistance_left_invariant Y q⁻¹ p q
  rw [inv_mul_cancel] at h
  exact h.symm

/-! ## Permutation microstates -/

/-- **A permutation microstate for a presentation code.**  A nonempty finite
model together with one permutation per generator: finite data, and no
reference to the coded group. -/
structure PermMicrostate (c : PresentationCode) where
  /-- The finite model the permutations act on. -/
  carrier : FiniteModel
  /-- The model is nonempty; a microstate on no points separates nothing. -/
  nonempty : 0 < Fintype.card carrier
  /-- One permutation per generator. -/
  gen : Fin (genCount c) → Equiv.Perm carrier

namespace PermMicrostate

variable {c : PresentationCode}

/-- The homomorphism a permutation microstate induces on the free group.  This
is exact: a microstate is a genuine permutation representation of the *free*
group, and only its behaviour on the relators is approximate. -/
def hom (M : PermMicrostate c) :
    FreeGroup (Fin (genCount c)) →* Equiv.Perm M.carrier :=
  FreeGroup.lift M.gen

/-- Hamming displacement of a free-group element in a permutation
microstate. -/
noncomputable def hlen (M : PermMicrostate c)
    (x : FreeGroup (Fin (genCount c))) : ℝ :=
  hammingDistance M.carrier (M.hom x) 1

/-- Hamming displacement of a raw word in a permutation microstate. -/
noncomputable def len (M : PermMicrostate c) (w : List (ℕ × Bool)) : ℝ :=
  M.hlen (wordOf c w)

@[simp] theorem hlen_def (M : PermMicrostate c)
    (x : FreeGroup (Fin (genCount c))) :
    M.hlen x = hammingDistance M.carrier (M.hom x) 1 := rfl

@[simp] theorem len_def (M : PermMicrostate c) (w : List (ℕ × Bool)) :
    M.len w = hammingDistance M.carrier (M.hom (wordOf c w)) 1 := rfl

@[simp] theorem hom_of (M : PermMicrostate c) (j : Fin (genCount c)) :
    M.hom (FreeGroup.of j) = M.gen j := by simp [hom]

@[simp] theorem hlen_one (M : PermMicrostate c) : M.hlen 1 = 0 := by
  rw [hlen, map_one, hammingDistance_self]

theorem hlen_nonneg (M : PermMicrostate c) (x : FreeGroup (Fin (genCount c))) :
    0 ≤ M.hlen x := hammingDistance_nonnegative _ _ _

theorem hlen_le_one (M : PermMicrostate c) (x : FreeGroup (Fin (genCount c))) :
    M.hlen x ≤ 1 := hammingDistance_le_one _ _ _

/-- Displacement is subadditive. -/
theorem hlen_mul_le (M : PermMicrostate c)
    (x y : FreeGroup (Fin (genCount c))) :
    M.hlen (x * y) ≤ M.hlen x + M.hlen y := by
  rw [hlen, hlen, hlen, map_mul]
  have hstep : hammingDistance M.carrier (M.hom x * M.hom y) (M.hom x)
      = hammingDistance M.carrier (M.hom y) 1 := by
    have h := hammingDistance_left_invariant M.carrier (M.hom x) (M.hom y) 1
    rwa [mul_one] at h
  have htri := hammingDistance_triangle M.carrier
    (M.hom x * M.hom y) (M.hom x) 1
  rw [hstep] at htri
  linarith

/-- Displacement is inversion-invariant. -/
theorem hlen_inv (M : PermMicrostate c) (x : FreeGroup (Fin (genCount c))) :
    M.hlen x⁻¹ = M.hlen x := by
  rw [hlen, hlen, map_inv]
  have h := hammingDistance_right_invariant M.carrier (M.hom x)⁻¹ 1 (M.hom x)
  rw [inv_mul_cancel, one_mul] at h
  rw [← h]
  exact hammingDistance_comm _ _ _

/-- Displacement is conjugation-invariant. -/
theorem hlen_conj (M : PermMicrostate c)
    (t x : FreeGroup (Fin (genCount c))) :
    M.hlen (t * x * t⁻¹) = M.hlen x := by
  rw [hlen, hlen, map_mul, map_mul, map_inv]
  have h1 := hammingDistance_right_invariant M.carrier
    (M.hom t * M.hom x * (M.hom t)⁻¹) 1 (M.hom t)
  have heq : M.hom t * M.hom x * (M.hom t)⁻¹ * M.hom t
      = M.hom t * M.hom x := by group
  rw [heq, one_mul] at h1
  have h2 := hammingDistance_left_invariant M.carrier
    (M.hom t) (M.hom x) 1
  rw [mul_one] at h2
  rw [← h1, h2]

@[simp] theorem len_nil (M : PermMicrostate c) : M.len [] = 0 := by
  rw [len, wordOf_nil, hlen_one]

theorem len_nonneg (M : PermMicrostate c) (w : List (ℕ × Bool)) :
    0 ≤ M.len w := hlen_nonneg _ _

theorem len_append (M : PermMicrostate c) (u v : List (ℕ × Bool)) :
    M.len (u ++ v) ≤ M.len u + M.len v := by
  rw [len, len, len, wordOf_append]
  exact hlen_mul_le _ _ _

end PermMicrostate

/-! ## The area bound

Verbatim the argument of `MFMicrostate.areaSubgroup`, which uses only the four
displacement properties proved above and nothing about unitaries. -/

/-- The free-group elements whose Hamming displacement is bounded by a fixed
multiple of the relator displacement, uniformly over permutation
microstates. -/
noncomputable def areaSubgroupPerm (c : PresentationCode)
    (S : Set (FreeGroup (Fin (genCount c)))) :
    Subgroup (FreeGroup (Fin (genCount c))) where
  carrier := {x | ∃ N : ℕ, ∀ (M : PermMicrostate c) (δ : ℝ), 0 ≤ δ →
    (∀ r ∈ S, M.hlen r ≤ δ) → M.hlen x ≤ (N : ℝ) * δ}
  one_mem' := by
    refine ⟨0, fun M δ _ _ => ?_⟩
    rw [M.hlen_one, Nat.cast_zero, zero_mul]
  mul_mem' := by
    rintro x y ⟨Nx, hx⟩ ⟨Ny, hy⟩
    refine ⟨Nx + Ny, fun M δ hδ hrel => ?_⟩
    refine (M.hlen_mul_le x y).trans ?_
    have := add_le_add (hx M δ hδ hrel) (hy M δ hδ hrel)
    rwa [← add_mul, ← Nat.cast_add] at this
  inv_mem' := by
    rintro x ⟨N, hx⟩
    refine ⟨N, fun M δ hδ hrel => ?_⟩
    rw [M.hlen_inv]
    exact hx M δ hδ hrel

/-- Displacement is conjugation-invariant, so the area subgroup is normal. -/
instance areaSubgroupPerm_normal (c : PresentationCode)
    (S : Set (FreeGroup (Fin (genCount c)))) :
    (areaSubgroupPerm c S).Normal where
  conj_mem := by
    rintro x ⟨N, hx⟩ g
    refine ⟨N, fun M δ hδ hrel => ?_⟩
    rw [M.hlen_conj]
    exact hx M δ hδ hrel

theorem mem_areaSubgroupPerm_iff {c : PresentationCode}
    {S : Set (FreeGroup (Fin (genCount c)))}
    {x : FreeGroup (Fin (genCount c))} :
    x ∈ areaSubgroupPerm c S ↔ ∃ N : ℕ, ∀ (M : PermMicrostate c) (δ : ℝ),
      0 ≤ δ → (∀ r ∈ S, M.hlen r ≤ δ) → M.hlen x ≤ (N : ℝ) * δ := Iff.rfl

theorem subset_areaSubgroupPerm (c : PresentationCode)
    (S : Set (FreeGroup (Fin (genCount c)))) :
    S ⊆ (areaSubgroupPerm c S : Set (FreeGroup (Fin (genCount c)))) := by
  intro r hr
  refine mem_areaSubgroupPerm_iff.2 ⟨1, fun M δ _ hrel => ?_⟩
  rw [Nat.cast_one, one_mul]
  exact hrel r hr

/-- **Approximate relators force approximate triviality**, for permutation
microstates.  An element of the normal closure of `S` carries an area count
that bounds its displacement in every microstate, in terms of the displacement
of `S`. -/
theorem exists_area_bound_perm (c : PresentationCode)
    {S : Set (FreeGroup (Fin (genCount c)))}
    {x : FreeGroup (Fin (genCount c))}
    (hx : x ∈ Subgroup.normalClosure S) :
    ∃ N : ℕ, ∀ (M : PermMicrostate c) (δ : ℝ), 0 ≤ δ →
      (∀ r ∈ S, M.hlen r ≤ δ) → M.hlen x ≤ (N : ℝ) * δ :=
  mem_areaSubgroupPerm_iff.1
    (Subgroup.normalClosure_le_normal (N := areaSubgroupPerm c S)
      (subset_areaSubgroupPerm c S) hx)

/-- Relator displacement measured on the listed relator words bounds it on the
whole relator set. -/
theorem hlen_relatorSet_le {c : PresentationCode} {M : PermMicrostate c}
    {δ : ℝ} (h : ∀ u ∈ c.2, M.len u ≤ δ) :
    ∀ r ∈ relatorSet c, M.hlen r ≤ δ := by
  intro r hr
  obtain ⟨u, hu, rfl⟩ := mem_relatorSet_iff.1 hr
  exact h u hu

/-- **The area bound, for a finite list of trivial words at once.** -/
theorem exists_area_bound_list_perm (c : PresentationCode)
    (L : List (List (ℕ × Bool))) (hL : ∀ u ∈ L, WordProblem c u) :
    ∃ N : ℕ, ∀ (M : PermMicrostate c) (δ : ℝ), 0 ≤ δ →
      (∀ r ∈ c.2, M.len r ≤ δ) → ∀ u ∈ L, M.len u ≤ (N : ℝ) * δ := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons a t ih =>
      obtain ⟨Nt, hNt⟩ := ih fun u hu => hL u (List.mem_cons_of_mem _ hu)
      obtain ⟨Na, hNa⟩ :=
        exists_area_bound_perm c
          (wordOf_mem_normalClosure (hL a List.mem_cons_self))
      refine ⟨max Na Nt, fun M δ hδ hrel u hu => ?_⟩
      have hmono : ∀ N : ℕ, N ≤ max Na Nt →
          ∀ y : ℝ, y ≤ (N : ℝ) * δ → y ≤ ((max Na Nt : ℕ) : ℝ) * δ := by
        intro N hN y hy
        refine hy.trans (mul_le_mul_of_nonneg_right ?_ hδ)
        exact_mod_cast hN
      rcases List.mem_cons.1 hu with rfl | hu'
      · exact hmono Na (le_max_left _ _) _
          (hNa M δ hδ (hlen_relatorSet_le hrel))
      · exact hmono Nt (le_max_right _ _) _ (hNt M δ hδ hrel u hu')

/-! ## Challenges and answers -/

/-- The conditions a challenge asks a permutation microstate for. -/
noncomputable def Passes (c : PresentationCode) (W : List (List (ℕ × Bool)))
    (k : ℕ) (M : PermMicrostate c) : Prop :=
  (∀ r ∈ c.2, M.len r ≤ 1 / ((k : ℝ) + 1)) ∧ (∀ w ∈ W, 1 / 2 ≤ M.len w)

/-- **One challenge, answered.**  Either the challenge is void because one of
its words is trivial in the coded group, or a permutation microstate meets
it. -/
noncomputable def Answers (c : PresentationCode) (W : List (List (ℕ × Bool)))
    (k : ℕ) : Prop :=
  (∃ w ∈ W, WordProblem c w) ∨ ∃ M : PermMicrostate c, Passes c W k M

/-! ## Reading a permutation microstate off a sofic model -/

section Forward

variable {c : PresentationCode} {F : Finset (Carrier c)} {ε : ℝ}

/-- The free-group homomorphism the model's one-letter values generate, stated
at the model's own carrier so that every estimate below lives in one type. -/
def modelHom (SM : SoficModel (Carrier c) F ε) :
    FreeGroup (Fin (genCount c)) →* Equiv.Perm SM.carrier :=
  FreeGroup.lift fun j => SM.map (ev c [((j : ℕ), true)])

@[simp] theorem modelHom_of (SM : SoficModel (Carrier c) F ε)
    (j : Fin (genCount c)) :
    modelHom SM (FreeGroup.of j) = SM.map (ev c [((j : ℕ), true)]) := by
  simp [modelHom]

/-- The permutation microstate a sofic model determines. -/
def toPermMicrostate (SM : SoficModel (Carrier c) F ε) : PermMicrostate c where
  carrier := SM.carrier
  nonempty := SM.nonempty
  gen := fun j => SM.map (ev c [((j : ℕ), true)])

@[simp] theorem toPermMicrostate_len (SM : SoficModel (Carrier c) F ε)
    (w : List (ℕ × Bool)) :
    (toPermMicrostate SM).len w
      = hammingDistance SM.carrier (modelHom SM (wordOf c w)) 1 := rfl

/-- The value at the identity is close to the identity. -/
theorem map_one_le (SM : SoficModel (Carrier c) F ε)
    (h1 : (1 : Carrier c) ∈ F) :
    hammingDistance SM.carrier (SM.map 1) 1 ≤ ε := by
  have h := SM.multiplicative 1 h1 1 h1
  rw [mul_one] at h
  have hr := hammingDistance_right_invariant SM.carrier 1 (SM.map 1) (SM.map 1)
  rw [one_mul] at hr
  rw [hr] at h
  rwa [hammingDistance_comm]

/-- The value at an inverse is close to the inverse of the value. -/
theorem map_inv_le (SM : SoficModel (Carrier c) F ε)
    (h1 : (1 : Carrier c) ∈ F) {g : Carrier c} (hg : g ∈ F) (hg' : g⁻¹ ∈ F) :
    hammingDistance SM.carrier (SM.map g⁻¹) (SM.map g)⁻¹ ≤ 2 * ε := by
  have h := SM.multiplicative g hg g⁻¹ hg'
  rw [mul_inv_cancel] at h
  have hone : hammingDistance SM.carrier 1 (SM.map 1) ≤ ε := by
    rw [hammingDistance_comm]
    exact map_one_le SM h1
  have htri := hammingDistance_triangle SM.carrier 1 (SM.map 1)
    (SM.map g * SM.map g⁻¹)
  have hb : hammingDistance SM.carrier 1 (SM.map g * SM.map g⁻¹) ≤ 2 * ε := by
    linarith
  have hl := hammingDistance_left_invariant SM.carrier (SM.map g)⁻¹ 1
    (SM.map g * SM.map g⁻¹)
  have heq1 : (SM.map g)⁻¹ * 1 = (SM.map g)⁻¹ := mul_one _
  have heq2 : (SM.map g)⁻¹ * (SM.map g * SM.map g⁻¹) = SM.map g⁻¹ := by group
  rw [heq1, heq2] at hl
  rw [hammingDistance_comm, hl]
  exact hb

/-- The microstate's value on a one-letter word is within `2ε` of the
model's. -/
theorem letter_gap (SM : SoficModel (Carrier c) F ε) (hε : 0 ≤ ε)
    (h1 : (1 : Carrier c) ∈ F)
    (hgen : ∀ (j : Fin (genCount c)) (s : Bool), ev c [((j : ℕ), s)] ∈ F)
    (p : ℕ × Bool) :
    hammingDistance SM.carrier (SM.map (ev c [p]))
        (modelHom SM (wordOf c [p])) ≤ 2 * ε := by
  obtain ⟨i, s⟩ := p
  cases s with
  | true =>
      rw [wordOf_pos, modelHom_of, ← ev_letter c i true, hammingDistance_self]
      linarith
  | false =>
      have hpos : ev c [(((letterOf c i : Fin (genCount c)) : ℕ), true)]
          = ev c [(i, true)] := (ev_letter c i true).symm
      have hg : ev c [(i, true)] ∈ F := by
        rw [ev_letter c i true]; exact hgen (letterOf c i) true
      have hg' : (ev c [(i, true)])⁻¹ ∈ F := by
        rw [← ev_letter_neg, ev_letter c i false]
        exact hgen (letterOf c i) false
      rw [wordOf_neg, map_inv, modelHom_of, hpos, ev_letter_neg]
      exact map_inv_le SM h1 hg hg'

/-- **The word induction.**  Evaluating a word in the microstate and
evaluating it in the model differ by at most a multiple of the accuracy,
linear in the word's length. -/
theorem approxWord (SM : SoficModel (Carrier c) F ε) (hε : 0 ≤ ε)
    (h1 : (1 : Carrier c) ∈ F)
    (hgen : ∀ (j : Fin (genCount c)) (s : Bool), ev c [((j : ℕ), s)] ∈ F) :
    ∀ (u : List (ℕ × Bool)), (∀ t ∈ u.tails, ev c t ∈ F) →
      hammingDistance SM.carrier (SM.map (ev c u)) (modelHom SM (wordOf c u))
        ≤ (3 * (u.length : ℝ) + 1) * ε
  | [], _ => by
      rw [ev_nil, wordOf_nil, map_one]
      have h := map_one_le SM h1
      simp only [List.length_nil, Nat.cast_zero, mul_zero, zero_add, one_mul]
      exact h
  | p :: t, hsuf => by
      have htail : ∀ s ∈ t.tails, ev c s ∈ F := by
        intro s hs
        exact hsuf s (by rw [List.tails_cons]; exact List.mem_cons_of_mem _ hs)
      have ih := approxWord SM hε h1 hgen t htail
      have hmemp : ev c [p] ∈ F := by
        obtain ⟨i, s⟩ := p
        rw [ev_letter c i s]; exact hgen (letterOf c i) s
      have hmemt : ev c t ∈ F := hsuf t (by
        rw [List.tails_cons]
        exact List.mem_cons_of_mem _ (self_mem_tails t))
      have hevcons : ev c (p :: t) = ev c [p] * ev c t := by
        show ev c ([p] ++ t) = _
        rw [ev_append]
      have hwordcons : wordOf c (p :: t) = wordOf c [p] * wordOf c t := by
        show wordOf c ([p] ++ t) = _
        rw [wordOf_append]
      have hhom : modelHom SM (wordOf c (p :: t))
          = modelHom SM (wordOf c [p]) * modelHom SM (wordOf c t) := by
        rw [hwordcons, map_mul]
      have hfirst : hammingDistance SM.carrier (SM.map (ev c (p :: t)))
          (SM.map (ev c [p]) * SM.map (ev c t)) ≤ ε := by
        have h := SM.multiplicative (ev c [p]) hmemp (ev c t) hmemt
        rwa [← hevcons] at h
      have hsecond : hammingDistance SM.carrier
          (SM.map (ev c [p]) * SM.map (ev c t))
          (modelHom SM (wordOf c [p]) * SM.map (ev c t)) ≤ 2 * ε := by
        rw [hammingDistance_right_invariant]
        exact letter_gap SM hε h1 hgen p
      have hthird : hammingDistance SM.carrier
          (modelHom SM (wordOf c [p]) * SM.map (ev c t))
          (modelHom SM (wordOf c [p]) * modelHom SM (wordOf c t))
            ≤ (3 * (t.length : ℝ) + 1) * ε := by
        rw [hammingDistance_left_invariant]
        exact ih
      have htri1 := hammingDistance_triangle SM.carrier
        (SM.map (ev c (p :: t)))
        (SM.map (ev c [p]) * SM.map (ev c t))
        (modelHom SM (wordOf c [p]) * modelHom SM (wordOf c t))
      have htri2 := hammingDistance_triangle SM.carrier
        (SM.map (ev c [p]) * SM.map (ev c t))
        (modelHom SM (wordOf c [p]) * SM.map (ev c t))
        (modelHom SM (wordOf c [p]) * modelHom SM (wordOf c t))
      have hbound : hammingDistance SM.carrier (SM.map (ev c (p :: t)))
          (modelHom SM (wordOf c (p :: t)))
            ≤ ε + (2 * ε + (3 * (t.length : ℝ) + 1) * ε) := by
        rw [hhom]
        linarith
      refine hbound.trans (le_of_eq ?_)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

end Forward

/-! ## The equivalence -/

/-- **Soficity of a coded group is exactly the assertion that every challenge
is answered.**

The right-hand side never mentions equality in the coded group except through
`WordProblem`, and the microstate disjunct mentions the coded group not at
all. -/
theorem isSofic_iff_forall_answers (c : PresentationCode) :
    IsSofic (Carrier c) ↔ ∀ W k, Answers c W k := by
  classical
  constructor
  · -- Forward: read a permutation microstate off a sofic model of a ball.
    intro hSofic W k
    by_cases hvoid : ∃ w ∈ W, WordProblem c w
    · exact Or.inl hvoid
    refine Or.inr ?_
    set allWords : List (List (ℕ × Bool)) := W ++ c.2 with hall
    set L : ℕ := (allWords.map List.length).foldr max 0 with hL
    set B : ℕ := 3 * L + 3 with hB
    have hBpos : (0 : ℝ) < (B : ℝ) := by rw [hB]; positivity
    set m : ℝ := min (1 / 2) (1 / ((k : ℝ) + 1)) with hm
    have hmpos : 0 < m := by
      rw [hm]; refine lt_min (by norm_num) ?_; positivity
    set ε : ℝ := m / (B : ℝ) with hεdef
    have hεpos : 0 < ε := div_pos hmpos hBpos
    have hBε : (B : ℝ) * ε = m := by rw [hεdef]; field_simp
    set sufs : List (List (ℕ × Bool)) := allWords.flatMap List.tails with hsufs
    set gens : List (List (ℕ × Bool)) :=
      (List.finRange (genCount c)).flatMap
        fun j : Fin (genCount c) =>
          [[((j : ℕ), true)], [((j : ℕ), false)]] with hgens
    set F : Finset (Carrier c) :=
      (([] :: (sufs ++ gens)).map (ev c)).toFinset with hF
    have hmemF : ∀ u ∈ ([] : List (ℕ × Bool)) :: (sufs ++ gens),
        ev c u ∈ F := by
      intro u hu
      rw [hF, List.mem_toFinset, List.mem_map]
      exact ⟨u, hu, rfl⟩
    have h1F : (1 : Carrier c) ∈ F := by
      have h := hmemF [] List.mem_cons_self
      rwa [ev_nil] at h
    have hgenF : ∀ (j : Fin (genCount c)) (s : Bool),
        ev c [((j : ℕ), s)] ∈ F := by
      intro j s
      refine hmemF _ (List.mem_cons_of_mem _ (List.mem_append_right _ ?_))
      rw [hgens, List.mem_flatMap]
      exact ⟨j, List.mem_finRange j, by cases s <;> simp⟩
    have hsufF : ∀ u ∈ allWords, ∀ t ∈ u.tails, ev c t ∈ F := by
      intro u hu t ht
      refine hmemF _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))
      rw [hsufs, List.mem_flatMap]
      exact ⟨u, hu, ht⟩
    obtain ⟨SM⟩ := hSofic F ε hεpos
    have hone := map_one_le SM h1F
    refine ⟨toPermMicrostate SM, ?_, ?_⟩
    · intro r hr
      have hrall : r ∈ allWords := by
        rw [hall]; exact List.mem_append_right _ hr
      have htriv : ev c r = 1 := wordProblem_of_mem_relators hr
      have hgap := approxWord SM hεpos.le h1F hgenF r (hsufF r hrall)
      rw [htriv] at hgap
      have htri := hammingDistance_triangle SM.carrier
        (modelHom SM (wordOf c r)) (SM.map 1) 1
      rw [hammingDistance_comm SM.carrier (modelHom SM (wordOf c r))
        (SM.map 1)] at htri
      have hlen : r.length ≤ L := by
        rw [hL]; exact le_foldr_max List.length allWords r hrall
      have hb : 3 * (r.length : ℝ) + 2 ≤ (B : ℝ) := by
        have hLle : (r.length : ℝ) ≤ (L : ℝ) := by exact_mod_cast hlen
        rw [hB]; push_cast; linarith
      have hcoef : ε + (3 * (r.length : ℝ) + 1) * ε ≤ (B : ℝ) * ε := by
        calc ε + (3 * (r.length : ℝ) + 1) * ε
            = (3 * (r.length : ℝ) + 2) * ε := by ring
          _ ≤ (B : ℝ) * ε := mul_le_mul_of_nonneg_right hb hεpos.le
      have hfinal : (B : ℝ) * ε ≤ 1 / ((k : ℝ) + 1) := by
        rw [hBε, hm]; exact min_le_right _ _
      rw [toPermMicrostate_len]
      linarith
    · intro w hw
      have hwall : w ∈ allWords := by
        rw [hall]; exact List.mem_append_left _ hw
      have hne : ev c w ≠ 1 := fun hcon => hvoid ⟨w, hw, hcon⟩
      have hwF : ev c w ∈ F := hsufF w hwall w (self_mem_tails w)
      have hgap := approxWord SM hεpos.le h1F hgenF w (hsufF w hwall)
      have hsep : (1 : ℝ) - ε
          ≤ hammingDistance SM.carrier (SM.map (ev c w)) (SM.map 1) :=
        SM.separated (ev c w) hwF 1 h1F hne
      have htri1 := hammingDistance_triangle SM.carrier
        (SM.map (ev c w)) (modelHom SM (wordOf c w)) (SM.map 1)
      have htri2 := hammingDistance_triangle SM.carrier
        (modelHom SM (wordOf c w)) 1 (SM.map 1)
      have honesymm : hammingDistance SM.carrier 1 (SM.map 1) ≤ ε := by
        rw [hammingDistance_comm]; exact hone
      have hlen : w.length ≤ L := by
        rw [hL]; exact le_foldr_max List.length allWords w hwall
      have hb : 3 * (w.length : ℝ) + 3 ≤ (B : ℝ) := by
        have hLle : (w.length : ℝ) ≤ (L : ℝ) := by exact_mod_cast hlen
        rw [hB]; push_cast; linarith
      have hcoef : (3 * (w.length : ℝ) + 1) * ε + ε ≤ (B : ℝ) * ε - ε := by
        have hstep : (3 * (w.length : ℝ) + 3) * ε ≤ (B : ℝ) * ε :=
          mul_le_mul_of_nonneg_right hb hεpos.le
        nlinarith [hεpos.le]
      have hhalf : (B : ℝ) * ε ≤ 1 / 2 := by
        rw [hBε, hm]; exact min_le_left _ _
      rw [toPermMicrostate_len]
      linarith
  · -- Backward: read a fixed-separation model off microstates, then amplify.
    intro h
    refine isSofic_of_isSoficWeak (δ := 1 / 2) (by norm_num) ?_
    intro F ε hε
    set wd : Carrier c → List (ℕ × Bool) := Function.surjInv (ev_surjective c)
      with hwd
    have hwdspec : ∀ g : Carrier c, ev c (wd g) = g := fun g =>
      Function.surjInv_eq (ev_surjective c) g
    set pairs : Finset (Carrier c × Carrier c) :=
      (F ×ˢ F).filter fun q => q.1 ≠ q.2 with hpairs
    set W : List (List (ℕ × Bool)) :=
      pairs.toList.map fun q => invWord (wd q.1) ++ wd q.2 with hW
    set mulWords : List (List (ℕ × Bool)) :=
      (F ×ˢ F).toList.map fun q => invWord (wd q.1 ++ wd q.2) ++ wd (q.1 * q.2)
      with hmul
    have hmultriv : ∀ u ∈ mulWords, WordProblem c u := by
      intro u hu
      rw [hmul, List.mem_map] at hu
      obtain ⟨q, _hq, rfl⟩ := hu
      rw [← ev_eq_one_iff, ev_append, ev_invWord, ev_append, hwdspec, hwdspec,
        hwdspec, inv_mul_cancel]
    obtain ⟨N, hN⟩ := exists_area_bound_list_perm c mulWords hmultriv
    obtain ⟨k, hk⟩ := exists_nat_gt ((N : ℝ) / ε)
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hNk : (N : ℝ) * (1 / ((k : ℝ) + 1)) ≤ ε := by
      have h1 : (N : ℝ) / ε < (k : ℝ) + 1 := by linarith
      have h2 : (N : ℝ) < ε * ((k : ℝ) + 1) := by
        have := (div_lt_iff₀ hε).1 h1
        linarith
      rw [mul_one_div]
      exact (div_le_iff₀ hkpos).2 (by linarith)
    rcases h W k with hvoid | ⟨M, hrel, hsep⟩
    · exfalso
      obtain ⟨w, hw, hwtriv⟩ := hvoid
      rw [hW, List.mem_map] at hw
      obtain ⟨q, hq, rfl⟩ := hw
      rw [Finset.mem_toList, hpairs, Finset.mem_filter] at hq
      rw [← ev_eq_one_iff, ev_append, ev_invWord, hwdspec, hwdspec,
        inv_mul_eq_one] at hwtriv
      exact hq.2 hwtriv
    refine ⟨{
      carrier := M.carrier
      nonempty := M.nonempty
      map := fun g => M.hom (wordOf c (wd g))
      multiplicative := ?_
      separated := ?_ }⟩
    · intro g hg h' hh'
      have hmemword :
          (invWord (wd g ++ wd h') ++ wd (g * h')) ∈ mulWords := by
        rw [hmul, List.mem_map]
        refine ⟨(g, h'), ?_, rfl⟩
        rw [Finset.mem_toList, Finset.mem_product]
        exact ⟨hg, hh'⟩
      have hval : M.len (invWord (wd g ++ wd h') ++ wd (g * h'))
          = hammingDistance M.carrier (M.hom (wordOf c (wd (g * h'))))
              (M.hom (wordOf c (wd g)) * M.hom (wordOf c (wd h'))) := by
        rw [PermMicrostate.len_def, wordOf_append, wordOf_invWord,
          wordOf_append, map_mul, map_inv, map_mul,
          ← hammingDistance_eq_displacement]
      have hbound := hN M (1 / ((k : ℝ) + 1)) (by positivity) hrel _ hmemword
      rw [hval] at hbound
      exact hbound.trans hNk
    · intro g hg h' hh' hne
      have hmemword : (invWord (wd h') ++ wd g) ∈ W := by
        rw [hW, List.mem_map]
        refine ⟨(h', g), ?_, rfl⟩
        rw [Finset.mem_toList, hpairs, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hh', hg⟩, Ne.symm hne⟩
      have hval : M.len (invWord (wd h') ++ wd g)
          = hammingDistance M.carrier (M.hom (wordOf c (wd g)))
              (M.hom (wordOf c (wd h'))) := by
        rw [PermMicrostate.len_def, wordOf_append, wordOf_invWord, map_mul,
          map_inv, ← hammingDistance_eq_displacement]
      have hbound := hsep _ hmemword
      rw [hval] at hbound
      exact hbound

/-! ## The closed form

The equivalence quantifies over codes, so it is routed through a named
proposition: the repository's advertised-endpoint audit refuses a leading
declaration binder. -/

/-- **The oracle-free `∀∃` normal form for soficity**, as a closed
proposition. -/
def SoficNormalForm : Prop :=
  ∀ c : PresentationCode, IsSofic (Carrier c) ↔ ∀ W k, Answers c W k

/-- **The normal form holds.**  No hypothesis, no construction datum. -/
theorem soficNormalForm : SoficNormalForm :=
  isSofic_iff_forall_answers

end SoficMicrostateNormalForm
end GroupApproximation

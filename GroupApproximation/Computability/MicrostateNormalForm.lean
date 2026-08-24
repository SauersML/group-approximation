import GroupApproximation.Computability.CodedMicrostate
import GroupApproximation.Sofic.OperatorMFLocalNormalization

/-!
# The oracle-free `∀∃` normal form for MF-ness of a presentation code

`OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one` already
characterises MF-ness locally, but in a shape that cannot be arithmetised: a
`NormModel` is a map out of the *group*, and its separation clause reads
`g ≠ h → …`, so both the data and the statement mention equality in a group
whose word problem is undecidable.

This file removes that.  A challenge is a finite list `W` of raw words together
with an accuracy index `k`.  It is *answered* when either

* some word of `W` is trivial in the coded group --- in which case the
  challenge asked for the impossible and is void; this disjunct is a search for
  a finite certificate, and it is sound because certificates are sound --- or
* a microstate displaces every listed relator by at most `1/(k+1)` and every
  word of `W` by at least `1/2`.

`isOperatorMF_iff_forall_answers` says MF-ness is exactly the assertion that
every challenge is answered.  Nothing in `Answers` mentions equality in the
coded group except through `WordProblem`, and nothing in `Passes` mentions the
coded group at all.

## Why this is the arithmetically useful shape

`WordProblem` is recursively enumerable
(`WordProblemRE.rePred_wordProblemPred`), so the first disjunct is an
existential over a `Primcodable` search space with a computable matrix.  The
second disjunct is an existential over microstates.  The remaining distance to
a `Π⁰₂` upper bound for MF recognition is therefore exactly the effectivisation
of that second existential: replacing complex unitaries by Gaussian-rational
matrices and the two norm inequalities by decidable rational tests.  That step
is **not** taken here, and no claim about the arithmetical hierarchy is made in
this file.

## The two directions

Forward, a microstate is read off a `NormModel`: its generators are the model's
values on the one-letter words, and the word induction `approxWord` bounds the
gap between evaluating a word in the microstate and evaluating it in the model
by a multiple of the model's accuracy, linear in the word's length.  Separation
survives with room to spare, which is why the threshold is `1/2` rather than
`1`.

Backward, a `NormModel` is read off a microstate by sending a group element to
the microstate's value on a chosen word for it.  Separation is immediate.
Multiplicativity is not: two words for the same element must land close
together, and that is exactly what `exists_area_bound_list` supplies, with the
accuracy index chosen after the area count.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace MFMicrostate

open PresentationCodes AdianRabinWordProblem RawWord

noncomputable section

/-! ## Challenges and answers -/

/-- The conditions a challenge asks a microstate for. -/
def Passes (c : PresentationCode) (W : List (List (ℕ × Bool))) (k : ℕ)
    (M : Microstate c) : Prop :=
  (∀ r ∈ c.2, M.len r ≤ 1 / ((k : ℝ) + 1)) ∧ (∀ w ∈ W, 1 / 2 ≤ M.len w)

/-- **One challenge, answered.**  Either the challenge is void because one of
its words is trivial in the coded group, or a microstate meets it. -/
def Answers (c : PresentationCode) (W : List (List (ℕ × Bool))) (k : ℕ) :
    Prop :=
  (∃ w ∈ W, WordProblem c w) ∨ ∃ M : Microstate c, Passes c W k M

/-! ## Listed relators die -/

/-- A word the code lists as a relator is trivial in the coded group. -/
theorem wordProblem_of_mem_relators {c : PresentationCode}
    {u : List (ℕ × Bool)} (hu : u ∈ c.2) : WordProblem c u :=
  (QuotientGroup.eq_one_iff (N := Subgroup.normalClosure (relatorSet c))
    (wordOf c u)).2
    (Subgroup.subset_normalClosure (wordOf_mem_relatorSet hu))

/-! ## A crude maximum over a list -/

/-- Every member's value is at most the folded maximum. -/
theorem le_foldr_max {α : Type*} (f : α → ℕ) :
    ∀ (l : List α) (a : α), a ∈ l → f a ≤ (l.map f).foldr max 0
  | [], _, ha => by simp at ha
  | b :: t, a, ha => by
      rcases List.mem_cons.1 ha with rfl | ha'
      · exact le_max_left _ _
      · exact (le_foldr_max f t a ha').trans (le_max_right _ _)

/-- A list is one of its own suffixes. -/
theorem self_mem_tails : ∀ l : List (ℕ × Bool), l ∈ l.tails
  | [] => by simp
  | a :: t => by rw [List.tails_cons]; exact List.mem_cons_self

/-! ## One-letter words -/

/-- A letter and its reduction name the same free-group element. -/
theorem wordOf_letter (c : PresentationCode) (i : ℕ) (s : Bool) :
    wordOf c [(i, s)]
      = wordOf c [(((letterOf c i : Fin (genCount c)) : ℕ), s)] := by
  simp only [wordOf_def, List.map_cons, List.map_nil, letterOf_val_letterOf]

/-- A letter and its reduction name the same group element. -/
theorem ev_letter (c : PresentationCode) (i : ℕ) (s : Bool) :
    ev c [(i, s)] = ev c [(((letterOf c i : Fin (genCount c)) : ℕ), s)] := by
  rw [ev, ev, wordOf_letter]

/-- A negative one-letter word names the inverse of the positive one. -/
theorem ev_letter_neg (c : PresentationCode) (i : ℕ) :
    ev c [(i, false)] = (ev c [(i, true)])⁻¹ := by
  rw [ev, ev, wordOf_neg, wordOf_pos, map_inv]

/-! ## Reading a microstate off a norm model -/

section Forward

variable {c : PresentationCode} {F : Finset (Carrier c)} {ε : ℝ}

/-- A norm model's value, as an element of the unitary group. -/
def umap (NM : NormModel (Carrier c) F 1 ε) (g : Carrier c) :
    Matrix.unitaryGroup NM.carrier ℂ :=
  ⟨NM.map g, NM.isUnitary g⟩

@[simp] theorem umap_coe (NM : NormModel (Carrier c) F 1 ε) (g : Carrier c) :
    ((umap NM g : Matrix.unitaryGroup NM.carrier ℂ) :
      Matrix NM.carrier NM.carrier ℂ) = NM.map g := rfl

/-- The free-group homomorphism the model's one-letter values generate, stated
at the model's own carrier so that every estimate below lives in one type. -/
def modelHom (NM : NormModel (Carrier c) F 1 ε) :
    FreeGroup (Fin (genCount c)) →* Matrix.unitaryGroup NM.carrier ℂ :=
  FreeGroup.lift fun j => umap NM (ev c [((j : ℕ), true)])

@[simp] theorem modelHom_of (NM : NormModel (Carrier c) F 1 ε)
    (j : Fin (genCount c)) :
    modelHom NM (FreeGroup.of j) = umap NM (ev c [((j : ℕ), true)]) := by
  simp [modelHom]

/-- Multiplicativity, in displacement form. -/
theorem umap_mul_le (NM : NormModel (Carrier c) F 1 ε) {g h : Carrier c}
    (hg : g ∈ F) (hh : h ∈ F) :
    opLength NM.carrier ((umap NM g * umap NM h)⁻¹ * umap NM (g * h)) ≤ ε := by
  rw [opLength_inv_mul]
  simpa using NM.multiplicative g hg h hh

/-- The value at the identity is small. -/
theorem umap_one_le (NM : NormModel (Carrier c) F 1 ε)
    (h1 : (1 : Carrier c) ∈ F) :
    opLength NM.carrier (umap NM 1) ≤ ε := by
  have h := umap_mul_le NM h1 h1
  rw [mul_one] at h
  have hrw : (umap NM 1 * umap NM 1)⁻¹ * umap NM 1 = (umap NM 1)⁻¹ := by group
  rw [hrw, opLength_inv] at h
  exact h

/-- The value at an inverse is close to the inverse of the value. -/
theorem umap_inv_le (NM : NormModel (Carrier c) F 1 ε)
    (h1 : (1 : Carrier c) ∈ F) {g : Carrier c} (hg : g ∈ F) (hg' : g⁻¹ ∈ F) :
    opLength NM.carrier ((umap NM g⁻¹)⁻¹ * (umap NM g)⁻¹) ≤ 2 * ε := by
  have h := umap_mul_le NM hg hg'
  rw [mul_inv_cancel] at h
  have hsplit : (umap NM g * umap NM g⁻¹)⁻¹
      = ((umap NM g * umap NM g⁻¹)⁻¹ * umap NM 1) * (umap NM 1)⁻¹ := by group
  have hone : opLength NM.carrier (umap NM 1)⁻¹ ≤ ε := by
    rw [opLength_inv]; exact umap_one_le NM h1
  have hbound : opLength NM.carrier (umap NM g * umap NM g⁻¹)⁻¹ ≤ ε + ε := by
    rw [hsplit]
    exact (opLength_mul_le _ _ _).trans (add_le_add h hone)
  have hEq : (umap NM g⁻¹)⁻¹ * (umap NM g)⁻¹
      = (umap NM g * umap NM g⁻¹)⁻¹ := by rw [mul_inv_rev]
  rw [hEq]
  linarith

/-- The microstate a norm model determines. -/
def toMicrostate (NM : NormModel (Carrier c) F 1 ε) : Microstate c where
  model := NM.carrier
  card_pos := NM.nonempty
  gen := fun j => umap NM (ev c [((j : ℕ), true)])

theorem toMicrostate_len (NM : NormModel (Carrier c) F 1 ε)
    (w : List (ℕ × Bool)) :
    (toMicrostate NM).len w
      = opLength NM.carrier (modelHom NM (wordOf c w)) := rfl

/-- The microstate's value on a one-letter word is within `2ε` of the
model's. -/
theorem letter_gap (NM : NormModel (Carrier c) F 1 ε) (hε : 0 ≤ ε)
    (h1 : (1 : Carrier c) ∈ F)
    (hgen : ∀ (j : Fin (genCount c)) (s : Bool), ev c [((j : ℕ), s)] ∈ F)
    (p : ℕ × Bool) :
    opLength NM.carrier
        ((umap NM (ev c [p]))⁻¹ * modelHom NM (wordOf c [p]))
      ≤ 2 * ε := by
  obtain ⟨i, s⟩ := p
  cases s with
  | true =>
      rw [wordOf_pos, modelHom_of, ← ev_letter c i true, inv_mul_cancel,
        opLength_one]
      linarith
  | false =>
      have hpos : ev c [(((letterOf c i : Fin (genCount c)) : ℕ), true)]
          = ev c [(i, true)] := (ev_letter c i true).symm
      rw [wordOf_neg, map_inv, modelHom_of, hpos, ev_letter_neg]
      have hg : ev c [(i, true)] ∈ F := by
        rw [ev_letter c i true]; exact hgen (letterOf c i) true
      have hg' : (ev c [(i, true)])⁻¹ ∈ F := by
        rw [← ev_letter_neg, ev_letter c i false]; exact hgen (letterOf c i) false
      exact umap_inv_le NM h1 hg hg'

/-- **The word induction.**  Evaluating a word in the microstate and evaluating
it in the model differ by at most a multiple of the accuracy, linear in the
word's length. -/
theorem approxWord (NM : NormModel (Carrier c) F 1 ε) (hε : 0 ≤ ε)
    (h1 : (1 : Carrier c) ∈ F)
    (hgen : ∀ (j : Fin (genCount c)) (s : Bool), ev c [((j : ℕ), s)] ∈ F) :
    ∀ (u : List (ℕ × Bool)), (∀ t ∈ u.tails, ev c t ∈ F) →
      opLength NM.carrier
          ((umap NM (ev c u))⁻¹ * modelHom NM (wordOf c u))
        ≤ (3 * (u.length : ℝ) + 1) * ε
  | [], _ => by
      rw [ev_nil, wordOf_nil, map_one, mul_one, opLength_inv]
      have h := umap_one_le NM h1
      simp only [List.length_nil, Nat.cast_zero, mul_zero, zero_add, one_mul]
      exact h
  | p :: t, hsuf => by
      have htail : ∀ s ∈ t.tails, ev c s ∈ F := by
        intro s hs
        exact hsuf s (by rw [List.tails_cons]; exact List.mem_cons_of_mem _ hs)
      have ih := approxWord NM hε h1 hgen t htail
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
      set a := umap NM (ev c [p]) with ha
      set b := umap NM (ev c t) with hb
      set A := modelHom NM (wordOf c [p]) with hA
      set B := modelHom NM (wordOf c t) with hB
      have hhom : modelHom NM (wordOf c (p :: t)) = A * B := by
        rw [hwordcons, map_mul]
      have hsplit :
          (umap NM (ev c (p :: t)))⁻¹ * modelHom NM (wordOf c (p :: t))
            = ((umap NM (ev c (p :: t)))⁻¹ * (a * b))
                * ((b⁻¹ * (a⁻¹ * A) * b) * (b⁻¹ * B)) := by
        rw [hhom]; group
      have hfirst :
          opLength NM.carrier ((umap NM (ev c (p :: t)))⁻¹ * (a * b)) ≤ ε := by
        have h := umap_mul_le NM hmemp hmemt
        rw [← hevcons, ← ha, ← hb] at h
        have hinv : (umap NM (ev c (p :: t)))⁻¹ * (a * b)
            = ((a * b)⁻¹ * umap NM (ev c (p :: t)))⁻¹ := by group
        rw [hinv, opLength_inv]
        exact h
      have hconj : opLength NM.carrier (b⁻¹ * (a⁻¹ * A) * b)
          = opLength NM.carrier (a⁻¹ * A) := by
        have hc := opLength_conj NM.carrier b⁻¹ (a⁻¹ * A)
        rwa [inv_inv] at hc
      have hletter : opLength NM.carrier (a⁻¹ * A) ≤ 2 * ε := by
        rw [ha, hA]; exact letter_gap NM hε h1 hgen p
      have hbound :
          opLength NM.carrier
              ((umap NM (ev c (p :: t)))⁻¹ * modelHom NM (wordOf c (p :: t)))
            ≤ ε + (2 * ε + (3 * (t.length : ℝ) + 1) * ε) := by
        rw [hsplit]
        refine (opLength_mul_le _ _ _).trans (add_le_add hfirst ?_)
        refine (opLength_mul_le _ _ _).trans (add_le_add ?_ ih)
        rw [hconj]; exact hletter
      refine hbound.trans (le_of_eq ?_)
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

end Forward

/-! ## The equivalence -/

/-- **MF-ness of a coded group is exactly the assertion that every challenge is
answered.**

The right-hand side never mentions equality in the coded group except through
`WordProblem`, and the microstate disjunct mentions the coded group not at
all. -/
theorem isOperatorMF_iff_forall_answers (c : PresentationCode) :
    IsOperatorMF (Carrier c) ↔ ∀ W k, Answers c W k := by
  classical
  constructor
  · -- Forward: read a microstate off a normalized local model.
    intro hMF W k
    by_cases hvoid : ∃ w ∈ W, WordProblem c w
    · exact Or.inl hvoid
    refine Or.inr ?_
    have hNA : IsNormApproximable (Carrier c) 1 :=
      OperatorMFLocalNormalization.isNormApproximable_one hMF
    set allWords : List (List (ℕ × Bool)) := W ++ c.2 with hall
    set L : ℕ := (allWords.map List.length).foldr max 0 with hL
    set B : ℕ := 3 * L + 2 with hB
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
    have hmemF : ∀ u ∈ ([] : List (ℕ × Bool)) :: (sufs ++ gens), ev c u ∈ F := by
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
    obtain ⟨NM⟩ := hNA F ε hεpos
    refine ⟨toMicrostate NM, ?_, ?_⟩
    · intro r hr
      have hrall : r ∈ allWords := by
        rw [hall]; exact List.mem_append_right _ hr
      have htriv : ev c r = 1 := wordProblem_of_mem_relators hr
      have hgap := approxWord NM hεpos.le h1F hgenF r (hsufF r hrall)
      rw [htriv] at hgap
      have hstep := Microstate.opLength_le_gap
        (modelHom NM (wordOf c r)) (umap NM 1)
      rw [Microstate.opLength_gap_symm] at hstep
      have hone := umap_one_le NM h1F
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
      rw [toMicrostate_len]
      linarith
    · intro w hw
      have hwall : w ∈ allWords := by
        rw [hall]; exact List.mem_append_left _ hw
      have hne : ev c w ≠ 1 := fun hcon => hvoid ⟨w, hw, hcon⟩
      have hwF : ev c w ∈ F := hsufF w hwall w (self_mem_tails w)
      have hgap := approxWord NM hεpos.le h1F hgenF w (hsufF w hwall)
      have hsep : (1 : ℝ)
          ≤ opLength NM.carrier ((umap NM 1)⁻¹ * umap NM (ev c w)) := by
        rw [opLength_inv_mul]
        simpa using NM.separated (ev c w) hwF 1 h1F hne
      have hone := umap_one_le NM h1F
      have hsplit := Microstate.opLength_le_gap
        ((umap NM 1)⁻¹ * umap NM (ev c w)) (umap NM (ev c w))
      have hgapsmall : opLength NM.carrier
          (((umap NM 1)⁻¹ * umap NM (ev c w))⁻¹ * umap NM (ev c w))
            ≤ ε := by
        have hEq : ((umap NM 1)⁻¹ * umap NM (ev c w))⁻¹ * umap NM (ev c w)
            = (umap NM (ev c w))⁻¹ * umap NM 1 * ((umap NM (ev c w))⁻¹)⁻¹ := by
          group
        rw [hEq, opLength_conj]
        exact hone
      have hbig : (1 : ℝ) - ε ≤ opLength NM.carrier (umap NM (ev c w)) := by
        linarith
      have hstep := Microstate.opLength_le_gap
        (umap NM (ev c w)) (modelHom NM (wordOf c w))
      have hlen : w.length ≤ L := by
        rw [hL]; exact le_foldr_max List.length allWords w hwall
      have hb : 3 * (w.length : ℝ) + 2 ≤ (B : ℝ) := by
        have hLle : (w.length : ℝ) ≤ (L : ℝ) := by exact_mod_cast hlen
        rw [hB]; push_cast; linarith
      have hcoef : ε + (3 * (w.length : ℝ) + 1) * ε ≤ (B : ℝ) * ε := by
        calc ε + (3 * (w.length : ℝ) + 1) * ε
            = (3 * (w.length : ℝ) + 2) * ε := by ring
          _ ≤ (B : ℝ) * ε := mul_le_mul_of_nonneg_right hb hεpos.le
      have hhalf : (B : ℝ) * ε ≤ 1 / 2 := by
        rw [hBε, hm]; exact min_le_left _ _
      rw [toMicrostate_len]
      linarith
  · -- Backward: read a norm model off microstates.
    intro h
    refine (show IsWeakMF (Carrier c) from ⟨1 / 2, by norm_num, ?_⟩).isOperatorMF
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
    obtain ⟨N, hN⟩ := exists_area_bound_list c mulWords hmultriv
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
      carrier := M.model
      nonempty := M.card_pos
      map := fun g => ((M.hom (wordOf c (wd g)) :
        Matrix.unitaryGroup M.model ℂ) : Matrix M.model M.model ℂ)
      isUnitary := fun g => (M.hom (wordOf c (wd g))).2
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
          = opLength M.model
            ((M.hom (wordOf c (wd g)) * M.hom (wordOf c (wd h')))⁻¹
              * M.hom (wordOf c (wd (g * h')))) := by
        rw [Microstate.len_def, wordOf_append, wordOf_invWord, wordOf_append,
          map_mul, map_inv, map_mul]
      have hbound := hN M (1 / ((k : ℝ) + 1)) (by positivity) hrel _ hmemword
      rw [hval] at hbound
      have hfinal := hbound.trans hNk
      rw [opLength_inv_mul] at hfinal
      simpa using hfinal
    · intro g hg h' hh' hne
      have hmemword : (invWord (wd h') ++ wd g) ∈ W := by
        rw [hW, List.mem_map]
        refine ⟨(h', g), ?_, rfl⟩
        rw [Finset.mem_toList, hpairs, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hh', hg⟩, Ne.symm hne⟩
      have hval : M.len (invWord (wd h') ++ wd g)
          = opLength M.model
            ((M.hom (wordOf c (wd h')))⁻¹ * M.hom (wordOf c (wd g))) := by
        rw [Microstate.len_def, wordOf_append, wordOf_invWord, map_mul, map_inv]
      have hbound := hsep _ hmemword
      rw [hval, opLength_inv_mul] at hbound
      simpa using hbound

/-! ## The closed form

The equivalence quantifies over codes, so it is routed through a named
proposition: the repository's advertised-endpoint audit refuses a leading
declaration binder, and a universally quantified sentence belongs inside the
`Prop` rather than in the theorem's telescope. -/

/-- **The oracle-free `∀∃` normal form for MF-ness**, as a closed
proposition. -/
def MicrostateNormalForm : Prop :=
  ∀ c : PresentationCode,
    IsOperatorMF (Carrier c) ↔ ∀ W k, Answers c W k

/-- **The normal form holds.**  No hypothesis, no construction datum. -/
theorem microstateNormalForm : MicrostateNormalForm :=
  isOperatorMF_iff_forall_answers

end

end MFMicrostate
end GroupApproximation

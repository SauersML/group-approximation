import GroupApproximation.GroupTheory.HNNBrittonSpelling
import GroupApproximation.Algebra.HNNTorsionFree
import Mathlib.Tactic.Group

/-!
# Cyclic reduction in HNN extensions, and the torsion theorem

`GroupApproximation/Algebra/HNNTorsionFree.lean` proves the two halves of
the HNN torsion theorem that are pure Britton combinatorics — a cyclically
reduced word with a stable letter has infinite order, and torsion-freeness
descends along that dichotomy — but leaves the third half, *existence of a
cyclic reduction*, as the named interface
`HNNTorsionFree.ExistsCyclicConjugate` (declared at that file's line 164
and carried as a hypothesis at lines 177, 248 and 256), whose own
docstring calls it "the single unformalized input of the torsion theorem
below".  Mathlib has no HNN cyclic reduction to import: its
`GroupTheory/FreeGroup/CyclicallyReduced.lean` is about free groups only.

This module discharges that interface outright.  Nothing here is
conditional, so the corollaries below are unconditional:

* `absorbLast` and its lemmas — multiplying the last syllable of a
  spelling on the right by a group element.  This is how the head of a
  reduced word is conjugated away: `g · w = g · (w · g) · g⁻¹`, and
  `w · g` is again spelled by a pinch-free list of the same length,
  because no pinch condition inspects the group part of the last
  syllable.
* `spell_rotate`, `spell_pinch` — the two algebraic identities of the
  reduction step: moving the final syllable to the front is conjugation
  by that syllable, and a leading pinch is absorbed into a new head by
  the defining relation.
* `cyclic_step` — the single reduction step.  A head-absorbed pinch-free
  word either satisfies the seam condition, and so is a
  `HNNTorsionFree.CyclicWord`, or its last syllable pinches against its
  first, and the rotation drops the syllable count by exactly two.
* `cyclicReduce` — the induction on syllable count.
* `existsCyclicConjugate` — **`HNNTorsionFree.ExistsCyclicConjugate` is a
  theorem**, for every HNN extension.  This is the declaration to rewire
  `HNNTorsionFree` against.
* `isPowerTorsionFree_hnn` — **the HNN torsion theorem**: an HNN extension
  of a torsion-free group over any associated pair is torsion-free.
* `isPowerTorsionFree_integerSourceGroup` — the explicit integer
  compression source of `ConcreteCompressionSource` is torsion-free.  Its
  module docstring records this as the only step separating
  `integerSource` from a fully torsion-free certified source.

Existence of a pinch-free spelling comes from `HNNBrittonSpelling` (which
reads it off Mathlib's normal form); the no-collapse half is Mathlib's
Britton lemma through `HNNBrittonPinch`.
-/

namespace GroupApproximation
namespace HNNBritton

universe u

variable {G : Type u} [Group G] {A B : Subgroup G}

/-! ## Absorbing a group element into the last syllable -/

/-- Multiply the last syllable of a syllable list on the right by `g`.
On the empty list this does nothing. -/
def absorbLast : List (ℤˣ × G) → G → List (ℤˣ × G)
  | [], _ => []
  | [(u, x)], g => [(u, x * g)]
  | p :: q :: L, g => p :: absorbLast (q :: L) g

@[simp] theorem absorbLast_nil (g : G) :
    absorbLast ([] : List (ℤˣ × G)) g = [] := by
  simp [absorbLast]

@[simp] theorem absorbLast_singleton (u : ℤˣ) (x g : G) :
    absorbLast [(u, x)] g = [(u, x * g)] := by
  simp [absorbLast]

theorem absorbLast_cons_cons (p q : ℤˣ × G) (L : List (ℤˣ × G)) (g : G) :
    absorbLast (p :: q :: L) g = p :: absorbLast (q :: L) g := by
  simp [absorbLast]

theorem absorbLast_ne_nil {l : List (ℤˣ × G)} (hl : l ≠ []) (g : G) :
    absorbLast l g ≠ [] := by
  rcases l with _ | ⟨⟨u, x⟩, L⟩
  · exact absurd rfl hl
  · rcases L with _ | ⟨q, M⟩
    · simp
    · rw [absorbLast_cons_cons]
      simp

theorem absorbLast_length :
    ∀ (l : List (ℤˣ × G)) (g : G), (absorbLast l g).length = l.length := by
  intro l
  induction l with
  | nil => intro g; simp
  | cons p L ih =>
      intro g
      cases L with
      | nil =>
          obtain ⟨u, x⟩ := p
          simp
      | cons q M =>
          rw [absorbLast_cons_cons]
          simp [ih g]

/-- Absorption does not change the sign of the leading syllable. -/
theorem absorbLast_head?_map_fst (l : List (ℤˣ × G)) (g : G) :
    (absorbLast l g).head?.map Prod.fst = l.head?.map Prod.fst := by
  cases l with
  | nil => simp
  | cons p L =>
      cases L with
      | nil =>
          obtain ⟨u, x⟩ := p
          simp
      | cons q M =>
          rw [absorbLast_cons_cons]
          simp

/-- Absorbing on the right multiplies the spelled element on the right. -/
theorem spell_absorbLast (φ : A ≃* B) :
    ∀ (l : List (ℤˣ × G)) (g : G), l ≠ [] →
      spell φ (absorbLast l g) = spell φ l * HNNExtension.of g := by
  intro l
  induction l with
  | nil => intro g h; exact absurd rfl h
  | cons p L ih =>
      intro g _
      cases L with
      | nil =>
          obtain ⟨u, x⟩ := p
          simp only [absorbLast_singleton, spell_cons, spell_nil, map_mul]
          group
      | cons q M =>
          rw [absorbLast_cons_cons]
          simp only [spell_cons]
          rw [ih g (by simp)]
          simp [mul_assoc]

/-- Absorption preserves pinch-freeness: it only touches the group part of
the final syllable, which no pinch condition inspects. -/
theorem noPinch_absorbLast :
    ∀ (l : List (ℤˣ × G)) (g : G), NoPinch A B l →
      NoPinch A B (absorbLast l g) := by
  intro l
  induction l with
  | nil =>
      intro g _
      rw [absorbLast_nil]
      exact noPinch_nil
  | cons p L ih =>
      intro g h
      cases L with
      | nil =>
          obtain ⟨u, x⟩ := p
          rw [absorbLast_singleton]
          exact noPinch_singleton _
      | cons q M =>
          rw [absorbLast_cons_cons]
          refine noPinch_cons ?_ (ih g h.tail)
          intro y hy hmem
          rw [Option.mem_def] at hy
          have hfst := absorbLast_head?_map_fst (q :: M) g
          rw [hy] at hfst
          simp at hfst
          have hpq : p.1 = q.1 := h.seam q (by simp) hmem
          exact hpq.trans hfst.symm

/-! ## The two identities of the reduction step -/

/-- **Rotation.**  Moving the last syllable of a spelling to the front is
conjugation by that syllable. -/
theorem spell_rotate (φ : A ≃* B) (L : List (ℤˣ × G)) (b : ℤˣ × G) :
    spell φ (L ++ [b]) =
      (spell φ [b])⁻¹ * spell φ (b :: L) * spell φ [b] := by
  have hb : spell φ (b :: L) = spell φ [b] * spell φ L := by
    simp only [spell_cons, spell_nil, mul_one, mul_assoc]
  rw [spell_append, hb]
  group

/-- **Leading pinch absorption.**  A leading syllable that lies in the
associated subgroup of its own sign and is followed by the opposite sign
is absorbed, together with that next syllable, into a new head. -/
theorem spell_pinch (φ : A ≃* B) {b p : ℤˣ × G} (P : List (ℤˣ × G))
    (hmem : b.2 ∈ HNNExtension.toSubgroup A B b.1) (hne : b.1 ≠ p.1) :
    ∃ g' : G, spell φ (b :: p :: P) = wordProd φ g' P := by
  obtain ⟨ub, xb⟩ := b
  obtain ⟨up, xp⟩ := p
  rcases Int.units_eq_one_or ub with rfl | rfl <;>
    rcases Int.units_eq_one_or up with rfl | rfl
  · exact absurd rfl hne
  · have hxb : xb ∈ A := hmem
    refine ⟨((φ ⟨xb, hxb⟩ : B) : G) * xp, ?_⟩
    have hconj := t_conj_of_mem φ hxb
    simp only [wordProd, spell_cons_one, spell_cons_neg_one, map_mul]
    rw [← hconj]
    group
  · have hxb : xb ∈ B := hmem
    refine ⟨((φ.symm ⟨xb, hxb⟩ : A) : G) * xp, ?_⟩
    have hconj := t_inv_conj_of_mem φ hxb
    simp only [wordProd, spell_cons_one, spell_cons_neg_one, map_mul]
    rw [← hconj]
    group
  · exact absurd rfl hne

/-! ## The single cyclic-reduction step -/

/-- **One cyclic-reduction step.**  A nonempty pinch-free syllable list
either already satisfies the seam condition — so the element it spells is
a cyclically reduced word — or its last syllable pinches against its
first, and conjugating by that last syllable produces a pinch-free
spelling with two fewer syllables. -/
theorem cyclic_step (φ : A ≃* B) {M : List (ℤˣ × G)} (hMne : M ≠ [])
    (hM : NoPinch A B M) :
    (∃ c : HNNTorsionFree.CyclicWord G A B, spell φ M = c.elem φ) ∨
      (∃ (w : HNNExtension G A B φ) (g' : G) (P : List (ℤˣ × G)),
        NoPinch A B P ∧ P.length + 2 = M.length ∧
          spell φ M = w * wordProd φ g' P * w⁻¹) := by
  rcases List.eq_nil_or_concat' M with rfl | ⟨L', b, hMeq⟩
  · exact absurd rfl hMne
  · have hlast : M.getLast? = some b := by
      rw [hMeq]
      exact List.getLast?_concat
    rcases L' with _ | ⟨p, P⟩
    · -- a single syllable: the seam condition is trivial
      have hsing : M = [b] := by simpa using hMeq
      refine Or.inl ⟨⟨M, hMne, hM, ?_⟩, rfl⟩
      have hhead : M.head? = some b := by simp [hsing]
      intro x hx y hy _
      rw [Option.mem_def, hlast, Option.some.injEq] at hx
      rw [Option.mem_def, hhead, Option.some.injEq] at hy
      subst hx
      subst hy
      rfl
    · -- at least two syllables
      have hMcons : M = p :: (P ++ [b]) := hMeq
      have hhead : M.head? = some p := by simp [hMcons]
      by_cases hpinch :
          b.2 ∈ HNNExtension.toSubgroup A B b.1 ∧ b.1 ≠ p.1
      · -- the last syllable pinches against the first: rotate and absorb
        obtain ⟨hmemA, hneq⟩ := hpinch
        have hPb : NoPinch A B (P ++ [b]) := by
          rw [hMcons] at hM
          exact hM.tail
        have hP : NoPinch A B P := hPb.infix ⟨[], [b], by simp⟩
        have hPlen : P.length + 2 = M.length := by
          rw [hMcons]
          simp only [List.length_cons, List.length_append, List.length_nil]
        have hrot : spell φ M =
            (spell φ [b])⁻¹ * spell φ (b :: (p :: P)) * spell φ [b] := by
          rw [hMeq]
          exact spell_rotate φ (p :: P) b
        obtain ⟨g', hg'⟩ := spell_pinch φ P hmemA hneq
        refine Or.inr ⟨(spell φ [b])⁻¹, g', P, hP, hPlen, ?_⟩
        rw [hrot, hg']
        group
      · -- the seam condition holds
        refine Or.inl ⟨⟨M, hMne, hM, ?_⟩, rfl⟩
        intro x hx y hy hmem
        rw [Option.mem_def, hlast, Option.some.injEq] at hx
        rw [Option.mem_def, hhead, Option.some.injEq] at hy
        subst hx
        subst hy
        by_contra hc
        exact hpinch ⟨hmem, hc⟩

/-! ## Cyclic reduction -/

/-- **Cyclic reduction.**  Every element spelled by a head and a
pinch-free syllable list is conjugate into the base copy or conjugate to a
cyclically reduced word. -/
theorem cyclicReduce (φ : A ≃* B) :
    ∀ (n : ℕ) (g : G) (l : List (ℤˣ × G)), l.length ≤ n → NoPinch A B l →
      (∃ (h : HNNExtension G A B φ) (b : G),
          wordProd φ g l = h * HNNExtension.of b * h⁻¹) ∨
        (∃ (h : HNNExtension G A B φ)
            (c : HNNTorsionFree.CyclicWord G A B),
          wordProd φ g l = h * c.elem φ * h⁻¹) := by
  intro n
  induction n with
  | zero =>
      intro g l hlen _
      cases l with
      | nil => exact Or.inl ⟨1, g, by simp⟩
      | cons p L => simp at hlen
  | succ n ih =>
      intro g l hlen hl
      rcases eq_or_ne l [] with rfl | hne
      · exact Or.inl ⟨1, g, by simp⟩
      · have hMne : absorbLast l g ≠ [] := absorbLast_ne_nil hne g
        have hMchain : NoPinch A B (absorbLast l g) :=
          noPinch_absorbLast l g hl
        have hMlen : (absorbLast l g).length = l.length :=
          absorbLast_length l g
        have hconj : wordProd φ g l =
            HNNExtension.of g * spell φ (absorbLast l g) *
              (HNNExtension.of g)⁻¹ := by
          rw [spell_absorbLast φ l g hne]
          simp only [wordProd]
          group
        rcases cyclic_step φ hMne hMchain with
          ⟨c, hc⟩ | ⟨w, g', P, hP, hPlen, hw⟩
        · refine Or.inr ⟨HNNExtension.of g, c, ?_⟩
          rw [hconj, hc]
        · have hlenP : P.length ≤ n := by omega
          have hstep : wordProd φ g l =
              (HNNExtension.of g * w) * wordProd φ g' P *
                (HNNExtension.of g * w)⁻¹ := by
            rw [hconj, hw]
            group
          rcases ih g' P hlenP hP with ⟨h, b', hb'⟩ | ⟨h, c, hc⟩
          · refine Or.inl ⟨HNNExtension.of g * w * h, b', ?_⟩
            rw [hstep, hb']
            group
          · refine Or.inr ⟨HNNExtension.of g * w * h, c, ?_⟩
            rw [hstep, hc]
            group

/-- **Cyclic-reduction existence is a theorem.**  This discharges the
named interface `HNNTorsionFree.ExistsCyclicConjugate`, which was the last
unformalized input of the HNN torsion theorem. -/
theorem existsCyclicConjugate (φ : A ≃* B) :
    HNNTorsionFree.ExistsCyclicConjugate φ := by
  intro x
  obtain ⟨g, l, hl, rfl⟩ := exists_hasSpelling φ x
  exact cyclicReduce φ l.length g l le_rfl hl

/-! ## The torsion theorem, unconditionally -/

/-- **The HNN torsion theorem.**  An HNN extension of a torsion-free group
is torsion-free, over any associated pair. -/
theorem isPowerTorsionFree_hnn (φ : A ≃* B) (hG : IsPowerTorsionFree G) :
    IsPowerTorsionFree (HNNExtension G A B φ) :=
  HNNTorsionFree.isPowerTorsionFree_of_existsCyclicConjugate φ
    (existsCyclicConjugate φ) hG

/-- The affine compression skeleton over an injective endomorphism has a
torsion-free total group as soon as its base is torsion-free. -/
theorem isPowerTorsionFree_sourceGroup {Γ : Type} [Group Γ] (α : Γ →* Γ)
    (hα : Function.Injective α)
    (hbase : IsPowerTorsionFree (ConcreteCompressionSource.Base Γ)) :
    IsPowerTorsionFree (ConcreteCompressionSource.SourceGroup α hα) :=
  HNNTorsionFree.isPowerTorsionFree_sourceGroup_of_existsCyclicConjugate α hα
    (existsCyclicConjugate _) hbase

/-- **The explicit integer compression source is torsion-free.**  This was
recorded in `ConcreteCompressionSource` as the only step separating
`integerSource` from a fully torsion-free certified source. -/
theorem isPowerTorsionFree_integerSourceGroup :
    IsPowerTorsionFree
      (ConcreteCompressionSource.SourceGroup
        ConcreteCompressionSource.doubling
        ConcreteCompressionSource.doubling_injective) :=
  HNNTorsionFree.isPowerTorsionFree_integerSourceGroup_of_existsCyclicConjugate
    (existsCyclicConjugate _)

end HNNBritton
end GroupApproximation

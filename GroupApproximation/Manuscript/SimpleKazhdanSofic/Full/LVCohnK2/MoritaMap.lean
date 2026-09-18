import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.MoritaUnits

/-!
# The block map `St_{I×J}(R) → St_I(M_J(R))` (lane LVCohnK2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  For the Morita
invariance of stable `K₂` (Ara–Brustenga–Cortiñas 2009, ultramatricial stages of the Cohn algebra)
we construct, when every three indices of `I` are avoided by a fourth, a homomorphism
`blockMap hI : St_{I×J}(R) →* St_I(M_J(R))` with

* `x_{(i,k),(j,l)}(a) ↦ x_{ij}(e_{kl} a)` for `i ≠ j` (`blockMap_x_ne`);
* `x_{(i,k),(i,l)}(a) ↦ ⁅x_{ip}(e_{kl} a), x_{pi}(e_{ll})⁆` with an auxiliary `p ≠ i`
  (`blockMap_x_eq`).

The Steinberg relations are checked in `blockGen_add`, `blockGen_commute` and
`blockGen_adjacent`, using the commutator calculus of `MoritaSteinberg` and `MoritaUnits`.
-/

namespace GroupApproximation.Full.LVCohnK2

open SteinbergGroup
open scoped commutatorElement

variable {I : Type*} [Fintype I] [DecidableEq I] {J : Type*} [Fintype J] [DecidableEq J]
  {R : Type*} [Ring R]

/-- A pair `(i, k) ≠ (i, l)` has `k ≠ l`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem pair_snd_ne {i : I} {k l : J} (h : (i, k) ≠ (i, l)) : k ≠ l :=
  fun e => h (congrArg (Prod.mk i) e)

/-- An auxiliary index different from `i`.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
noncomputable def auxIndex (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c) (i : I) : I :=
  (hI i i i).choose

/-- `i ≠ auxIndex hI i`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem auxIndex_ne (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c) (i : I) :
    i ≠ auxIndex hI i :=
  ((hI i i i).choose_spec.1).symm

/-- The image of the generator `x_{αβ}(a)` of `St_{I×J}(R)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
noncomputable def blockGen (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c)
    (α β : I × J) (h : α ≠ β) (a : R) : SteinbergGroup I (Matrix J J R) :=
  if h1 : α.1 = β.1 then diagElem α.1 (auxIndex hI α.1) (auxIndex_ne hI α.1) α.2 β.2 a
  else x α.1 β.1 h1 (Matrix.single α.2 β.2 a)

/-- `blockGen` on a generator with different first coordinates.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem blockGen_ne (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c) (i j : I) (k l : J)
    (h : (i, k) ≠ (j, l)) (hij : i ≠ j) (a : R) :
    blockGen hI (i, k) (j, l) h a = x i j hij (Matrix.single k l a) :=
  dif_neg hij

/-- `blockGen` on a generator with equal first coordinates.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem blockGen_eq (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c) (i : I) (k l : J)
    (h : (i, k) ≠ (i, l)) (a : R) :
    blockGen hI (i, k) (i, l) h a = diagElem i (auxIndex hI i) (auxIndex_ne hI i) k l a :=
  dif_pos (rfl : i = i)

/-- Relation R1 for `blockGen`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem blockGen_add (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c) (α β : I × J)
    (h : α ≠ β) (a b : R) :
    blockGen hI α β h a * blockGen hI α β h b = blockGen hI α β h (a + b) := by
  obtain ⟨i, k⟩ := α
  obtain ⟨j, l⟩ := β
  by_cases hij : i = j
  · subst hij
    obtain ⟨q, hqi, hqp, -⟩ := hI i (auxIndex hI i) i
    rw [blockGen_eq hI i k l h a, blockGen_eq hI i k l h b, blockGen_eq hI i k l h (a + b)]
    exact (diagElem_add i (auxIndex hI i) q (auxIndex_ne hI i) hqi hqp k l (pair_snd_ne h).symm
      a b).symm
  · rw [blockGen_ne hI i j k l h hij a, blockGen_ne hI i j k l h hij b,
      blockGen_ne hI i j k l h hij (a + b), x_mul, Matrix.single_add k l a b]

/-- A diagonal block generator commutes with an off-diagonal one under the hypotheses of the
commutation relation.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commute_diag_left (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c) (i : I)
    (k l : J) (hlk : l ≠ k) (a : R) (i' j' : I) (hij' : i' ≠ j') (k' l' : J)
    (hβγ : (i, l) ≠ (i', k')) (hδα : (j', l') ≠ (i, k)) (b : R) :
    Commute (diagElem i (auxIndex hI i) (auxIndex_ne hI i) k l a)
      (x i' j' hij' (Matrix.single k' l' b)) := by
  by_cases hii' : i = i'
  · subst hii'
    obtain ⟨q, hqi, hqj', -⟩ := hI i j' i
    exact commute_diagElem_x i (auxIndex hI i) j' q (auxIndex_ne hI i) hij' (fun e => hqi e.symm)
      hqj' k l hlk a k' l' (pair_snd_ne hβγ) b
  · by_cases hij2 : i = j'
    · subst hij2
      obtain ⟨q, hqi, hqi', -⟩ := hI i i' i
      exact (commute_x_diagElem i' i (auxIndex hI i) q hij' (auxIndex_ne hI i)
        (fun e => hqi e.symm) (fun e => hqi' e.symm) k l hlk a k' l' (pair_snd_ne hδα) b).symm
    · obtain ⟨q, hqi, hqi', hqj'⟩ := hI i i' j'
      exact commute_diagElem_x_away i (auxIndex hI i) q i' j' (auxIndex_ne hI i)
        (fun e => hqi e.symm) hij' hqi' (fun e => hij2 e.symm) hii' (fun e => hqj' e.symm) k l hlk
        a (Matrix.single k' l' b)

/-- Two off-diagonal block generators commute under the hypotheses of the commutation relation.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem commute_offdiag (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c) (i j : I)
    (hij : i ≠ j) (k l : J) (a : R) (i' j' : I) (hij' : i' ≠ j') (k' l' : J)
    (hβγ : (j, l) ≠ (i', k')) (hδα : (j', l') ≠ (i, k)) (b : R) :
    Commute (x i j hij (Matrix.single k l a)) (x i' j' hij' (Matrix.single k' l' b)) := by
  by_cases hji' : j = i'
  · by_cases hij2 : i = j'
    · subst hji'
      subst hij2
      obtain ⟨p, hpi, hpj, -⟩ := hI i j i
      exact commute_x_x_swap i j p hij hpj.symm hpi k l k' l' (pair_snd_ne hβγ)
        (pair_snd_ne hδα) a b
    · subst hji'
      exact commute_x_of_mul_eq_zero i j j' hij hij' hij2 (Matrix.single k l a)
        (Matrix.single k' l' b) (Matrix.single_mul_single_of_ne (c := a) k l k' (pair_snd_ne hβγ) b)
  · by_cases hij2 : i = j'
    · subst hij2
      exact (commute_x_of_mul_eq_zero i' i j hij' hij (fun e => hji' e.symm)
        (Matrix.single k' l' b) (Matrix.single k l a)
        (Matrix.single_mul_single_of_ne (c := b) k' l' k (pair_snd_ne hδα) a)).symm
    · exact x_commute_of_ne i j i' j' hij hij' hji' (fun e => hij2 e.symm) (Matrix.single k l a)
        (Matrix.single k' l' b)

/-- Relation R2 for `blockGen`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem blockGen_commute (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c)
    (α β γ δ : I × J) (h1 : α ≠ β) (h2 : γ ≠ δ) (hβγ : β ≠ γ) (hδα : δ ≠ α) (a b : R) :
    Commute (blockGen hI α β h1 a) (blockGen hI γ δ h2 b) := by
  obtain ⟨i, k⟩ := α
  obtain ⟨j, l⟩ := β
  obtain ⟨i', k'⟩ := γ
  obtain ⟨j', l'⟩ := δ
  by_cases hij : i = j
  · subst hij
    rw [blockGen_eq hI i k l h1 a]
    by_cases hij' : i' = j'
    · subst hij'
      rw [blockGen_eq hI i' k' l' h2 b]
      by_cases hii' : i = i'
      · subst hii'
        obtain ⟨q, hqi, hqp, -⟩ := hI i (auxIndex hI i) i
        exact commute_diagElem_diagElem_same i (auxIndex hI i) (auxIndex hI i) q
          (auxIndex_ne hI i) (auxIndex_ne hI i) (fun e => hqi e.symm) hqp k l
          (pair_snd_ne h1).symm a k' l' b (pair_snd_ne hβγ) (pair_snd_ne hδα)
      · obtain ⟨q, hqi, hqi', -⟩ := hI i i' i
        obtain ⟨r, hri, hri', hrq⟩ := hI i i' q
        exact commute_diagElem_diagElem_ne i (auxIndex hI i) i' (auxIndex hI i') q r
          (auxIndex_ne hI i) (auxIndex_ne hI i') hii' (fun e => hqi' e.symm) (fun e => hqi e.symm)
          (fun e => hri e.symm) hri' hrq k l (pair_snd_ne h1).symm a k' l' (pair_snd_ne h2).symm b
    · rw [blockGen_ne hI i' j' k' l' h2 hij' b]
      exact commute_diag_left hI i k l (pair_snd_ne h1).symm a i' j' hij' k' l' hβγ hδα b
  · rw [blockGen_ne hI i j k l h1 hij a]
    by_cases hij' : i' = j'
    · subst hij'
      rw [blockGen_eq hI i' k' l' h2 b]
      exact (commute_diag_left hI i' k' l' (pair_snd_ne h2).symm b i j hij k l hδα hβγ a).symm
    · rw [blockGen_ne hI i' j' k' l' h2 hij' b]
      exact commute_offdiag hI i j hij k l a i' j' hij' k' l' hβγ hδα b

/-- Relation R3 for `blockGen`.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem blockGen_adjacent (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c)
    (α β γ : I × J) (h1 : α ≠ β) (h2 : β ≠ γ) (h3 : α ≠ γ) (a b : R) :
    ⁅blockGen hI α β h1 a, blockGen hI β γ h2 b⁆ = blockGen hI α γ h3 (a * b) := by
  obtain ⟨i, k⟩ := α
  obtain ⟨j, l⟩ := β
  obtain ⟨r, t⟩ := γ
  by_cases hij : i = j
  · subst hij
    rw [blockGen_eq hI i k l h1 a]
    obtain ⟨q, hqi, hqp, -⟩ := hI i (auxIndex hI i) i
    by_cases hir : i = r
    · subst hir
      rw [blockGen_eq hI i l t h2 b, blockGen_eq hI i k t h3 (a * b),
        diagElem_indep i (auxIndex hI i) q (auxIndex_ne hI i) (fun e => hqi e.symm) k l
          (pair_snd_ne h1).symm a]
      exact commutator_diagElem_diagElem i (auxIndex hI i) q (auxIndex_ne hI i)
        (fun e => hqi e.symm) hqp k l t (pair_snd_ne h1).symm (pair_snd_ne h2).symm
        (pair_snd_ne h3).symm a b
    · rw [blockGen_ne hI i r l t h2 hir b, blockGen_ne hI i r k t h3 hir (a * b)]
      obtain ⟨q', hq'i, hq'r, -⟩ := hI i r i
      rw [diagElem_indep i (auxIndex hI i) q' (auxIndex_ne hI i) (fun e => hq'i e.symm) k l
        (pair_snd_ne h1).symm a]
      exact commutator_diagElem_x i q' r (fun e => hq'i e.symm) hir hq'r k l t
        (pair_snd_ne h1).symm a b
  · rw [blockGen_ne hI i j k l h1 hij a]
    by_cases hjr : j = r
    · subst hjr
      rw [blockGen_eq hI j l t h2 b, blockGen_ne hI i j k t h3 hij (a * b)]
      obtain ⟨q, hqj, hqi, -⟩ := hI j i j
      rw [diagElem_indep j (auxIndex hI j) q (auxIndex_ne hI j) (fun e => hqj e.symm) l t
        (pair_snd_ne h2).symm b]
      exact commutator_x_diagElem i j q hij (fun e => hqj e.symm) (fun e => hqi e.symm) k l t
        (pair_snd_ne h2).symm a b
    · rw [blockGen_ne hI j r l t h2 hjr b]
      by_cases hir : i = r
      · subst hir
        rw [blockGen_eq hI i k t h3 (a * b)]
        obtain ⟨q, hqi, hqj, -⟩ := hI i j i
        exact (commutator_x_x_eq_diagElem i j q hij (fun e => hqj e.symm) hqi k l t
          (pair_snd_ne h3).symm a b).trans
          (diagElem_indep i q (auxIndex hI i) (fun e => hqi e.symm) (auxIndex_ne hI i) k t
            (pair_snd_ne h3).symm (a * b))
      · rw [blockGen_ne hI i r k t h3 hir (a * b), x_commutator i j r hij hjr hir,
          Matrix.single_mul_single_same (c := a) k l t b]

/-- The generator images of the block map.  (`simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
noncomputable def blockGenerator (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c)
    (g : SteinbergGenerator (I × J) R) : SteinbergGroup I (Matrix J J R) :=
  blockGen hI g.row g.column g.row_ne_column g.coefficient

/-- The block generators satisfy the Steinberg relations of `St_{I×J}(R)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem blockGenerator_kills_relations (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c)
    (w : FreeGroup (SteinbergGenerator (I × J) R))
    (hw : w ∈ SteinbergGroup.relations (I := I × J) (R := R)) :
    FreeGroup.lift (blockGenerator hI) w = 1 := by
  change IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      change blockGen hI i j hij a * blockGen hI i j hij b * (blockGen hI i j hij (a + b))⁻¹ = 1
      rw [blockGen_add hI i j hij a b, mul_inv_cancel]
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅blockGen hI i j hij a, blockGen hI k l hkl b⁆ = 1
      exact (blockGen_commute hI i j k l hij hkl hjk hli a b).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅blockGen hI i j hij a, blockGen hI j k hjk b⁆ * (blockGen hI i k hik (a * b))⁻¹ = 1
      rw [blockGen_adjacent hI i j k hij hjk hik a b, mul_inv_cancel]

/-- **The block map** `St_{I×J}(R) →* St_I(M_J(R))`.  (Ara–Brustenga–Cortiñas 2009, Morita
invariance of `K₂`; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
noncomputable def blockMap (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c) :
    SteinbergGroup (I × J) R →* SteinbergGroup I (Matrix J J R) :=
  PresentedGroup.toGroup (f := blockGenerator hI) (blockGenerator_kills_relations hI)

/-- `blockMap` on generators.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem blockMap_x (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c) (α β : I × J)
    (h : α ≠ β) (a : R) : blockMap hI (x α β h a) = blockGen hI α β h a := by
  exact PresentedGroup.toGroup.of _

/-- `blockMap` on generators with different first coordinates.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem blockMap_x_ne (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c) (i j : I) (k l : J)
    (h : (i, k) ≠ (j, l)) (hij : i ≠ j) (a : R) :
    blockMap hI (x (i, k) (j, l) h a) = x i j hij (Matrix.single k l a) :=
  (blockMap_x hI (i, k) (j, l) h a).trans (blockGen_ne hI i j k l h hij a)

/-- `blockMap` on generators with equal first coordinates.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem blockMap_x_eq (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c) (i : I) (k l : J)
    (h : (i, k) ≠ (i, l)) (a : R) :
    blockMap hI (x (i, k) (i, l) h a) = diagElem i (auxIndex hI i) (auxIndex_ne hI i) k l a :=
  (blockMap_x hI (i, k) (i, l) h a).trans (blockGen_eq hI i k l h a)

end GroupApproximation.Full.LVCohnK2

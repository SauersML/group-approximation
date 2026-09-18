import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionPurelyLargeDefs

/-!
# Purely large ideals: uniform witnesses and the closure step

Lane TWWSch3c3, work order WO-TWWSch-3c-3 (C. Schafhauser, *Subalgebras of simple
AF-algebras*, Ann. of Math. 192 (2020), §3--4; *A new proof of the Tikuisis--White--Winter
theorem*, J. reine angew. Math. 759 (2020), §4; non_mf_group_notes.tex,
thm:fixed-radical-membership).

A `PurelyLargeWitnessData J` supplies *quantitatively uniform* witnesses for the
Hjelmborg--Rørdam condition and for fullness inside the cuts `d J d*` of a right ideal
`J ⊆ B`.  The bounds depend only on `‖d‖`, a lower bound for a Lipschitz "size" of `d`
that is positive exactly off `J`, the size of the element of `J` that is approximated,
and the target precision.  (For the trace-kernel ideal of the norm ultrapower of `Q` the
size is the uniform `2`-seminorm; there the witnesses come from strict comparison.)

Uniformity is what makes the Löwenheim--Skolem closure work: witnesses chosen for
elements of a countable dense set remain witnesses, up to a controlled error, for the
limit points.  This file contains

* `IsPurelyLargeExtension`;
* `PurelyLargeWitnessData` and the choice functions `jApprox`, `stableWitness`,
  `fullWitness`;
* the countable witness sets `jSet`, `kSet`, `fSet`, `witnessSet`;
* the step relation `purelyLargeStep` and its countable-witness property.

Nothing here has been compiled (lane rule).
-/

namespace GroupApproximation.Full.TWWSchafhauser

noncomputable section

variable {B : Type} [CStarAlgebra B]

/-- The extension `0 → I → E → E/I → 0`, realised by subalgebras of `B`, is **purely
large** (Elliott--Kucerovsky 2001): `I ⊆ E` and every cut `closure (e I e*)` with
`e ∈ E \ I` contains a closed separable Hjelmborg--Rørdam-stable subalgebra full in `I`. -/
def IsPurelyLargeExtension (E : StarSubalgebra ℂ B) (I : NonUnitalStarSubalgebra ℂ B) :
    Prop :=
  (I : Set B) ⊆ E ∧ IsPurelyLargeIdeal E I

/-- **Uniform purely-large witnesses** for the cuts of `J`. -/
structure PurelyLargeWitnessData (J : NonUnitalStarSubalgebra ℂ B) where
  /-- A `1`-Lipschitz size function. -/
  size : B → ℝ
  size_le : ∀ x y : B, size x ≤ size y + ‖x - y‖
  size_pos : ∀ x : B, x ∉ J → 0 < size x
  /-- The uniform norm bound for the witnesses. -/
  bound : ℕ → ℕ → ℕ → ℕ → ℝ
  stable : ∀ (a b c e : ℕ) (d j : B), ‖d‖ ≤ (a : ℝ) → 1 / ((b : ℝ) + 1) ≤ size d →
    ‖j‖ ≤ (c : ℝ) → j ∈ J → ∃ k ∈ J, ‖k‖ ≤ bound a b c e ∧
      ‖star (d * k * star d) * (d * k * star d) -
          star (d * j * star d) * (d * j * star d)‖ < 1 / ((e : ℝ) + 1) ∧
      ‖d * k * star d * star (d * k * star d) *
          (star (d * j * star d) * (d * j * star d))‖ < 1 / ((e : ℝ) + 1)
  full : ∀ (a b c e : ℕ) (d j : B), ‖d‖ ≤ (a : ℝ) → 1 / ((b : ℝ) + 1) ≤ size d →
    ‖j‖ ≤ (c : ℝ) → j ∈ J → ∃ p ∈ J, ∃ k ∈ J, ∃ q ∈ J, ‖p‖ ≤ bound a b c e ∧
      ‖k‖ ≤ bound a b c e ∧ ‖q‖ ≤ bound a b c e ∧
      ‖j - p * (d * k * star d) * q‖ < 1 / ((e : ℝ) + 1)

variable {J : NonUnitalStarSubalgebra ℂ B}

/-- The hypotheses under which the witnesses are guaranteed. -/
def WitnessAdmissible (W : PurelyLargeWitnessData J) (a b c : ℕ) (d j : B) : Prop :=
  ‖d‖ ≤ (a : ℝ) ∧ 1 / ((b : ℝ) + 1) ≤ W.size d ∧ ‖j‖ ≤ (c : ℝ) ∧ j ∈ J

theorem exists_jApprox (J : NonUnitalStarSubalgebra ℂ B) (t : B) (m : ℕ) :
    ∃ j : B, j ∈ J ∧
      ((∃ j' ∈ J, ‖t - j'‖ < 1 / ((m : ℝ) + 1)) → ‖t - j‖ < 1 / ((m : ℝ) + 1)) := by
  by_cases h : ∃ j' ∈ J, ‖t - j'‖ < 1 / ((m : ℝ) + 1)
  · obtain ⟨j', hj', hlt⟩ := h
    exact ⟨j', hj', fun _ => hlt⟩
  · exact ⟨0, zero_mem J, fun h' => absurd h' h⟩

/-- An element of `J` within `1/(m+1)` of `t`, whenever there is one. -/
def jApprox (J : NonUnitalStarSubalgebra ℂ B) (t : B) (m : ℕ) : B :=
  (exists_jApprox J t m).choose

theorem jApprox_mem (J : NonUnitalStarSubalgebra ℂ B) (t : B) (m : ℕ) : jApprox J t m ∈ J :=
  (exists_jApprox J t m).choose_spec.1

theorem jApprox_spec (J : NonUnitalStarSubalgebra ℂ B) (t : B) (m : ℕ)
    (h : ∃ j' ∈ J, ‖t - j'‖ < 1 / ((m : ℝ) + 1)) :
    ‖t - jApprox J t m‖ < 1 / ((m : ℝ) + 1) :=
  (exists_jApprox J t m).choose_spec.2 h

theorem exists_stableWitness (W : PurelyLargeWitnessData J) (a b c e : ℕ) (d j : B) :
    ∃ k : B, k ∈ J ∧ (WitnessAdmissible W a b c d j → ‖k‖ ≤ W.bound a b c e ∧
      ‖star (d * k * star d) * (d * k * star d) -
          star (d * j * star d) * (d * j * star d)‖ < 1 / ((e : ℝ) + 1) ∧
      ‖d * k * star d * star (d * k * star d) *
          (star (d * j * star d) * (d * j * star d))‖ < 1 / ((e : ℝ) + 1)) := by
  by_cases h : WitnessAdmissible W a b c d j
  · obtain ⟨k, hk, h1, h2, h3⟩ := W.stable a b c e d j h.1 h.2.1 h.2.2.1 h.2.2.2
    exact ⟨k, hk, fun _ => ⟨h1, h2, h3⟩⟩
  · exact ⟨0, zero_mem J, fun h' => absurd h' h⟩

/-- The chosen Hjelmborg--Rørdam witness. -/
def stableWitness (W : PurelyLargeWitnessData J) (a b c e : ℕ) (d j : B) : B :=
  (exists_stableWitness W a b c e d j).choose

theorem stableWitness_mem (W : PurelyLargeWitnessData J) (a b c e : ℕ) (d j : B) :
    stableWitness W a b c e d j ∈ J :=
  (exists_stableWitness W a b c e d j).choose_spec.1

theorem stableWitness_spec (W : PurelyLargeWitnessData J) (a b c e : ℕ) (d j : B)
    (h : WitnessAdmissible W a b c d j) :
    ‖stableWitness W a b c e d j‖ ≤ W.bound a b c e ∧
      ‖star (d * stableWitness W a b c e d j * star d) *
            (d * stableWitness W a b c e d j * star d) -
          star (d * j * star d) * (d * j * star d)‖ < 1 / ((e : ℝ) + 1) ∧
      ‖d * stableWitness W a b c e d j * star d *
            star (d * stableWitness W a b c e d j * star d) *
          (star (d * j * star d) * (d * j * star d))‖ < 1 / ((e : ℝ) + 1) :=
  (exists_stableWitness W a b c e d j).choose_spec.2 h

theorem exists_fullWitness (W : PurelyLargeWitnessData J) (a b c e : ℕ) (d j : B) :
    ∃ w : B × B × B, w.1 ∈ J ∧ w.2.1 ∈ J ∧ w.2.2 ∈ J ∧
      (WitnessAdmissible W a b c d j → ‖w.1‖ ≤ W.bound a b c e ∧
        ‖w.2.1‖ ≤ W.bound a b c e ∧ ‖w.2.2‖ ≤ W.bound a b c e ∧
        ‖j - w.1 * (d * w.2.1 * star d) * w.2.2‖ < 1 / ((e : ℝ) + 1)) := by
  by_cases h : WitnessAdmissible W a b c d j
  · obtain ⟨p, hp, k, hk, q, hq, h1, h2, h3, h4⟩ :=
      W.full a b c e d j h.1 h.2.1 h.2.2.1 h.2.2.2
    exact ⟨(p, k, q), hp, hk, hq, fun _ => ⟨h1, h2, h3, h4⟩⟩
  · exact ⟨(0, 0, 0), zero_mem J, zero_mem J, zero_mem J, fun h' => absurd h' h⟩

/-- The chosen fullness witness `(p, k, q)`. -/
def fullWitness (W : PurelyLargeWitnessData J) (a b c e : ℕ) (d j : B) : B × B × B :=
  (exists_fullWitness W a b c e d j).choose

theorem fullWitness_mem (W : PurelyLargeWitnessData J) (a b c e : ℕ) (d j : B) :
    (fullWitness W a b c e d j).1 ∈ J ∧ (fullWitness W a b c e d j).2.1 ∈ J ∧
      (fullWitness W a b c e d j).2.2 ∈ J :=
  ⟨(exists_fullWitness W a b c e d j).choose_spec.1,
    (exists_fullWitness W a b c e d j).choose_spec.2.1,
    (exists_fullWitness W a b c e d j).choose_spec.2.2.1⟩

theorem fullWitness_spec (W : PurelyLargeWitnessData J) (a b c e : ℕ) (d j : B)
    (h : WitnessAdmissible W a b c d j) :
    ‖(fullWitness W a b c e d j).1‖ ≤ W.bound a b c e ∧
      ‖(fullWitness W a b c e d j).2.1‖ ≤ W.bound a b c e ∧
      ‖(fullWitness W a b c e d j).2.2‖ ≤ W.bound a b c e ∧
      ‖j - (fullWitness W a b c e d j).1 * (d * (fullWitness W a b c e d j).2.1 * star d) *
          (fullWitness W a b c e d j).2.2‖ < 1 / ((e : ℝ) + 1) :=
  (exists_fullWitness W a b c e d j).choose_spec.2.2.2 h

/-- Approximants in `J` of the elements of `c`. -/
def jSet (J : NonUnitalStarSubalgebra ℂ B) (c : Set B) : Set B :=
  ⋃ m : ℕ, (fun t => jApprox J t m) '' c

/-- The Hjelmborg--Rørdam witnesses for pairs from `c × jSet J c`. -/
def kSet (W : PurelyLargeWitnessData J) (c : Set B) : Set B :=
  ⋃ a : ℕ, ⋃ b : ℕ, ⋃ n : ℕ, ⋃ e : ℕ,
    (fun p : B × B => stableWitness W a b n e p.1 p.2) '' (c ×ˢ jSet J c)

/-- The fullness witness triples for pairs from `c × jSet J c`. -/
def fTriples (W : PurelyLargeWitnessData J) (c : Set B) : Set (B × B × B) :=
  ⋃ a : ℕ, ⋃ b : ℕ, ⋃ n : ℕ, ⋃ e : ℕ,
    (fun p : B × B => fullWitness W a b n e p.1 p.2) '' (c ×ˢ jSet J c)

/-- The components of the fullness witnesses. -/
def fSet (W : PurelyLargeWitnessData J) (c : Set B) : Set B :=
  (fun w : B × B × B => w.1) '' fTriples W c ∪ (fun w : B × B × B => w.2.1) '' fTriples W c ∪
    (fun w : B × B × B => w.2.2) '' fTriples W c

/-- All witnesses attached to `c`. -/
def witnessSet (W : PurelyLargeWitnessData J) (c : Set B) : Set B :=
  kSet W c ∪ fSet W c

theorem mem_jSet {c : Set B} {t : B} (ht : t ∈ c) (m : ℕ) : jApprox J t m ∈ jSet J c :=
  Set.mem_iUnion.mpr ⟨m, ⟨t, ht, rfl⟩⟩

theorem mem_kSet (W : PurelyLargeWitnessData J) {c : Set B} {t j : B} (ht : t ∈ c)
    (hj : j ∈ jSet J c) (a b n e : ℕ) : stableWitness W a b n e t j ∈ kSet W c :=
  Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨n,
    Set.mem_iUnion.mpr ⟨e, ⟨(t, j), Set.mk_mem_prod ht hj, rfl⟩⟩⟩⟩⟩

theorem mem_fTriples (W : PurelyLargeWitnessData J) {c : Set B} {t j : B} (ht : t ∈ c)
    (hj : j ∈ jSet J c) (a b n e : ℕ) : fullWitness W a b n e t j ∈ fTriples W c :=
  Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨n,
    Set.mem_iUnion.mpr ⟨e, ⟨(t, j), Set.mk_mem_prod ht hj, rfl⟩⟩⟩⟩⟩

/-- The three components of a fullness witness lie in `witnessSet`. -/
theorem fullWitness_mem_witnessSet (W : PurelyLargeWitnessData J) {c : Set B} {t j : B}
    (ht : t ∈ c) (hj : j ∈ jSet J c) (a b n e : ℕ) :
    (fullWitness W a b n e t j).1 ∈ witnessSet W c ∧
      (fullWitness W a b n e t j).2.1 ∈ witnessSet W c ∧
      (fullWitness W a b n e t j).2.2 ∈ witnessSet W c := by
  have hw := mem_fTriples W ht hj a b n e
  refine ⟨Set.mem_union_right _ (Set.mem_union_left _ (Set.mem_union_left _ ⟨_, hw, rfl⟩)),
    Set.mem_union_right _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, hw, rfl⟩)),
    Set.mem_union_right _ (Set.mem_union_right _ ⟨_, hw, rfl⟩)⟩

theorem stableWitness_mem_witnessSet (W : PurelyLargeWitnessData J) {c : Set B} {t j : B}
    (ht : t ∈ c) (hj : j ∈ jSet J c) (a b n e : ℕ) :
    stableWitness W a b n e t j ∈ witnessSet W c :=
  Set.mem_union_left _ (mem_kSet W ht hj a b n e)

theorem countable_jSet (J : NonUnitalStarSubalgebra ℂ B) {c : Set B} (hc : c.Countable) :
    (jSet J c).Countable :=
  Set.countable_iUnion fun m => hc.image _

theorem countable_witnessSet (W : PurelyLargeWitnessData J) {c : Set B} (hc : c.Countable) :
    (witnessSet W c).Countable := by
  have hp : (c ×ˢ jSet J c).Countable := hc.prod (countable_jSet J hc)
  have hk : (kSet W c).Countable :=
    Set.countable_iUnion fun _ => Set.countable_iUnion fun _ =>
      Set.countable_iUnion fun _ => Set.countable_iUnion fun _ => hp.image _
  have hT : (fTriples W c).Countable :=
    Set.countable_iUnion fun _ => Set.countable_iUnion fun _ =>
      Set.countable_iUnion fun _ => Set.countable_iUnion fun _ => hp.image _
  exact hk.union (((hT.image _).union (hT.image _)).union (hT.image _))

/-- `D` contains the witnesses for a countable set dense in `D₀`. -/
def purelyLargeStep (W : PurelyLargeWitnessData J) (D₀ D : StarSubalgebra ℂ B) : Prop :=
  ∃ c : Set B, (D₀ : Set B) ⊆ closure c ∧ witnessSet W c ⊆ D

/-- The step relation has countably many witnesses (shape of `exists_isSepClosed_of_step`). -/
theorem purelyLargeStep_exists (W : PurelyLargeWitnessData J) (D₀ : StarSubalgebra ℂ B)
    (h₀ : IsSepClosed D₀) :
    ∃ s : Set B, s.Countable ∧ ∀ D : StarSubalgebra ℂ B, D₀ ≤ D → s ⊆ D →
      purelyLargeStep W D₀ D := by
  obtain ⟨c, hc, hdense⟩ := h₀.2
  exact ⟨witnessSet W c, countable_witnessSet W hc, fun _ _ hs => ⟨c, hdense, hs⟩⟩

end

end GroupApproximation.Full.TWWSchafhauser

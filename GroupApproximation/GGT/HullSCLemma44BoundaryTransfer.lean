import GroupApproximation.GGT.HullSCLemma44ContiguityDiagram

/-!
# Boundary transfer from exterior cells in Hull's Lemma 4.4

Osin's Appendix Lemma 9.7 produces an exterior contiguity cell for a reduced
relative diagram.  This file proves the part after that production which is
independent of a chosen Hull alphabet.  A large exterior cell contradicts a
short boundary word over every subalphabet of the relative alphabet.  Applying
that contradiction at the full relative alphabet gives injectivity on the
union of peripheral subgroups, because every peripheral element is a
one-letter relative word.

The remaining construction of the exterior cell is Osin's Appendix Lemma 9.7.
The resulting general boundary-transfer statements are also the form used by
the reduced power diagrams in Hull's Lemma 4.9.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-- A large exterior cell contradicts a sufficiently short boundary over any
alphabet contained in the relative alphabet.  This is the numerical last step
of Osin's Lemma 5.1(2), separated from the special source alphabet used by
Hull's Lemma 4.4. -/
theorem false_of_lemma44LargeExteriorCell_of_boundarySubset
    {G : Type u} [Group G] {Lambda : Type w} {X : Alphabet G}
    (P : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    (Z : Lemma44ReducedRelatorDiagram X W R)
    (hX : X.carrier ⊆ P.alphabet.carrier)
    (hsc : RelWord.IsLemma44Input P W eps mu rho)
    (hmu : mu ≤ 1 / 52)
    (hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    (C : Lemma44LargeExteriorCell P W eps mu Z) : False := by
  have hlongNat : rho ≤ C.relator.length := hsc.long C.relator C.relator_mem
  have hcoeff : (3 / 4 : ℝ) ≤ 1 - 13 * mu := by linarith
  have hrelator_nonneg : (0 : ℝ) ≤ C.relator.length := Nat.cast_nonneg _
  have hexterior_fraction :
      (3 / 4 : ℝ) * C.relator.length < C.exterior.length :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcoeff hrelator_nonneg)
      C.exterior_large
  have hlong : (rho : ℝ) ≤ C.relator.length := by exact_mod_cast hlongNat
  have hexterior_long :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) < C.exterior.length := by
    have hscale : (3 / 4 : ℝ) * (rho : ℝ) ≤
        (3 / 4 : ℝ) * C.relator.length :=
      mul_le_mul_of_nonneg_left hlong (by norm_num)
    exact lt_trans hthreshold (lt_of_le_of_lt hscale hexterior_fraction)
  have hexterior_le : C.exterior.length ≤ C.relator.length := by
    rw [C.relator_decomposition]
    simp only [List.length_append]
    omega
  have htake : C.relator.take C.exterior.length = C.exterior := by
    rw [C.relator_decomposition]
    simp
  have hqg := hsc.quasiGeodesic C.relator C.relator_mem
  have hlowerRaw := (hqg 0 C.exterior.length (Nat.zero_le _)
    hexterior_le).1
  have hzero : GGT.RelLetter.listVal (C.relator.take 0) = 1 := by
    simp [GGT.RelLetter.listVal]
  dsimp only at hlowerRaw
  rw [hzero, htake, wordDist_one_left] at hlowerRaw
  have hlower : (C.exterior.length : ℝ) / 4 - 1 ≤
      (wordNorm P.alphabet.carrier
        (GGT.RelLetter.listVal C.exterior) : ℝ) := by
    norm_num at hlowerRaw ⊢
    exact hlowerRaw
  have hleftRel : wordNorm P.alphabet.carrier C.leftConnector ≤ eps :=
    C.leftConnector_short
  have hrightRel : wordNorm P.alphabet.carrier C.rightConnector ≤ eps :=
    C.rightConnector_short
  have harcWord : IsWord P.alphabet.carrier
      C.boundaryArc.arc C.boundaryArc.arc.prod := by
    refine ⟨?_, rfl⟩
    intro x hx
    exact hX (C.boundaryArc.arc_isWord.letters x hx)
  have harcRel : wordNorm P.alphabet.carrier C.boundaryArc.arc.prod ≤ 2 * R :=
    le_trans (wordNorm_le_length harcWord)
      C.boundaryArc.arc_length_le_two_mul_radius
  have hmul₁ := wordNorm_mul_le P.alphabet.symmetricGenerating
    C.leftConnector C.boundaryArc.arc.prod
  have hmul₂ := wordNorm_mul_le P.alphabet.symmetricGenerating
    (C.leftConnector * C.boundaryArc.arc.prod) C.rightConnector
  have hupper : wordNorm P.alphabet.carrier
      (GGT.RelLetter.listVal C.exterior) ≤ 2 * R + 2 * eps := by
    rw [C.exterior_value]
    omega
  have hupperReal :
      (wordNorm P.alphabet.carrier
        (GGT.RelLetter.listVal C.exterior) : ℝ) ≤
          ((2 * R + 2 * eps : ℕ) : ℝ) := by
    exact_mod_cast hupper
  have hlowerStrict :
      ((2 * R + 2 * eps : ℕ) : ℝ) < C.exterior.length / 4 - 1 := by
    have hcast : ((2 * R + 2 * eps + 1 : ℕ) : ℝ) =
        ((2 * R + 2 * eps : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast] at hexterior_long
    linarith
  linarith

/-- An exterior-cell Greendlinger certificate gives injectivity on a ball of
any alphabet contained in the relative alphabet.  The proof is the
least-area normal-closure reduction followed by the preceding numerical
contradiction. -/
theorem injOn_cayleyBall_of_largeExteriorCells_of_boundarySubset
    {G : Type u} [Group G] {Lambda : Type w} {X : Alphabet G}
    (P : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    (hX : X.carrier ⊆ P.alphabet.carrier)
    (hsc : RelWord.IsLemma44Input P W eps mu rho)
    (hmu : mu ≤ 1 / 52)
    (hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    {Q : Type*} [Group Q] (q : G →* Q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hgreendlinger : ∀ Z : Lemma44OrientedRelatorDiagram X W R,
      Nonempty (Lemma44LargeExteriorCell P W eps mu
        Z.toLemma44ReducedRelatorDiagram)) :
    Set.InjOn q (cayleyBall X R) := by
  by_contra hnot
  obtain ⟨Z₀⟩ := exists_lemma44ReducedRelatorDiagram_of_not_injOn
    X W R q hker hnot
  obtain ⟨Z⟩ := Z₀.exists_oriented hsc.toIsSmallCancellation
  obtain ⟨C⟩ := hgreendlinger Z
  exact false_of_lemma44LargeExteriorCell_of_boundarySubset P
    Z.toLemma44ReducedRelatorDiagram hX hsc hmu hthreshold C

/-- Every element of every peripheral subgroup is in the radius-one ball of
the relative Cayley alphabet. -/
theorem peripheralUnion_subset_cayleyBall_one
    {G : Type u} [Group G] {Lambda : Type w} (P : GGT.RelGenSet G Lambda) :
    (⋃ i : Lambda, (P.fam i : Set G)) ⊆ cayleyBall P.alphabet 1 := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  rw [mem_cayleyBall_iff, wordDist_one_left]
  apply wordNorm_le_one_of_mem
  exact GGT.RelGenSet.fam_subset_alphabet P i hxi

/-- Injectivity on the unit relative ball restricts to the whole union of the
peripheral subgroups. -/
theorem injOn_peripheralUnion_of_injOn_cayleyBall_one
    {G : Type u} [Group G] {Lambda : Type w} (P : GGT.RelGenSet G Lambda)
    {Q : Type*} (q : G → Q)
    (hinj : Set.InjOn q (cayleyBall P.alphabet 1)) :
    Set.InjOn q (⋃ i : Lambda, (P.fam i : Set G)) := by
  intro x hx y hy hxy
  exact hinj (peripheralUnion_subset_cayleyBall_one P hx)
    (peripheralUnion_subset_cayleyBall_one P hy) hxy

/-- The original Cayley ball embeds in a relative Cayley ball when its alphabet
is contained in the relative alphabet. -/
theorem cayleyBall_subset_of_alphabet_subset
    {G : Type u} [Group G] (A B : Alphabet G)
    (hAB : A.carrier ⊆ B.carrier) (R : ℕ) :
    cayleyBall A R ⊆ cayleyBall B R := by
  intro x hx
  rw [mem_cayleyBall_iff, wordDist_one_left] at hx ⊢
  exact le_trans
    (wordNorm_mono hAB (wordLengths_nonempty A.symmetricGenerating x)) hx

/-- Increasing the radius enlarges a Cayley ball. -/
theorem cayleyBall_subset_of_le_radius
    {G : Type u} [Group G] (A : Alphabet G) {R R' : ℕ}
    (hRR' : R ≤ R') : cayleyBall A R ⊆ cayleyBall A R' := by
  intro x hx
  rw [mem_cayleyBall_iff] at hx ⊢
  exact le_trans hx hRR'

/-- A single Greendlinger certificate at the relative radius `max R 1` gives
both injectivity clauses of Hull's Lemma 4.4: the requested original ball and
the entire source peripheral union.  The hyperbolic-embedding clause of the
lemma needs the separate relative-presentation isoperimetric argument in
Osin's Lemma 5.1. -/
theorem injOn_cayleyBall_and_peripheralUnion_of_largeExteriorCells
    {G : Type u} [Group G] {Lambda : Type w} {A : Alphabet G}
    (P : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    (hA : A.carrier ⊆ P.alphabet.carrier)
    (hsc : RelWord.IsLemma44Input P W eps mu rho)
    (hmu : mu ≤ 1 / 52)
    (hthreshold :
      4 * ((2 * max R 1 + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    {Q : Type*} [Group Q] (q : G →* Q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hgreendlinger : ∀ Z :
      Lemma44OrientedRelatorDiagram P.alphabet W (max R 1),
      Nonempty (Lemma44LargeExteriorCell P W eps mu
        Z.toLemma44ReducedRelatorDiagram)) :
    Set.InjOn q (cayleyBall A R) ∧
      Set.InjOn q (⋃ i : Lambda, (P.fam i : Set G)) := by
  have hinjRel : Set.InjOn q (cayleyBall P.alphabet (max R 1)) :=
    injOn_cayleyBall_of_largeExteriorCells_of_boundarySubset P
      (X := P.alphabet) (R := max R 1) Set.Subset.rfl hsc hmu hthreshold
      q hker hgreendlinger
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    apply hinjRel
    · exact cayleyBall_subset_of_le_radius P.alphabet (Nat.le_max_left _ _)
        (cayleyBall_subset_of_alphabet_subset A P.alphabet hA R hx)
    · exact cayleyBall_subset_of_le_radius P.alphabet (Nat.le_max_left _ _)
        (cayleyBall_subset_of_alphabet_subset A P.alphabet hA R hy)
    · exact hxy
  · apply injOn_peripheralUnion_of_injOn_cayleyBall_one P q
    intro x hx y hy hxy
    apply hinjRel
    · exact cayleyBall_subset_of_le_radius P.alphabet (Nat.le_max_right _ _) hx
    · exact cayleyBall_subset_of_le_radius P.alphabet (Nat.le_max_right _ _) hy
    · exact hxy

end HullSC
end GroupApproximation

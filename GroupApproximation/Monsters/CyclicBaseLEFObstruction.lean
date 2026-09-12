import GroupApproximation.Monsters.LiteralCyclicCalibration
import GroupApproximation.Sofic.LEFSofic

/-!
# The cyclic-base marked word admits no exact finite model

The cyclic-base calibration of `LiteralCyclicCalibration` produces a group in
which the marked word survives (`mark_ne_one`, `quotientMap_mark_ne_one`)
while every finite-dimensional linear representation kills it
(`finiteDimensional_kill`).  It is tempting to conclude that the realized
Clifford quotient is approximable by *exact* finite models -- that it is
locally embeddable into finite groups, and hence weakly MF and operator-MF
through `isWeakMF_of_isLEF`.

This file proves that this route is closed: the cyclic-base pattern is
incompatible with exact finite models.  The mechanism is one line of finite
group theory.  In a finite group, the stable relation `t γ t⁻¹ = γ²` makes
`γ` conjugate to its own square, so iterating it around the finite order `N`
of `t` gives `γ^(2^N) = γ`; hence `γ` already lies in the subgroup generated
by `γ²`.  Anything commuting with `γ²` therefore commutes with `γ`.  Since
`c` commutes with `γ`, conjugating by `t` makes `t c t⁻¹` commute with
`t γ t⁻¹ = γ²`, hence with `γ`, and the marked commutator
`⁅t c t⁻¹, γ (t c t⁻¹) γ⁻¹⁆` collapses to `⁅d, d⁆ = 1`.

`markedCompressionWord_eq_one_of_finite` is that statement.  Local
multiplicativity on a large enough finite test set transports the two
relations verbatim into the finite permutation target of `IsLEF`, so
`not_isLEF_of_markedCompression` upgrades it to a genuine non-embeddability
theorem, applied here to the presented literal group, to the ambient Clifford
model, and to the realized quotient itself.

Two consequences worth stating plainly.  First, none of these groups is
residually finite.  Second, and this is the point of the file, any MF
statement about the realized cyclic quotient must come from genuinely
*approximate* matrix models: the exact-model routes of this library
(`isLEF_of_residuallyFinite`, `isLEF_of_locallyFinite`, and everything
downstream of `isWeakMF_of_isLEF`) provably do not apply to it.

Nothing here contradicts the marked word being invisible to the MF radical;
that is an approximate-model statement about a different mode of
approximation.
-/

namespace GroupApproximation
namespace CyclicBaseLEFObstruction

open scoped commutatorElement
open CyclicBaseCalibration
open LiteralCyclicCalibration

/-! ## The finite-model collapse -/

/-- Iterating the compression relation: conjugating `a` by `t^j` doubles the
exponent `j` times. -/
theorem conj_pow_two_pow {H : Type*} [Group H] {t a : H}
    (hst : t * a * t⁻¹ = a ^ 2) :
    ∀ j : ℕ, t ^ j * a * (t ^ j)⁻¹ = a ^ (2 ^ j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      have hsplit : t ^ (j + 1) * a * (t ^ (j + 1))⁻¹
          = t * (t ^ j * a * (t ^ j)⁻¹) * t⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        simp [mul_assoc]
      calc t ^ (j + 1) * a * (t ^ (j + 1))⁻¹
          = t * (t ^ j * a * (t ^ j)⁻¹) * t⁻¹ := hsplit
        _ = t * a ^ (2 ^ j) * t⁻¹ := by rw [ih]
        _ = (t * a * t⁻¹) ^ (2 ^ j) := conj_pow.symm
        _ = (a ^ 2) ^ (2 ^ j) := by rw [hst]
        _ = a ^ (2 ^ (j + 1)) := by rw [← pow_mul, ← pow_succ']

/-- The compressed generator is recovered from its own square: the
compression relation makes `a` conjugate to `a ^ 2`, and iterating around
the order of `t` returns to `a` (trivially so when `t` has infinite
order, since then `orderOf t = 0`). -/
theorem eq_pow_two_pow_orderOf {H : Type*} [Group H] {t a : H}
    (hst : t * a * t⁻¹ = a ^ 2) :
    a ^ (2 ^ orderOf t) = a := by
  have h := conj_pow_two_pow hst (orderOf t)
  rw [pow_orderOf_eq_one] at h
  simpa using h.symm

/-- **The finite-model collapse.**  In *every* finite group, the cyclic-base
marked commutator is trivial as soon as the stable relation and the lamp
commutation hold.  No representation theory, no field, and no
finite-dimensionality hypothesis enter: only the finiteness of the ambient
group. -/
theorem markedCompressionWord_eq_one_of_finite {H : Type*} [Group H] [Finite H]
    (t a c : H) (hst : t * a * t⁻¹ = a ^ 2) (hca : Commute c a) :
    markedCompressionWord t a c = 1 := by
  have hconj : Commute (t * c * t⁻¹) (t * a * t⁻¹) := by
    have hc : c * a = a * c := hca.eq
    show (t * c * t⁻¹) * (t * a * t⁻¹) = (t * a * t⁻¹) * (t * c * t⁻¹)
    calc (t * c * t⁻¹) * (t * a * t⁻¹) = t * (c * a) * t⁻¹ := by group
      _ = t * (a * c) * t⁻¹ := by rw [hc]
      _ = (t * a * t⁻¹) * (t * c * t⁻¹) := by group
  rw [hst] at hconj
  -- `t c t⁻¹` commutes with `a ^ 2`, hence with every power of it.
  have hpos : 0 < orderOf t := orderOf_pos t
  obtain ⟨N, hN⟩ : ∃ N : ℕ, orderOf t = N + 1 := ⟨orderOf t - 1, by omega⟩
  have hpow : Commute (t * c * t⁻¹) ((a ^ 2) ^ (2 ^ N)) := hconj.pow_right _
  rw [← pow_mul, ← pow_succ', ← hN, eq_pow_two_pow_orderOf hst] at hpow
  have hfix : a * (t * c * t⁻¹) * a⁻¹ = t * c * t⁻¹ := by
    rw [← hpow.eq, mul_inv_cancel_right]
  rw [markedCompressionWord, hfix, commutatorElement_self]

/-! ## Transporting the two relations into a local model -/

/-- The assignment of the three literal generators `γ₀`, `t`, `c` used to
transport the manuscript's relators into an arbitrary group. -/
def markedGenerator {G : Type*} (t a c : G) : Generator → G
  | 0 => a
  | 1 => t
  | 2 => c

@[simp] theorem markedGenerator_gamma {G : Type*} (t a c : G) :
    markedGenerator t a c gammaIndex = a := rfl
@[simp] theorem markedGenerator_stable {G : Type*} (t a c : G) :
    markedGenerator t a c stableIndex = t := rfl
@[simp] theorem markedGenerator_lamp {G : Type*} (t a c : G) :
    markedGenerator t a c lampIndex = c := rfl

/-- The stable relator, evaluated in an arbitrary group. -/
theorem lift_stableRelator {H : Type*} [Group H] (u : Generator → H) :
    FreeGroup.lift u stableRelator =
      u stableIndex * u gammaIndex * (u stableIndex)⁻¹ *
        ((u gammaIndex) ^ 2)⁻¹ := by
  simp only [stableRelator, stableWord, gammaWord, map_mul, map_inv, map_pow,
    FreeGroup.lift_apply_of]

/-- The lamp-commutation relator, evaluated in an arbitrary group. -/
theorem lift_lampGammaRelator {H : Type*} [Group H] (u : Generator → H) :
    FreeGroup.lift u lampGammaRelator = ⁅u lampIndex, u gammaIndex⁆ := by
  simp only [lampGammaRelator, lampWord, gammaWord, commutatorWord,
    commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]

/-- The marked word, evaluated in an arbitrary group. -/
theorem lift_markedWord {H : Type*} [Group H] (u : Generator → H) :
    FreeGroup.lift u markedWord =
      markedCompressionWord (u stableIndex) (u gammaIndex) (u lampIndex) := by
  simp [markedWord, displacedLampWord, commutatorWord, markedCompressionWord,
    commutatorElement_def]

/-- **The cyclic-base pattern is not locally embeddable into finite groups.**
A group carrying the manuscript's stable relation and lamp commutation, in
which the marked commutator is nontrivial, admits no exact finite local
model: local multiplicativity on a large enough test set would transport both
relations verbatim into a finite permutation group, where
`markedCompressionWord_eq_one_of_finite` kills the marked word. -/
theorem not_isLEF_of_markedCompression {G : Type*} [Group G] (t a c : G)
    (hst : t * a * t⁻¹ = a ^ 2) (hca : Commute c a)
    (hne : markedCompressionWord t a c ≠ 1) : ¬ IsLEF G := by
  classical
  intro hlef
  set φ : FreeGroup Generator →* G :=
    FreeGroup.lift (markedGenerator t a c) with hφ
  have hφstable : φ stableRelator = 1 := by
    rw [hφ, lift_stableRelator, markedGenerator_stable, markedGenerator_gamma,
      hst, mul_inv_cancel]
  have hφlamp : φ lampGammaRelator = 1 := by
    rw [hφ, lift_lampGammaRelator, markedGenerator_lamp, markedGenerator_gamma]
    exact hca.commutator_eq
  have hφmark : φ markedWord = markedCompressionWord t a c := by
    rw [hφ, lift_markedWord, markedGenerator_stable, markedGenerator_gamma,
      markedGenerator_lamp]
  set tracked : Finset (FreeGroup Generator) :=
    {stableRelator, lampGammaRelator, markedWord} with htracked
  have hcontrols : ∀ q : FreeGroup Generator, ∃ s : Finset G,
      ∀ (H : Type) [Group H] (f : G → H), LocalMultiplicativeOn s f →
        FreeGroup.lift (fun i ↦ f (φ (FreeGroup.of i))) q = f (φ q) :=
    fun q ↦ exists_local_word_control φ q
  choose controls hcontrolspec using hcontrols
  set support : Finset G :=
    insert 1 (insert (φ markedWord) (tracked.biUnion controls)) with hsupport
  obtain ⟨n, f, hinj, hlocal⟩ := hlef support
  set u : Generator → Equiv.Perm (Fin n) :=
    fun i ↦ f (φ (FreeGroup.of i)) with hu
  set ψ : FreeGroup Generator →* Equiv.Perm (Fin n) := FreeGroup.lift u with hψ
  have hword : ∀ q ∈ tracked, ψ q = f (φ q) := by
    intro q hq
    apply hcontrolspec q (Equiv.Perm (Fin n)) f
    apply hlocal.mono
    intro z hz
    simp only [hsupport, Finset.mem_insert, Finset.mem_biUnion]
    exact Or.inr (Or.inr ⟨q, hq, hz⟩)
  have hψstable : ψ stableRelator = 1 := by
    rw [hword stableRelator (by simp [htracked]), hφstable, hlocal.map_one]
  have hψlamp : ψ lampGammaRelator = 1 := by
    rw [hword lampGammaRelator (by simp [htracked]), hφlamp, hlocal.map_one]
  have hmodelStable :
      u stableIndex * u gammaIndex * (u stableIndex)⁻¹ = (u gammaIndex) ^ 2 := by
    apply mul_inv_eq_one.mp
    rw [← lift_stableRelator u]
    exact hψstable
  have hmodelLamp : Commute (u lampIndex) (u gammaIndex) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← lift_lampGammaRelator u]
    exact hψlamp
  have hψmark : ψ markedWord = 1 := by
    rw [lift_markedWord u]
    exact markedCompressionWord_eq_one_of_finite _ _ _ hmodelStable hmodelLamp
  apply hne
  rw [← hφmark]
  apply hinj
  · simp [hsupport]
  · simp [hsupport]
  calc f (φ markedWord) = ψ markedWord :=
        (hword markedWord (by simp [htracked])).symm
    _ = 1 := hψmark
    _ = f 1 := hlocal.map_one.symm

/-- The same pattern rules out residual finiteness, since a residually finite
group is LEF. -/
theorem not_residuallyFinite_of_markedCompression {G : Type*} [Group G]
    (t a c : G) (hst : t * a * t⁻¹ = a ^ 2) (hca : Commute c a)
    (hne : markedCompressionWord t a c ≠ 1) : ¬ Group.ResiduallyFinite G := by
  intro h
  haveI := h
  exact not_isLEF_of_markedCompression t a c hst hca hne isLEF_of_residuallyFinite

/-! ## The three cyclic-base groups -/

/-- Every homomorphism from the literal presented group to a finite group
kills the marked word.  This is the finite-group companion of
`finiteDimensional_kill`, and it needs no field and no dimension
hypothesis. -/
theorem finite_image_mark_eq_one {H : Type*} [Group H] [Finite H]
    (pi : LiteralGroup →* H) : pi mark = 1 := by
  rw [mark_eq_markedCompressionWord, map_markedCompressionWord]
  refine markedCompressionWord_eq_one_of_finite _ _ _ ?_ (lamp_comm_gamma.map pi)
  rw [← map_inv, ← map_mul, ← map_mul, stable_relation, map_pow]

/-- **The literal presented group is not LEF.** -/
theorem literalGroup_not_isLEF : ¬ IsLEF LiteralGroup :=
  not_isLEF_of_markedCompression stable gamma lamp stable_relation
    lamp_comm_gamma (by rw [← mark_eq_markedCompressionWord]; exact mark_ne_one)

/-- **The ambient Clifford cyclic model is not LEF.** -/
theorem cliffordBS_not_isLEF : ¬ IsLEF CliffordBS :=
  not_isLEF_of_markedCompression tBS gammaBS cBS tBS_conj_gammaBS
    cBS_comm_gammaBS markedWord_ne_one

/-- **The realized Clifford quotient is not LEF.**  In particular the
exact-model route to operator-MF -- `isWeakMF_of_isLEF` and everything
upstream of it -- is unavailable for this group, and any MF statement about
it must be proved from genuinely approximate matrix models. -/
theorem realizedQuotient_not_isLEF : ¬ IsLEF RealizedQuotient := by
  refine not_isLEF_of_markedCompression (quotientMap stable) (quotientMap gamma)
    (quotientMap lamp) ?_ (lamp_comm_gamma.map quotientMap) ?_
  · rw [← map_inv, ← map_mul, ← map_mul, stable_relation, map_pow]
  · rw [← map_markedCompressionWord, ← mark_eq_markedCompressionWord]
    exact quotientMap_mark_ne_one

/-- The realized quotient is not residually finite. -/
theorem realizedQuotient_not_residuallyFinite :
    ¬ Group.ResiduallyFinite RealizedQuotient := by
  intro h
  haveI := h
  exact realizedQuotient_not_isLEF isLEF_of_residuallyFinite

/-- The literal presented group is not residually finite. -/
theorem literalGroup_not_residuallyFinite :
    ¬ Group.ResiduallyFinite LiteralGroup := by
  intro h
  haveI := h
  exact literalGroup_not_isLEF isLEF_of_residuallyFinite

/-- The exact-model status of the cyclic-base calibration, in one statement:
the marked word survives in the realized quotient, dies in every finite group
image, and blocks local embeddability into finite groups. -/
theorem cyclicBase_exactModel_package :
    quotientMap mark ≠ 1 ∧
      (∀ {H : Type} [Group H] [Finite H] (pi : LiteralGroup →* H),
        pi mark = 1) ∧
      ¬ IsLEF LiteralGroup ∧
      ¬ IsLEF RealizedQuotient ∧
      ¬ Group.ResiduallyFinite RealizedQuotient :=
  ⟨quotientMap_mark_ne_one, fun pi ↦ finite_image_mark_eq_one pi,
    literalGroup_not_isLEF, realizedQuotient_not_isLEF,
    realizedQuotient_not_residuallyFinite⟩

/-! ## Positive controls

Two things could make `not_isLEF_of_markedCompression` say less than it
appears to.  Its hypotheses could be unsatisfiable, in which case it excludes
nothing; or the nontriviality hypothesis could be redundant, in which case
the two relations alone would already exclude LEF and the marked word would
be beside the point.  Neither holds. -/

/-- The hypotheses are inhabited: the Clifford cyclic model satisfies all
three at once, so the criterion is not vacuous. -/
theorem obstruction_hypotheses_inhabited :
    ∃ t a c : CliffordBS,
      t * a * t⁻¹ = a ^ 2 ∧ Commute c a ∧
        markedCompressionWord t a c ≠ 1 :=
  ⟨tBS, gammaBS, cBS, tBS_conj_gammaBS, cBS_comm_gammaBS, markedWord_ne_one⟩

/-- The nontriviality hypothesis carries the argument: the two relations on
their own are compatible with LEF, as the infinite cyclic group with all
three elements trivial shows.  So `hne` cannot simply be dropped. -/
theorem relations_alone_compatible_with_isLEF :
    ∃ t a c : Multiplicative ℤ,
      t * a * t⁻¹ = a ^ 2 ∧ Commute c a ∧
        markedCompressionWord t a c = 1 ∧ IsLEF (Multiplicative ℤ) :=
  ⟨1, 1, 1, by simp, Commute.one_left 1,
    by simp [markedCompressionWord],
    isLEF_multiplicative_int⟩

end CyclicBaseLEFObstruction
end GroupApproximation

import GroupApproximation.Sofic.MonomialModel
import GroupApproximation.Sofic.NormTraceGap
import GroupApproximation.Sofic.OperatorMF
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Sofic.CliffordBSAmenable
import GroupApproximation.Monsters.CyclicBaseLEFObstruction

/-!
# The sharpness paragraph without Tikuisis--White--Winter

`non_mf_groups_exist.tex`, `\section{The cyclic comparison}`
(`\label{sec:necessity}`), paragraph *Sharpness of the Kazhdan hypothesis*
(grep `"hence MF by"`, never a line number: the file is edited concurrently).
The paragraph needs exactly one thing:

> some corona representation of `E_BS` separates the marked word from the
> identity; in the radical language, `w_BS ∉ Res_MF(E_BS)`.

The printed route to that conclusion is *amenable `⟹` MF*: the realized
Clifford quotient is a subgroup of an amenable group, hence amenable, hence MF
by \cite{TWW}.  `Sofic.CliffordBSAmenable` machine-checks every step of that
sentence except the last, and the last one is Tikuisis--White--Winter.

**This file proves the conclusion, and never proves the general theorem.**  It
does not prove that amenable groups are MF, that quasidiagonality holds for any
class of groups, or that the realized Clifford quotient is MF.  It exhibits one
explicit sequence of finite matrix models of the *seven printed relators* of
`E_BS` in which the marked word stays at operator-norm distance `2` from the
identity.  That is all `w_BS ∉ Res_MF(E_BS)` asks for: the MF radical is an
intersection of kernels, so a single corona representation that fails to kill
`w_BS` removes it from every one of them, and no injectivity -- hence no MF
statement about any group -- is involved anywhere.

## Why an approximate model is unavoidable, and what shape it must have

`Monsters.CyclicBaseLEFObstruction` proves that no *exact* finite model can
work: in any finite group the doubling relation makes `⟨γ₀²⟩ = ⟨γ₀⟩`, the lamp
then commutes with the halved element, and the marked word dies.
`LiteralCyclicCalibration.finiteDimensional_kill` proves the same for every
finite-dimensional linear representation over every field.  So the model below
must satisfy the doubling relation only approximately -- and it does, with a
defect `O(1/m)` -- while the marked word is exactly the scalar `-1`.

`Analysis.AmenableQuasidiagonal` proves that models built from *permutation*
matrices are exact or useless: their operator-norm defects are `0` or at least
`1`.  The models here are monomial rather than permutation matrices, and the
whole approximation lives in their phases, which is exactly the room that
dichotomy leaves open.

## The construction

Fix the odd modulus `M = 2m+3` and take the coordinates `Fin 2 × ZMod M`: a
spin coordinate carrying the Clifford sign, a cyclic coordinate carrying the
spectrum.

* `γ₀` is the diagonal unitary `(s, k) ↦ (-1)^s ζ^k`, where `ζ = exp(2πi/M)`.
  Its spectrum is the set of all `2M`-th roots of unity, each once.
* `t` is the coordinate permutation `(s, k) ↦ (s, 2k + b_s)` with `b₀ = 0` and
  `b₁ = m+1`.  Doubling is invertible because `M` is odd, so this is a
  permutation, and it matches the spectrum of `γ₀` against the spectrum of
  `γ₀²` with a mismatch of exactly one `2M`-th root; hence
  `‖t γ₀ t⁻¹ - γ₀²‖ = |1 + ζ^{m+1}| = 2 sin(π/2M)`.
* `c` is `t⁻¹ D t`, where `D = 2^{-1/2}(X + Z)` acts on the spin coordinate
  alone: `X` is the spin flip, `Z` the spin sign.  `D` is a self-adjoint
  unitary, and `γ₀²` does not see the spin coordinate, so `D` commutes with
  `γ₀²` *exactly*; the lamp relation `[c, γ₀] = 1` therefore inherits the
  doubling defect and nothing else.
* The marked word `⁅t c t⁻¹, γ₀ (t c t⁻¹) γ₀⁻¹⁆` is `⁅D, Z D Z⁆`, and the `45°`
  angle between `D` and `Z D Z` makes it the scalar `-1`, exactly.  Being a
  scalar it also satisfies, exactly, the four printed relators that make the
  mark a central involution.

So all seven relators hold in the corona and the mark is `-1` in every model;
its class in the cofinite norm-matrix corona is therefore nontrivial.  At each
single stage `m` exactly **five** of the seven hold on the nose -- the lamp
involution and the four centrality relators of the mark -- while **two** hold
only approximately: the doubling relator `t γ₀ t⁻¹ = γ₀²` with defect
`‖ζ^{m+1} + 1‖`, and the lamp relator `[c, γ₀] = 1` with defect at most twice
that.  The second is approximate even though `D` commutes with `γ₀²` exactly,
because the relator is a commutator with `γ₀` and not with `γ₀²`; it inherits
the doubling defect through the transport, which is what "inherits the doubling
defect and nothing else" above means.  `finiteStageSpecification` states all
eight facts at one stage, in one theorem, so that the split cannot be
misreported.

Note also that the model is not a monomial-matrix model in the strict sense:
`γ₀` and `t` are monomial, but `D = 2^{-1/2}(X + Z)`, and therefore the lamp
`c = t⁻¹ D t`, is a *sum of two* monomial matrices.  That is exactly the room
the permutation-matrix dichotomy of `Analysis.AmenableQuasidiagonal` leaves
open, and `finiteStageSpecification` records the decomposition rather than
leaving "monomial" to be read as a property of every matrix in the file.

The `45°` angle is forced rather than convenient: a self-adjoint unitary whose
conjugate by the spin sign anticommutes with it must weight its even and odd
parts equally.  That is the one irrational constant in the file.

## What this changes, and what it does not

`Sofic.CliffordBSAmenable.isOperatorMF_subgroup_CliffordBS` remains what it is,
a conditional theorem quantifying over the Tikuisis--White--Winter input.
Nothing here discharges it and nothing here should be read as discharging it.
What is discharged is the manuscript's *use* of it in the sharpness paragraph,
which was never the general theorem but only the survival of one marked word in
one corona.

Two consequences for the neighbouring modules, stated so that a later reader
does not over-read either of them.

* `Algebra.AmenableMFProof` and `Analysis.AmenableQuasidiagonal` prove that the
  *permutation* route is closed, and conclude that certifying the manuscript's
  sentence "requires genuinely non-permutation unitaries".  That much is
  confirmed here and is exactly why the models below are monomial.  Their
  further reading -- that the sentence therefore rests on quasidiagonality --
  holds for the sentence's *literal subject*, MF-ness of the realized Clifford
  quotient, and not for the conclusion the paragraph draws from it.
* The other use of amenable `⟹` MF, in `\section{Consequences}` (grep
  `"homomorphism to any countable"`), quantifies over *all* countable amenable
  groups.  Nothing here touches it; it still needs the general theorem.

## Relation to `Sofic.CliffordBSPrintedRoute`

The route this file takes is the one the manuscript's sharpness paragraph
prints since the 2026-08-17 rewrite: the marked word survives in the MF image
`Θ(E_BS)`, and the print no longer claims that the models separate the
realized Clifford quotient.  `Sofic.CliffordBSPrintedRoute` formalizes the
superseded paragraph instead --- solvable base, locally finite lamps, amenable
extension, amenable subgroup, `⟹` MF, compose with a faithful representation of
the quotient --- with the fifth link carried by the explicit hypothesis
`CyclicBaseCalibration.AmenableImpliesMF` and appearing exactly once.  That was
the 1:1 formalization of the paragraph as it stood before the rewrite; what is
here is a *different* argument reaching the same endpoint with no hypothesis.

Nothing in this file may be cited as certifying MF-ness of the realized
Clifford quotient: that statement is
`CliffordBSPrintedRoute.isOperatorMF_realizedQuotient` and still carries its
hypothesis.  The manuscript badges `manuscriptSharpnessOfKazhdanHypothesis` on
the sharpness paragraph, and this module is in the root import closure
(`GroupApproximation.lean`), so the badge is load-bearing: what it certifies is
survival of the mark in an MF quotient of `E_BS`, which is exactly what the
paragraph now claims, and no more.
-/

namespace GroupApproximation
namespace CliffordBSAmenableMF

open Matrix
open scoped Matrix.Norms.L2Operator
open scoped commutatorElement
open LiteralCyclicCalibration

/-! ## Monomial matrix algebra

A monomial matrix is a permutation matrix carrying a phase on each row.  Every
matrix of the model is monomial or a sum of two monomial matrices, and every
computation below is the multiplication rule for them. -/

/-- Monomial matrices agree when their data agree. -/
theorem monomialMatrix_congr (Y : FiniteModel) {d d' : Y → ℂ}
    {σ σ' : Equiv.Perm Y} (hd : ∀ i, d i = d' i) (hσ : σ = σ') :
    monomialMatrix Y d σ = monomialMatrix Y d' σ' := by
  subst hσ
  rw [show d = d' from funext hd]

/-- **The monomial multiplication rule.**  Phases multiply along the first
permutation; the permutations compose in the opposite order. -/
theorem monomialMatrix_mul (Y : FiniteModel) (d d' : Y → ℂ)
    (σ σ' : Equiv.Perm Y) :
    monomialMatrix Y d σ * monomialMatrix Y d' σ'
      = monomialMatrix Y (fun i ↦ d i * d' (σ i)) (σ' * σ) := by
  classical
  ext i k
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ i)]
  · rw [monomialMatrix_apply, monomialMatrix_apply, monomialMatrix_apply,
      if_pos rfl, Equiv.Perm.mul_apply]
    by_cases hk : σ' (σ i) = k
    · rw [if_pos hk, if_pos hk]
    · rw [if_neg hk, if_neg hk, mul_zero]
  · intro j _ hj
    rw [monomialMatrix_apply, if_neg (Ne.symm hj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (σ i)) h

/-- The multiplication rule in the form used below: the caller names the
resulting phase and permutation. -/
theorem monomialMatrix_mul_eq (Y : FiniteModel) (d d' e : Y → ℂ)
    (σ σ' τ : Equiv.Perm Y) (hphase : ∀ i, d i * d' (σ i) = e i)
    (hperm : σ' * σ = τ) :
    monomialMatrix Y d σ * monomialMatrix Y d' σ' = monomialMatrix Y e τ := by
  rw [monomialMatrix_mul]
  exact monomialMatrix_congr Y hphase hperm

/-- Differences of monomial matrices over a common permutation. -/
theorem monomialMatrix_sub_eq (Y : FiniteModel) (d d' e : Y → ℂ)
    (σ : Equiv.Perm Y) (hphase : ∀ i, d i - d' i = e i) :
    monomialMatrix Y d σ - monomialMatrix Y d' σ = monomialMatrix Y e σ := by
  have hsub : monomialMatrix Y d σ - monomialMatrix Y d' σ
      = monomialMatrix Y (fun i ↦ d i - d' i) σ := by
    ext i j
    rw [Matrix.sub_apply, monomialMatrix_apply, monomialMatrix_apply,
      monomialMatrix_apply]
    by_cases h : σ i = j
    · rw [if_pos h, if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, if_neg h, sub_zero]
  rw [hsub]
  exact monomialMatrix_congr Y hphase rfl

/-- Scalars act on the phases. -/
theorem monomialMatrix_smul_eq (Y : FiniteModel) (c : ℂ) (d e : Y → ℂ)
    (σ : Equiv.Perm Y) (hphase : ∀ i, c * d i = e i) :
    c • monomialMatrix Y d σ = monomialMatrix Y e σ := by
  have hsmul : c • monomialMatrix Y d σ
      = monomialMatrix Y (fun i ↦ c * d i) σ := by
    ext i j
    rw [Matrix.smul_apply, monomialMatrix_apply, monomialMatrix_apply,
      smul_eq_mul]
    by_cases h : σ i = j
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hsmul]
  exact monomialMatrix_congr Y hphase rfl

/-- Negation acts on the phases. -/
theorem monomialMatrix_neg (Y : FiniteModel) (d : Y → ℂ) (σ : Equiv.Perm Y) :
    -monomialMatrix Y d σ = monomialMatrix Y (fun i ↦ -d i) σ := by
  ext i j
  rw [Matrix.neg_apply, monomialMatrix_apply, monomialMatrix_apply]
  by_cases h : σ i = j
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, neg_zero]

/-- The trivial monomial matrix is the identity. -/
theorem monomialMatrix_one (Y : FiniteModel) :
    monomialMatrix Y (fun _ ↦ (1 : ℂ)) 1 = 1 := by
  ext i j
  rw [monomialMatrix_apply, Matrix.one_apply, Equiv.Perm.one_apply]

/-- The constant phase `-1` gives the scalar `-1`. -/
theorem monomialMatrix_negOne (Y : FiniteModel) :
    monomialMatrix Y (fun _ ↦ (-1 : ℂ)) 1 = -1 := by
  ext i j
  rw [monomialMatrix_apply, Matrix.neg_apply, Matrix.one_apply,
    Equiv.Perm.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, neg_zero]

/-- Adjoints of monomial matrices. -/
theorem monomialMatrix_conjTranspose (Y : FiniteModel) (d : Y → ℂ)
    (σ : Equiv.Perm Y) :
    (monomialMatrix Y d σ)ᴴ
      = monomialMatrix Y (fun i ↦ (starRingEnd ℂ) (d (σ⁻¹ i))) σ⁻¹ := by
  ext i j
  rw [Matrix.conjTranspose_apply, monomialMatrix_apply, monomialMatrix_apply]
  by_cases h : σ⁻¹ i = j
  · have h' : σ j = i := by
      rw [← h]
      exact Equiv.apply_symm_apply σ i
    -- `rw` closes with a `with_reducible` `rfl`, which does not see through
    -- `starRingEnd ℂ` to `star`; `starRingEnd_apply` lands that step
    -- syntactically.
    rw [if_pos h', if_pos h, h, starRingEnd_apply]
  · have h' : ¬ σ j = i := by
      intro hc
      apply h
      rw [← hc]
      exact Equiv.symm_apply_apply σ j
    -- `star` is `Star.star`, not a bundled hom application, so `map_zero`
    -- has no `⇑f 0` to match; `star_zero` is the lemma for it.
    rw [if_neg h', if_neg h, star_zero]

/-- The adjoint rule in the form used below. -/
theorem monomialMatrix_conjTranspose_eq (Y : FiniteModel) (d e : Y → ℂ)
    (σ τ : Equiv.Perm Y)
    (hphase : ∀ i, (starRingEnd ℂ) (d (σ⁻¹ i)) = e i) (hperm : σ⁻¹ = τ) :
    (monomialMatrix Y d σ)ᴴ = monomialMatrix Y e τ := by
  rw [monomialMatrix_conjTranspose]
  exact monomialMatrix_congr Y hphase hperm

/-- Adjoints of complex scalar multiples, entrywise. -/
theorem conjTranspose_smul_complex {Y : FiniteModel} (c : ℂ)
    (M : Matrix Y Y ℂ) : (c • M)ᴴ = (starRingEnd ℂ) c • Mᴴ := by
  ext i j
  -- `star` is `Star.star`, not a bundled hom, so `map_mul` has no `⇑f (a * b)`
  -- to match; `star_mul'` is the lemma, and `starRingEnd_apply` lands the two
  -- spellings of conjugation on each other syntactically.
  rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, smul_eq_mul, star_mul',
    starRingEnd_apply]

/-! ## The coordinates -/

/-- The odd modulus of the `m`-th model. -/
def modulus (m : ℕ) : ℕ := 2 * m + 3

theorem modulus_pos (m : ℕ) : 0 < modulus m := by
  unfold modulus
  omega

theorem modulus_cast (m : ℕ) : ((modulus m : ℕ) : ℂ) = 2 * (m : ℂ) + 3 := by
  unfold modulus
  push_cast
  ring

instance instNeZeroModulus (m : ℕ) : NeZero (modulus m) := ⟨(modulus_pos m).ne'⟩

instance instFactOneLtModulus (m : ℕ) : Fact (1 < modulus m) :=
  ⟨by unfold modulus; omega⟩

instance instNonemptyZMod (m : ℕ) : Nonempty (ZMod (modulus m)) := ⟨0⟩

/-- The coordinates of the `m`-th model: a spin coordinate carrying the
Clifford sign, and a cyclic coordinate of odd order carrying the spectrum. -/
abbrev site (m : ℕ) : FiniteModel :=
  ⟨Fin 2 × ZMod (modulus m), inferInstance, inferInstance⟩

instance instNonemptySite (m : ℕ) : Nonempty (site m) := ⟨(0, 0)⟩

theorem card_site_pos (m : ℕ) : 0 < Fintype.card (site m) :=
  Fintype.card_pos_iff.mpr (instNonemptySite m)

/-! ## Spins -/

/-- The spin sign. -/
def spin : Fin 2 → ℂ := fun s ↦ if s = 0 then 1 else -1

@[simp] theorem spin_zero : spin 0 = 1 := by simp [spin]
@[simp] theorem spin_one : spin 1 = -1 := by simp [spin]

theorem spin_mul_self (s : Fin 2) : spin s * spin s = 1 := by
  fin_cases s
  · show spin 0 * spin 0 = 1
    rw [spin_zero, one_mul]
  · show spin 1 * spin 1 = 1
    rw [spin_one]
    ring

theorem conj_spin (s : Fin 2) : (starRingEnd ℂ) (spin s) = spin s := by
  fin_cases s
  · show (starRingEnd ℂ) (spin 0) = spin 0
    rw [spin_zero, map_one]
  · show (starRingEnd ℂ) (spin 1) = spin 1
    rw [spin_one, map_neg, map_one]

theorem normSq_spin (s : Fin 2) : Complex.normSq (spin s) = 1 := by
  fin_cases s
  · show Complex.normSq (spin 0) = 1
    rw [spin_zero]
    simp
  · show Complex.normSq (spin 1) = 1
    rw [spin_one]
    simp

/-- The spin flip. -/
def spinSwap : Fin 2 → Fin 2 := fun s ↦ if s = 0 then 1 else 0

@[simp] theorem spinSwap_zero : spinSwap 0 = 1 := by simp [spinSwap]
@[simp] theorem spinSwap_one : spinSwap 1 = 0 := by simp [spinSwap]

theorem spinSwap_spinSwap (s : Fin 2) : spinSwap (spinSwap s) = s := by
  fin_cases s
  · show spinSwap (spinSwap 0) = 0
    rw [spinSwap_zero, spinSwap_one]
  · show spinSwap (spinSwap 1) = 1
    rw [spinSwap_one, spinSwap_zero]

theorem spin_spinSwap (s : Fin 2) : spin (spinSwap s) = -spin s := by
  fin_cases s
  · show spin (spinSwap 0) = -spin 0
    rw [spinSwap_zero, spin_one, spin_zero]
  · show spin (spinSwap 1) = -spin 1
    rw [spinSwap_one, spin_zero, spin_one, neg_neg]

/-! ## Phases -/

/-- The primitive `M`-th root of unity carrying the spectrum. -/
noncomputable def zeta (m : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((modulus m : ℕ) : ℂ))

theorem zeta_pow_modulus (m : ℕ) : zeta m ^ modulus m = 1 := by
  have hm0 : ((modulus m : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (modulus_pos m).ne'
  rw [zeta, ← Complex.exp_nat_mul]
  have harg : ((modulus m : ℕ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I / ((modulus m : ℕ) : ℂ))
        = 2 * (Real.pi : ℂ) * Complex.I := by
    field_simp
  rw [harg]
  exact Complex.exp_two_pi_mul_I

theorem norm_zeta (m : ℕ) : ‖zeta m‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (zeta_pow_modulus m) (modulus_pos m).ne'

theorem zeta_pow_mod (m n : ℕ) : zeta m ^ (n % modulus m) = zeta m ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n (modulus m)]
  rw [pow_add, pow_mul, zeta_pow_modulus, one_pow, one_mul]

/-- The phase attached to a cyclic coordinate. -/
noncomputable def phase (m : ℕ) (k : ZMod (modulus m)) : ℂ := zeta m ^ k.val

theorem norm_phase (m : ℕ) (k : ZMod (modulus m)) : ‖phase m k‖ = 1 := by
  rw [phase, norm_pow, norm_zeta, one_pow]

theorem normSq_phase (m : ℕ) (k : ZMod (modulus m)) :
    Complex.normSq (phase m k) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_phase, one_pow]

theorem phase_mul_conj (m : ℕ) (k : ZMod (modulus m)) :
    phase m k * (starRingEnd ℂ) (phase m k) = 1 := by
  rw [Complex.mul_conj, normSq_phase]
  norm_num

theorem phase_add (m : ℕ) (j k : ZMod (modulus m)) :
    phase m (j + k) = phase m j * phase m k := by
  rw [phase, phase, phase, ZMod.val_add, zeta_pow_mod, pow_add]

theorem phase_zero (m : ℕ) : phase m 0 = 1 := by
  rw [phase, ZMod.val_zero, pow_zero]

theorem phase_one (m : ℕ) : phase m 1 = zeta m := by
  rw [phase, ZMod.val_one, pow_one]

theorem phase_natCast (m n : ℕ) :
    phase m ((n : ℕ) : ZMod (modulus m)) = zeta m ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, phase_zero, pow_zero]
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, phase_add, ih, phase_one, pow_succ]

theorem phase_two_mul (m : ℕ) (k : ZMod (modulus m)) :
    phase m (2 * k) = phase m k * phase m k := by
  rw [two_mul, phase_add]

/-! ## The defect phase

The single approximate quantity of the construction: the mismatch between the
spectrum of `γ₀` and the spectrum of `γ₀²`, one `2M`-th root of unity. -/

/-- The phase by which the model misses the doubling relation. -/
noncomputable def defectPhase (m : ℕ) : ℂ :=
  phase m (((m + 1 : ℕ) : ZMod (modulus m)))

/-- The elementary field identity behind `defectPhase_eq`: when `2A = M - 1`,
`A` copies of `2p/M` fall exactly `p/M` short of `p`.

It is stated for an abstract `p` on purpose.  With `π` and `Complex.I` in
place the same goal is a complex-cast identity that `field_simp` does not
close; with them abstracted away it is four rewrites and no `field_simp`. -/
theorem mul_two_div_eq_sub_div (p M A : ℂ) (hM : M ≠ 0) (hA : A * 2 = M - 1) :
    A * (2 * p / M) = p + -(p / M) := by
  have h : A * (2 * p / M) = A * 2 * p / M := by ring
  rw [h, hA, sub_mul, one_mul, sub_div, mul_div_cancel_left₀ p hM,
    sub_eq_add_neg]

theorem defectPhase_eq (m : ℕ) :
    defectPhase m
      = -Complex.exp
        (-((Real.pi : ℂ) * Complex.I / ((modulus m : ℕ) : ℂ))) := by
  have hm0 : ((modulus m : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (modulus_pos m).ne'
  rw [defectPhase, phase_natCast, zeta, ← Complex.exp_nat_mul]
  have harg : ((m + 1 : ℕ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I / ((modulus m : ℕ) : ℂ))
        = (Real.pi : ℂ) * Complex.I
          + -((Real.pi : ℂ) * Complex.I / ((modulus m : ℕ) : ℂ)) := by
    -- `2 * π * I` parses as `(2 * π) * I`; the identity below wants `2 * (π * I)`
    rw [mul_assoc (2 : ℂ) (Real.pi : ℂ) Complex.I]
    refine mul_two_div_eq_sub_div _ _ _ hm0 ?_
    rw [modulus_cast]
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

theorem norm_defectPhase_add_one_le (m : ℕ) (hm : 1 ≤ m) :
    ‖defectPhase m + 1‖ ≤ 2 * (Real.pi / ((modulus m : ℕ) : ℝ)) := by
  have hMpos : (0 : ℝ) < ((modulus m : ℕ) : ℝ) := by
    exact_mod_cast modulus_pos m
  have hM5 : (5 : ℝ) ≤ ((modulus m : ℕ) : ℝ) := by
    have h5 : 5 ≤ modulus m := by unfold modulus; omega
    exact_mod_cast h5
  have hnorm : ‖-((Real.pi : ℂ) * Complex.I / ((modulus m : ℕ) : ℂ))‖
      = Real.pi / ((modulus m : ℕ) : ℝ) := by
    rw [norm_neg, norm_div, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_natCast]
  have hle : ‖-((Real.pi : ℂ) * Complex.I / ((modulus m : ℕ) : ℂ))‖ ≤ 1 := by
    rw [hnorm, div_le_one hMpos]
    have h4 := Real.pi_le_four
    linarith
  have hbound := Complex.norm_exp_sub_one_le hle
  rw [hnorm] at hbound
  have hsplit : defectPhase m + 1
      = -(Complex.exp (-((Real.pi : ℂ) * Complex.I / ((modulus m : ℕ) : ℂ)))
          - 1) := by
    rw [defectPhase_eq]
    ring
  rw [hsplit, norm_neg]
  exact hbound

theorem eventually_defect_lt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in Filter.cofinite, 2 * ‖defectPhase n + 1‖ < ε := by
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * Real.pi / ε)
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnN : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast le_trans (le_max_left N 1) hn
  have hMpos : (0 : ℝ) < ((modulus n : ℕ) : ℝ) := by
    exact_mod_cast modulus_pos n
  have hnM : (n : ℝ) ≤ ((modulus n : ℕ) : ℝ) := by
    have h : n ≤ modulus n := by unfold modulus; omega
    exact_mod_cast h
  have hbound := norm_defectPhase_add_one_le n hn1
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hlt : 4 * Real.pi / ((modulus n : ℕ) : ℝ) < ε := by
    rw [div_lt_iff₀ hMpos]
    have hchain : 4 * Real.pi / ε < ((modulus n : ℕ) : ℝ) :=
      lt_of_lt_of_le hN (le_trans hnN hnM)
    have hmul : (4 * Real.pi / ε) * ε < ((modulus n : ℕ) : ℝ) * ε :=
      mul_lt_mul_of_pos_right hchain hε
    have hcancel : (4 * Real.pi / ε) * ε = 4 * Real.pi := by
      field_simp
    linarith
  have hrw : 2 * (2 * (Real.pi / ((modulus n : ℕ) : ℝ)))
      = 4 * Real.pi / ((modulus n : ℕ) : ℝ) := by
    ring
  calc 2 * ‖defectPhase n + 1‖
      ≤ 2 * (2 * (Real.pi / ((modulus n : ℕ) : ℝ))) := by linarith
    _ = 4 * Real.pi / ((modulus n : ℕ) : ℝ) := hrw
    _ < ε := hlt

/-! ## The coordinate permutations -/

/-- Halving modulo the odd number `2m+3`. -/
def halfOf (m : ℕ) : ZMod (modulus m) := ((m + 2 : ℕ) : ZMod (modulus m))

theorem two_mul_halfOf (m : ℕ) : (2 : ZMod (modulus m)) * halfOf m = 1 := by
  have hnat : 2 * (m + 2) = modulus m + 1 := by unfold modulus; omega
  have hcast : ((2 * (m + 2) : ℕ) : ZMod (modulus m))
      = ((modulus m : ℕ) : ZMod (modulus m)) + 1 := by
    rw [hnat]
    push_cast
    ring
  rw [halfOf]
  calc (2 : ZMod (modulus m)) * ((m + 2 : ℕ) : ZMod (modulus m))
      = ((2 * (m + 2) : ℕ) : ZMod (modulus m)) := by push_cast; ring
    _ = ((modulus m : ℕ) : ZMod (modulus m)) + 1 := hcast
    _ = 1 := by rw [ZMod.natCast_self, zero_add]

/-- The block-dependent offset of the doubling permutation. -/
def offset (m : ℕ) : Fin 2 → ZMod (modulus m) :=
  fun s ↦ if s = 0 then 0 else ((m + 1 : ℕ) : ZMod (modulus m))

@[simp] theorem offset_zero (m : ℕ) : offset m 0 = 0 := by simp [offset]
@[simp] theorem offset_one (m : ℕ) :
    offset m 1 = ((m + 1 : ℕ) : ZMod (modulus m)) := by simp [offset]

theorem phase_offset_zero (m : ℕ) : phase m (offset m 0) = 1 := by
  rw [offset_zero, phase_zero]

theorem phase_offset_one (m : ℕ) : phase m (offset m 1) = defectPhase m := by
  rw [offset_one, defectPhase]

/-- **The defect, as a scalar identity.**  On the `+` block the doubling
relation is exact; on the `-` block it is off by the defect phase. -/
theorem spin_mul_phase_offset (m : ℕ) (s : Fin 2) :
    spin s * phase m (offset m s) - 1
      = (-(2 : ℂ)⁻¹ * (defectPhase m + 1)) * (1 - spin s) := by
  fin_cases s
  · show spin 0 * phase m (offset m 0) - 1
      = (-(2 : ℂ)⁻¹ * (defectPhase m + 1)) * (1 - spin 0)
    rw [spin_zero, phase_offset_zero]
    ring
  · show spin 1 * phase m (offset m 1) - 1
      = (-(2 : ℂ)⁻¹ * (defectPhase m + 1)) * (1 - spin 1)
    rw [spin_one, phase_offset_one]
    ring

/-- The spin flip as a permutation of the coordinates. -/
def flipPerm (m : ℕ) : Equiv.Perm (Fin 2 × ZMod (modulus m)) where
  toFun p := (spinSwap p.1, p.2)
  invFun p := (spinSwap p.1, p.2)
  left_inv := by
    rintro ⟨s, k⟩
    show ((spinSwap (spinSwap s), k) : Fin 2 × ZMod (modulus m)) = (s, k)
    rw [spinSwap_spinSwap]
  right_inv := by
    rintro ⟨s, k⟩
    show ((spinSwap (spinSwap s), k) : Fin 2 × ZMod (modulus m)) = (s, k)
    rw [spinSwap_spinSwap]

@[simp] theorem flipPerm_apply (m : ℕ) (p : Fin 2 × ZMod (modulus m)) :
    flipPerm m p = (spinSwap p.1, p.2) := rfl

theorem flipPerm_mul_self (m : ℕ) : flipPerm m * flipPerm m = 1 := by
  apply Equiv.ext
  rintro ⟨s, k⟩
  show ((spinSwap (spinSwap s), k) : Fin 2 × ZMod (modulus m)) = (s, k)
  rw [spinSwap_spinSwap]

theorem flipPerm_inv (m : ℕ) : (flipPerm m)⁻¹ = flipPerm m :=
  inv_eq_of_mul_eq_one_right (flipPerm_mul_self m)

/-- The doubling permutation: on each spin block the cyclic coordinate is
doubled, with a block-dependent offset. -/
def doublePerm (m : ℕ) : Equiv.Perm (Fin 2 × ZMod (modulus m)) where
  toFun p := (p.1, 2 * p.2 + offset m p.1)
  invFun p := (p.1, (p.2 - offset m p.1) * halfOf m)
  left_inv := by
    rintro ⟨s, k⟩
    show ((s, (2 * k + offset m s - offset m s) * halfOf m) :
      Fin 2 × ZMod (modulus m)) = (s, k)
    have hk : (2 * k + offset m s - offset m s) * halfOf m = k := by
      calc (2 * k + offset m s - offset m s) * halfOf m
          = k * (2 * halfOf m) := by ring
        _ = k := by rw [two_mul_halfOf, mul_one]
    rw [hk]
  right_inv := by
    rintro ⟨s, k⟩
    show ((s, 2 * ((k - offset m s) * halfOf m) + offset m s) :
      Fin 2 × ZMod (modulus m)) = (s, k)
    have hk : 2 * ((k - offset m s) * halfOf m) + offset m s = k := by
      calc 2 * ((k - offset m s) * halfOf m) + offset m s
          = (k - offset m s) * (2 * halfOf m) + offset m s := by ring
        _ = (k - offset m s) + offset m s := by rw [two_mul_halfOf, mul_one]
        _ = k := by ring
    rw [hk]

@[simp] theorem doublePerm_apply (m : ℕ) (p : Fin 2 × ZMod (modulus m)) :
    doublePerm m p = (p.1, 2 * p.2 + offset m p.1) := rfl

/-! ## The four matrices -/

/-- The diagonal of `γ₀`: a spin sign times a cyclic phase. -/
noncomputable def gammaDiag (m : ℕ) : Fin 2 × ZMod (modulus m) → ℂ :=
  fun p ↦ spin p.1 * phase m p.2

/-- The diagonal of `γ₀²`, which does not see the spin coordinate. -/
noncomputable def sqDiag (m : ℕ) : Fin 2 × ZMod (modulus m) → ℂ :=
  fun p ↦ phase m p.2 * phase m p.2

theorem gammaDiag_mul_self (m : ℕ) (p : Fin 2 × ZMod (modulus m)) :
    gammaDiag m p * gammaDiag m p = sqDiag m p := by
  show spin p.1 * phase m p.2 * (spin p.1 * phase m p.2)
    = phase m p.2 * phase m p.2
  calc spin p.1 * phase m p.2 * (spin p.1 * phase m p.2)
      = (spin p.1 * spin p.1) * (phase m p.2 * phase m p.2) := by ring
    _ = phase m p.2 * phase m p.2 := by rw [spin_mul_self, one_mul]

theorem gammaDiag_mul_conj (m : ℕ) (p : Fin 2 × ZMod (modulus m)) :
    gammaDiag m p * (starRingEnd ℂ) (gammaDiag m p) = 1 := by
  show spin p.1 * phase m p.2
    * (starRingEnd ℂ) (spin p.1 * phase m p.2) = 1
  rw [map_mul, conj_spin]
  calc spin p.1 * phase m p.2 * (spin p.1 * (starRingEnd ℂ) (phase m p.2))
      = (spin p.1 * spin p.1)
        * (phase m p.2 * (starRingEnd ℂ) (phase m p.2)) := by ring
    _ = 1 := by rw [spin_mul_self, phase_mul_conj, one_mul]

theorem gammaDiag_mul_conj_flip (m : ℕ) (p : Fin 2 × ZMod (modulus m)) :
    gammaDiag m p * (starRingEnd ℂ) (gammaDiag m (flipPerm m p)) = -1 := by
  show spin p.1 * phase m p.2
    * (starRingEnd ℂ) (spin (spinSwap p.1) * phase m p.2) = -1
  rw [map_mul, conj_spin, spin_spinSwap]
  calc spin p.1 * phase m p.2
        * (-spin p.1 * (starRingEnd ℂ) (phase m p.2))
      = -((spin p.1 * spin p.1)
        * (phase m p.2 * (starRingEnd ℂ) (phase m p.2))) := by ring
    _ = -1 := by rw [spin_mul_self, phase_mul_conj, one_mul]

theorem normSq_gammaDiag (m : ℕ) (p : Fin 2 × ZMod (modulus m)) :
    Complex.normSq (gammaDiag m p) = 1 := by
  show Complex.normSq (spin p.1 * phase m p.2) = 1
  rw [Complex.normSq_mul, normSq_spin, normSq_phase, one_mul]

/-- `γ₀`: the diagonal unitary whose spectrum is the set of `2M`-th roots of
unity, each once. -/
noncomputable def gammaMatrix (m : ℕ) : Matrix (site m) (site m) ℂ :=
  monomialMatrix (site m) (gammaDiag m) 1

/-- `t`: the coordinate permutation doubling the cyclic coordinate. -/
noncomputable def stableMatrix (m : ℕ) : Matrix (site m) (site m) ℂ :=
  monomialMatrix (site m) (fun _ ↦ 1) (doublePerm m)

/-- The spin flip. -/
noncomputable def flipMatrix (m : ℕ) : Matrix (site m) (site m) ℂ :=
  monomialMatrix (site m) (fun _ ↦ 1) (flipPerm m)

/-- The spin sign. -/
noncomputable def spinMatrix (m : ℕ) : Matrix (site m) (site m) ℂ :=
  monomialMatrix (site m) (fun p ↦ spin p.1) 1

/-- The one irrational constant: the `45°` weight. -/
noncomputable def half2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

theorem half2_mul_half2 : half2 * half2 = (2 : ℂ)⁻¹ := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = (2 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [half2, ← mul_inv, h2]

theorem conj_half2 : (starRingEnd ℂ) half2 = half2 := by
  rw [half2, map_inv₀, Complex.conj_ofReal]

/-- The lamp `D`: an equal-weight combination of the spin flip and the spin
sign, hence a self-adjoint unitary at `45°` to its own conjugate by the spin
sign. -/
noncomputable def lampBase (m : ℕ) : Matrix (site m) (site m) ℂ :=
  half2 • (flipMatrix m + spinMatrix m)

/-! ## Products of the spin matrices -/

theorem flip_mul_flip (m : ℕ) : flipMatrix m * flipMatrix m = 1 := by
  rw [← monomialMatrix_one (site m), flipMatrix]
  exact monomialMatrix_mul_eq (site m) _ _ _ _ _ _ (fun p ↦ one_mul 1)
    (flipPerm_mul_self m)

theorem spin_mul_spin (m : ℕ) : spinMatrix m * spinMatrix m = 1 := by
  rw [← monomialMatrix_one (site m), spinMatrix]
  exact monomialMatrix_mul_eq (site m) _ _ _ _ _ _
    (fun p ↦ by
      show spin p.1 * spin ((1 : Equiv.Perm (site m)) p).1 = 1
      rw [Equiv.Perm.one_apply]
      exact spin_mul_self p.1)
    (one_mul 1)

theorem flip_mul_spin (m : ℕ) :
    flipMatrix m * spinMatrix m
      = monomialMatrix (site m) (fun p ↦ -spin p.1) (flipPerm m) := by
  rw [flipMatrix, spinMatrix]
  exact monomialMatrix_mul_eq (site m) _ _ _ _ _ _
    (fun p ↦ by
      show (1 : ℂ) * spin (spinSwap p.1) = -spin p.1
      rw [one_mul, spin_spinSwap])
    (one_mul _)

theorem spin_mul_flip (m : ℕ) :
    spinMatrix m * flipMatrix m
      = monomialMatrix (site m) (fun p ↦ spin p.1) (flipPerm m) := by
  rw [flipMatrix, spinMatrix]
  exact monomialMatrix_mul_eq (site m) _ _ _ _ _ _
    (fun p ↦ by
      show spin p.1 * (1 : ℂ) = spin p.1
      rw [mul_one])
    (mul_one _)

theorem spin_flip_anticomm (m : ℕ) :
    spinMatrix m * flipMatrix m = -(flipMatrix m * spinMatrix m) := by
  rw [flip_mul_spin, spin_mul_flip, monomialMatrix_neg]
  exact monomialMatrix_congr (site m) (fun p ↦ (neg_neg (spin p.1)).symm) rfl

theorem flipSpin_sq (m : ℕ) :
    (flipMatrix m * spinMatrix m) * (flipMatrix m * spinMatrix m) = -1 := by
  rw [flip_mul_spin, ← monomialMatrix_negOne (site m)]
  refine monomialMatrix_mul_eq (site m) _ _ _ _ _ _ (fun p ↦ ?_)
    (flipPerm_mul_self m)
  show -spin p.1 * -spin (spinSwap p.1) = -1
  rw [spin_spinSwap]
  calc -spin p.1 * - -spin p.1 = -(spin p.1 * spin p.1) := by ring
    _ = -1 := by rw [spin_mul_self]

/-! ## Unitarity -/

theorem gammaMatrix_mem (m : ℕ) :
    gammaMatrix m ∈ Matrix.unitaryGroup (site m) ℂ :=
  monomialMatrix_mem_unitaryGroup (site m) (fun p ↦ normSq_gammaDiag m p) 1

theorem stableMatrix_mem (m : ℕ) :
    stableMatrix m ∈ Matrix.unitaryGroup (site m) ℂ :=
  monomialMatrix_mem_unitaryGroup (site m) (fun _ ↦ by simp) (doublePerm m)

theorem flipMatrix_mem (m : ℕ) :
    flipMatrix m ∈ Matrix.unitaryGroup (site m) ℂ :=
  monomialMatrix_mem_unitaryGroup (site m) (fun _ ↦ by simp) (flipPerm m)

theorem spinMatrix_mem (m : ℕ) :
    spinMatrix m ∈ Matrix.unitaryGroup (site m) ℂ :=
  monomialMatrix_mem_unitaryGroup (site m) (fun p ↦ normSq_spin p.1) 1

theorem flipMatrix_conjTranspose (m : ℕ) : (flipMatrix m)ᴴ = flipMatrix m := by
  rw [flipMatrix]
  exact monomialMatrix_conjTranspose_eq (site m) _ _ _ _
    (fun p ↦ map_one _) (flipPerm_inv m)

theorem spinMatrix_conjTranspose (m : ℕ) : (spinMatrix m)ᴴ = spinMatrix m := by
  rw [spinMatrix]
  refine monomialMatrix_conjTranspose_eq (site m) _ _ _ _ (fun p ↦ ?_) inv_one
  show (starRingEnd ℂ) (spin ((1 : Equiv.Perm (site m))⁻¹ p).1) = spin p.1
  rw [inv_one, Equiv.Perm.one_apply, conj_spin]

theorem lampBase_conjTranspose (m : ℕ) : (lampBase m)ᴴ = lampBase m := by
  rw [lampBase, conjTranspose_smul_complex, Matrix.conjTranspose_add,
    flipMatrix_conjTranspose, spinMatrix_conjTranspose, conj_half2]

theorem lampBase_mul_self (m : ℕ) : lampBase m * lampBase m = 1 := by
  have hexp : (flipMatrix m + spinMatrix m) * (flipMatrix m + spinMatrix m)
      = (2 : ℂ) • (1 : Matrix (site m) (site m) ℂ) := by
    have hmul : (flipMatrix m + spinMatrix m) * (flipMatrix m + spinMatrix m)
        = flipMatrix m * flipMatrix m + spinMatrix m * spinMatrix m
          + (flipMatrix m * spinMatrix m + spinMatrix m * flipMatrix m) := by
      noncomm_ring
    rw [hmul, flip_mul_flip, spin_mul_spin, spin_flip_anticomm,
      add_neg_cancel, add_zero, two_smul]
  rw [lampBase, Matrix.smul_mul, Matrix.mul_smul, hexp, smul_smul, smul_smul,
    half2_mul_half2, show ((2 : ℂ)⁻¹ * 2 = 1) from by norm_num, one_smul]

theorem lampBase_mem (m : ℕ) :
    lampBase m ∈ Matrix.unitaryGroup (site m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    lampBase_conjTranspose]
  exact lampBase_mul_self m

theorem negOne_mem (m : ℕ) :
    (-1 : Matrix (site m) (site m) ℂ) ∈ Matrix.unitaryGroup (site m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_neg, star_one, neg_mul_neg, one_mul]

/-! ## The exact identities -/

theorem gammaMatrix_conjTranspose (m : ℕ) :
    (gammaMatrix m)ᴴ
      = monomialMatrix (site m)
        (fun p ↦ (starRingEnd ℂ) (gammaDiag m p)) 1 := by
  rw [gammaMatrix]
  refine monomialMatrix_conjTranspose_eq (site m) _ _ _ _ (fun p ↦ ?_) inv_one
  show (starRingEnd ℂ) (gammaDiag m ((1 : Equiv.Perm (site m))⁻¹ p))
    = (starRingEnd ℂ) (gammaDiag m p)
  rw [inv_one, Equiv.Perm.one_apply]

theorem gammaMatrix_mul_self (m : ℕ) :
    gammaMatrix m * gammaMatrix m = monomialMatrix (site m) (sqDiag m) 1 := by
  rw [gammaMatrix]
  refine monomialMatrix_mul_eq (site m) _ _ _ _ _ _ (fun p ↦ ?_) (one_mul 1)
  show gammaDiag m p * gammaDiag m ((1 : Equiv.Perm (site m)) p) = sqDiag m p
  rw [Equiv.Perm.one_apply]
  exact gammaDiag_mul_self m p

theorem gammaSq_mem (m : ℕ) :
    gammaMatrix m * gammaMatrix m ∈ Matrix.unitaryGroup (site m) ℂ :=
  Submonoid.mul_mem _ (gammaMatrix_mem m) (gammaMatrix_mem m)

/-- **The lamp commutes with `γ₀²` exactly.**  The square of `γ₀` does not see
the spin coordinate, and the lamp acts on the spin coordinate alone.  This is
the identity that keeps the lamp relation as accurate as the doubling
relation. -/
theorem lampBase_comm_gammaSq (m : ℕ) :
    lampBase m * (gammaMatrix m * gammaMatrix m)
      = (gammaMatrix m * gammaMatrix m) * lampBase m := by
  have hflip : flipMatrix m * (gammaMatrix m * gammaMatrix m)
      = (gammaMatrix m * gammaMatrix m) * flipMatrix m := by
    rw [gammaMatrix_mul_self, flipMatrix]
    have hleft : monomialMatrix (site m) (fun _ ↦ (1 : ℂ)) (flipPerm m)
        * monomialMatrix (site m) (sqDiag m) 1
        = monomialMatrix (site m) (fun p ↦ sqDiag m p) (flipPerm m) := by
      refine monomialMatrix_mul_eq (site m) _ _ _ _ _ _ (fun p ↦ ?_)
        (one_mul _)
      show (1 : ℂ) * sqDiag m p = sqDiag m p
      rw [one_mul]
    have hright : monomialMatrix (site m) (sqDiag m) 1
        * monomialMatrix (site m) (fun _ ↦ (1 : ℂ)) (flipPerm m)
        = monomialMatrix (site m) (fun p ↦ sqDiag m p) (flipPerm m) := by
      refine monomialMatrix_mul_eq (site m) _ _ _ _ _ _ (fun p ↦ ?_)
        (mul_one _)
      show sqDiag m p * (1 : ℂ) = sqDiag m p
      rw [mul_one]
    rw [hleft, hright]
  have hspin : spinMatrix m * (gammaMatrix m * gammaMatrix m)
      = (gammaMatrix m * gammaMatrix m) * spinMatrix m := by
    rw [gammaMatrix_mul_self, spinMatrix]
    have hleft : monomialMatrix (site m) (fun p ↦ spin p.1) 1
        * monomialMatrix (site m) (sqDiag m) 1
        = monomialMatrix (site m) (fun p ↦ spin p.1 * sqDiag m p) 1 := by
      refine monomialMatrix_mul_eq (site m) _ _ _ _ _ _ (fun p ↦ ?_) (one_mul 1)
      show spin p.1 * sqDiag m ((1 : Equiv.Perm (site m)) p)
        = spin p.1 * sqDiag m p
      rw [Equiv.Perm.one_apply]
    have hright : monomialMatrix (site m) (sqDiag m) 1
        * monomialMatrix (site m) (fun p ↦ spin p.1) 1
        = monomialMatrix (site m) (fun p ↦ spin p.1 * sqDiag m p) 1 := by
      refine monomialMatrix_mul_eq (site m) _ _ _ _ _ _ (fun p ↦ ?_) (one_mul 1)
      show sqDiag m p * spin ((1 : Equiv.Perm (site m)) p).1
        = spin p.1 * sqDiag m p
      rw [Equiv.Perm.one_apply, mul_comm]
    rw [hleft, hright]
  have hexpand : lampBase m * (gammaMatrix m * gammaMatrix m)
      = half2 • (flipMatrix m * (gammaMatrix m * gammaMatrix m)
        + spinMatrix m * (gammaMatrix m * gammaMatrix m)) := by
    rw [lampBase, Matrix.smul_mul, Matrix.add_mul]
  have hexpand' : (gammaMatrix m * gammaMatrix m) * lampBase m
      = half2 • ((gammaMatrix m * gammaMatrix m) * flipMatrix m
        + (gammaMatrix m * gammaMatrix m) * spinMatrix m) := by
    rw [lampBase, Matrix.mul_smul, Matrix.mul_add]
  rw [hexpand, hexpand', hflip, hspin]

/-- The conjugate of the lamp by `γ₀`: the spin flip changes sign, the spin
sign does not. -/
theorem gamma_conj_lampBase (m : ℕ) :
    gammaMatrix m * lampBase m * (gammaMatrix m)ᴴ
      = half2 • (spinMatrix m - flipMatrix m) := by
  have hflip : gammaMatrix m * flipMatrix m * (gammaMatrix m)ᴴ
      = -flipMatrix m := by
    have hstep : gammaMatrix m * flipMatrix m
        = monomialMatrix (site m) (gammaDiag m) (flipPerm m) := by
      rw [gammaMatrix, flipMatrix]
      -- `hperm : σ' * σ = τ` with `σ = 1` (the diagonal `γ₀`) and
      -- `σ' = flipPerm m`, so the identity needed is `flipPerm m * 1`, not
      -- `1 * flipPerm m`.
      refine monomialMatrix_mul_eq (site m) _ _ _ _ _ _ (fun p ↦ ?_) (mul_one _)
      show gammaDiag m p * (1 : ℂ) = gammaDiag m p
      rw [mul_one]
    rw [hstep, gammaMatrix_conjTranspose, flipMatrix, monomialMatrix_neg]
    refine monomialMatrix_mul_eq (site m) _ _ _ _ _ _ (fun p ↦ ?_) (one_mul _)
    show gammaDiag m p * (starRingEnd ℂ) (gammaDiag m ((flipPerm m) p))
      = -(1 : ℂ)
    exact gammaDiag_mul_conj_flip m p
  have hspin : gammaMatrix m * spinMatrix m * (gammaMatrix m)ᴴ
      = spinMatrix m := by
    have hstep : gammaMatrix m * spinMatrix m
        = monomialMatrix (site m) (fun p ↦ gammaDiag m p * spin p.1) 1 := by
      rw [gammaMatrix, spinMatrix]
      refine monomialMatrix_mul_eq (site m) _ _ _ _ _ _ (fun p ↦ ?_) (one_mul 1)
      show gammaDiag m p * spin ((1 : Equiv.Perm (site m)) p).1
        = gammaDiag m p * spin p.1
      rw [Equiv.Perm.one_apply]
    rw [hstep, gammaMatrix_conjTranspose, spinMatrix]
    refine monomialMatrix_mul_eq (site m) _ _ _ _ _ _ (fun p ↦ ?_) (one_mul 1)
    show gammaDiag m p * spin p.1
        * (starRingEnd ℂ) (gammaDiag m ((1 : Equiv.Perm (site m)) p))
      = spin p.1
    rw [Equiv.Perm.one_apply]
    calc gammaDiag m p * spin p.1 * (starRingEnd ℂ) (gammaDiag m p)
        = spin p.1 * (gammaDiag m p * (starRingEnd ℂ) (gammaDiag m p)) := by
          ring
      _ = spin p.1 := by rw [gammaDiag_mul_conj, mul_one]
  have hexpand : gammaMatrix m * lampBase m * (gammaMatrix m)ᴴ
      = half2 • (gammaMatrix m * flipMatrix m * (gammaMatrix m)ᴴ
        + gammaMatrix m * spinMatrix m * (gammaMatrix m)ᴴ) := by
    rw [lampBase, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
      Matrix.add_mul]
  rw [hexpand, hflip, hspin]
  congr 1
  abel

/-- **The marked word is the scalar `-1`.**  This is the `45°` computation: the
lamp and its conjugate by the spin sign anticommute. -/
theorem lampBase_mul_conj (m : ℕ) :
    lampBase m * (gammaMatrix m * lampBase m * (gammaMatrix m)ᴴ)
      = flipMatrix m * spinMatrix m := by
  have hexp : (flipMatrix m + spinMatrix m) * (spinMatrix m - flipMatrix m)
      = (2 : ℂ) • (flipMatrix m * spinMatrix m) := by
    have hmul : (flipMatrix m + spinMatrix m) * (spinMatrix m - flipMatrix m)
        = flipMatrix m * spinMatrix m - spinMatrix m * flipMatrix m
          + (spinMatrix m * spinMatrix m - flipMatrix m * flipMatrix m) := by
      noncomm_ring
    rw [hmul, flip_mul_flip, spin_mul_spin, sub_self, add_zero,
      spin_flip_anticomm, sub_neg_eq_add, two_smul]
  rw [gamma_conj_lampBase, lampBase, Matrix.smul_mul, Matrix.mul_smul, hexp,
    smul_smul, smul_smul, half2_mul_half2,
    show ((2 : ℂ)⁻¹ * 2 = 1) from by norm_num, one_smul]

/-! ## The defect estimate -/

theorem gammaDiag_double (m : ℕ) (p : Fin 2 × ZMod (modulus m)) :
    gammaDiag m (doublePerm m p)
      = spin p.1 * (sqDiag m p * phase m (offset m p.1)) := by
  show spin p.1 * phase m (2 * p.2 + offset m p.1)
    = spin p.1 * (phase m p.2 * phase m p.2 * phase m (offset m p.1))
  rw [phase_add, phase_two_mul]

theorem defect_scalar (m : ℕ) (p : Fin 2 × ZMod (modulus m)) :
    gammaDiag m (doublePerm m p) - sqDiag m p
      = (-(2 : ℂ)⁻¹ * (defectPhase m + 1))
        * (sqDiag m p - spin p.1 * sqDiag m p) := by
  rw [gammaDiag_double]
  have h := spin_mul_phase_offset m p.1
  have hfactor : spin p.1 * (sqDiag m p * phase m (offset m p.1)) - sqDiag m p
      = sqDiag m p * (spin p.1 * phase m (offset m p.1) - 1) := by ring
  rw [hfactor, h]
  ring

/-- The doubling relation, computed exactly: it is the diagonal matrix of the
transported phases. -/
theorem stable_conj_gamma (m : ℕ) :
    stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
      = monomialMatrix (site m)
        (fun p ↦ gammaDiag m (doublePerm m p)) 1 := by
  have hT : (stableMatrix m)ᴴ
      = monomialMatrix (site m) (fun _ ↦ 1) (doublePerm m)⁻¹ := by
    rw [stableMatrix]
    exact monomialMatrix_conjTranspose_eq (site m) _ _ _ _
      (fun p ↦ map_one _) rfl
  have hstep : stableMatrix m * gammaMatrix m
      = monomialMatrix (site m) (fun p ↦ gammaDiag m (doublePerm m p))
        (doublePerm m) := by
    rw [stableMatrix, gammaMatrix]
    refine monomialMatrix_mul_eq (site m) _ _ _ _ _ _ (fun p ↦ ?_) (one_mul _)
    show (1 : ℂ) * gammaDiag m ((doublePerm m) p)
      = gammaDiag m (doublePerm m p)
    rw [one_mul]
  rw [hstep, hT]
  refine monomialMatrix_mul_eq (site m) _ _ _ _ _ _ (fun p ↦ ?_) ?_
  · show gammaDiag m (doublePerm m p) * (1 : ℂ)
      = gammaDiag m (doublePerm m p)
    rw [mul_one]
  · exact inv_mul_cancel (doublePerm m)

theorem conj_sub_sq (m : ℕ) :
    stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
        - gammaMatrix m * gammaMatrix m
      = (-(2 : ℂ)⁻¹ * (defectPhase m + 1)) •
        (gammaMatrix m * gammaMatrix m
          - spinMatrix m * (gammaMatrix m * gammaMatrix m)) := by
  have hS : spinMatrix m * (gammaMatrix m * gammaMatrix m)
      = monomialMatrix (site m) (fun p ↦ spin p.1 * sqDiag m p) 1 := by
    rw [gammaMatrix_mul_self, spinMatrix]
    refine monomialMatrix_mul_eq (site m) _ _ _ _ _ _ (fun p ↦ ?_) (one_mul 1)
    show spin p.1 * sqDiag m ((1 : Equiv.Perm (site m)) p)
      = spin p.1 * sqDiag m p
    rw [Equiv.Perm.one_apply]
  have hright : gammaMatrix m * gammaMatrix m
      - spinMatrix m * (gammaMatrix m * gammaMatrix m)
      = monomialMatrix (site m)
        (fun p ↦ sqDiag m p - spin p.1 * sqDiag m p) 1 := by
    rw [hS, gammaMatrix_mul_self]
    exact monomialMatrix_sub_eq (site m) _ _ _ _ (fun p ↦ rfl)
  have hleft : stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
      - gammaMatrix m * gammaMatrix m
      = monomialMatrix (site m)
        (fun p ↦ gammaDiag m (doublePerm m p) - sqDiag m p) 1 := by
    rw [stable_conj_gamma, gammaMatrix_mul_self]
    exact monomialMatrix_sub_eq (site m) _ _ _ _ (fun p ↦ rfl)
  rw [hleft, hright]
  exact (monomialMatrix_smul_eq (site m) _ _ _ _
    (fun p ↦ (defect_scalar m p).symm)).symm

theorem norm_conj_sub_sq_le (m : ℕ) :
    ‖stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
        - gammaMatrix m * gammaMatrix m‖ ≤ ‖defectPhase m + 1‖ := by
  have hsq : ‖gammaMatrix m * gammaMatrix m‖ = 1 :=
    CStarRing.norm_of_mem_unitary (gammaSq_mem m)
  have hspinsq : ‖spinMatrix m * (gammaMatrix m * gammaMatrix m)‖ = 1 :=
    CStarRing.norm_of_mem_unitary
      (Submonoid.mul_mem _ (spinMatrix_mem m) (gammaSq_mem m))
  have hscalar : ‖(-(2 : ℂ)⁻¹ * (defectPhase m + 1))‖
      = ‖defectPhase m + 1‖ / 2 := by
    rw [norm_mul, norm_neg, norm_inv, Complex.norm_ofNat]
    ring
  have hdiff : ‖gammaMatrix m * gammaMatrix m
      - spinMatrix m * (gammaMatrix m * gammaMatrix m)‖ ≤ 2 := by
    calc ‖gammaMatrix m * gammaMatrix m
        - spinMatrix m * (gammaMatrix m * gammaMatrix m)‖
        ≤ ‖gammaMatrix m * gammaMatrix m‖
          + ‖spinMatrix m * (gammaMatrix m * gammaMatrix m)‖ := norm_sub_le _ _
      _ = 2 := by rw [hsq, hspinsq]; norm_num
  have hnn : 0 ≤ ‖defectPhase m + 1‖ / 2 := by positivity
  rw [conj_sub_sq, norm_smul, hscalar]
  calc ‖defectPhase m + 1‖ / 2 * ‖gammaMatrix m * gammaMatrix m
        - spinMatrix m * (gammaMatrix m * gammaMatrix m)‖
      ≤ ‖defectPhase m + 1‖ / 2 * 2 := mul_le_mul_of_nonneg_left hdiff hnn
    _ = ‖defectPhase m + 1‖ := by ring

/-! ## The unitaries of the model -/

@[simp] theorem coe_mulU {Y : FiniteModel} (u v : Matrix.unitaryGroup Y ℂ) :
    ((u * v : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)
      = (u : Matrix Y Y ℂ) * (v : Matrix Y Y ℂ) := rfl

theorem coe_invU {Y : FiniteModel} (u : Matrix.unitaryGroup Y ℂ) :
    ((u⁻¹ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ)
      = (u : Matrix Y Y ℂ)ᴴ := by
  rw [← Matrix.star_eq_conjTranspose]
  rfl

/-- `γ₀` in the `m`-th model. -/
noncomputable def gammaU (m : ℕ) : Matrix.unitaryGroup (site m) ℂ :=
  ⟨gammaMatrix m, gammaMatrix_mem m⟩

/-- `t` in the `m`-th model. -/
noncomputable def stableU (m : ℕ) : Matrix.unitaryGroup (site m) ℂ :=
  ⟨stableMatrix m, stableMatrix_mem m⟩

/-- The lamp before transport. -/
noncomputable def baseU (m : ℕ) : Matrix.unitaryGroup (site m) ℂ :=
  ⟨lampBase m, lampBase_mem m⟩

/-- `c` in the `m`-th model: the lamp transported by `t`. -/
noncomputable def lampU (m : ℕ) : Matrix.unitaryGroup (site m) ℂ :=
  (stableU m)⁻¹ * baseU m * stableU m

/-- The value of the marked word in every model. -/
noncomputable def negOneU (m : ℕ) : Matrix.unitaryGroup (site m) ℂ :=
  ⟨-1, negOne_mem m⟩

@[simp] theorem coe_gammaU (m : ℕ) :
    ((gammaU m : Matrix.unitaryGroup (site m) ℂ) :
      Matrix (site m) (site m) ℂ) = gammaMatrix m := rfl

@[simp] theorem coe_stableU (m : ℕ) :
    ((stableU m : Matrix.unitaryGroup (site m) ℂ) :
      Matrix (site m) (site m) ℂ) = stableMatrix m := rfl

@[simp] theorem coe_baseU (m : ℕ) :
    ((baseU m : Matrix.unitaryGroup (site m) ℂ) :
      Matrix (site m) (site m) ℂ) = lampBase m := rfl

@[simp] theorem coe_negOneU (m : ℕ) :
    ((negOneU m : Matrix.unitaryGroup (site m) ℂ) :
      Matrix (site m) (site m) ℂ) = -1 := rfl

theorem baseU_mul_self (m : ℕ) : baseU m * baseU m = 1 := by
  apply Subtype.ext
  show lampBase m * lampBase m = 1
  exact lampBase_mul_self m

theorem baseU_inv (m : ℕ) : (baseU m)⁻¹ = baseU m :=
  inv_eq_of_mul_eq_one_right (baseU_mul_self m)

theorem lampU_mul_self (m : ℕ) : lampU m * lampU m = 1 := by
  rw [lampU]
  calc (stableU m)⁻¹ * baseU m * stableU m
        * ((stableU m)⁻¹ * baseU m * stableU m)
      = (stableU m)⁻¹ * (baseU m * baseU m) * stableU m := by group
    _ = 1 := by rw [baseU_mul_self]; group

theorem negOneU_mul_self (m : ℕ) : negOneU m * negOneU m = 1 := by
  apply Subtype.ext
  show (-1 : Matrix (site m) (site m) ℂ) * (-1 : Matrix (site m) (site m) ℂ)
    = (1 : Matrix (site m) (site m) ℂ)
  rw [neg_mul_neg, one_mul]

theorem negOneU_commute (m : ℕ) (u : Matrix.unitaryGroup (site m) ℂ) :
    Commute (negOneU m) u := by
  show negOneU m * u = u * negOneU m
  apply Subtype.ext
  show (-1 : Matrix (site m) (site m) ℂ) * (u : Matrix (site m) (site m) ℂ)
    = (u : Matrix (site m) (site m) ℂ) * (-1 : Matrix (site m) (site m) ℂ)
  rw [neg_one_mul, mul_neg_one]

/-- **The marked word of `E_BS` evaluates to `-1` in every model.** -/
theorem marked_value (m : ℕ) :
    markedCompressionWord (stableU m) (gammaU m) (lampU m) = negOneU m := by
  have hconj : stableU m * lampU m * (stableU m)⁻¹ = baseU m := by
    rw [lampU]
    group
  have hB' : (gammaU m * baseU m * (gammaU m)⁻¹)
      * (gammaU m * baseU m * (gammaU m)⁻¹) = 1 := by
    calc (gammaU m * baseU m * (gammaU m)⁻¹)
          * (gammaU m * baseU m * (gammaU m)⁻¹)
        = gammaU m * (baseU m * baseU m) * (gammaU m)⁻¹ := by group
      _ = 1 := by rw [baseU_mul_self m]; group
  rw [markedCompressionWord, hconj, commutatorElement_def, baseU_inv,
    inv_eq_of_mul_eq_one_right hB']
  apply Subtype.ext
  have hcoe : ((baseU m * (gammaU m * baseU m * (gammaU m)⁻¹) * baseU m
        * (gammaU m * baseU m * (gammaU m)⁻¹) :
        Matrix.unitaryGroup (site m) ℂ) : Matrix (site m) (site m) ℂ)
      = (lampBase m * (gammaMatrix m * lampBase m * (gammaMatrix m)ᴴ))
        * (lampBase m * (gammaMatrix m * lampBase m * (gammaMatrix m)ᴴ)) := by
    -- Mathlib's global simp set already pushes the submonoid coercion through
    -- products and inverses, so `coe_mulU` and friends are redundant here and
    -- `noncomm_ring` (which runs `simp`) does the whole step.
    noncomm_ring
  rw [hcoe, lampBase_mul_conj, flipSpin_sq, coe_negOneU]

/-! ## The two approximate relators, fibrewise -/

/-- The operator-norm length of a commutator of unitaries is the commutator
defect of the underlying matrices. -/
theorem opLength_commutator (Y : FiniteModel) (u v : Matrix.unitaryGroup Y ℂ) :
    opLength Y ⁅u, v⁆
      = ‖(u : Matrix Y Y ℂ) * (v : Matrix Y Y ℂ)
        - (v : Matrix Y Y ℂ) * (u : Matrix Y Y ℂ)‖ := by
  have hu : (u : Matrix Y Y ℂ) * (u : Matrix Y Y ℂ)ᴴ = 1 := by
    have h := u.2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have hv : (v : Matrix Y Y ℂ) * (v : Matrix Y Y ℂ)ᴴ = 1 := by
    have h := v.2
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have hvu : ((v : Matrix Y Y ℂ) * (u : Matrix Y Y ℂ))
      ∈ Matrix.unitaryGroup Y ℂ := Submonoid.mul_mem _ v.2 u.2
  have hstar : (((v : Matrix Y Y ℂ) * (u : Matrix Y Y ℂ))ᴴ)
      ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hvu
  have hsplit : ((⁅u, v⁆ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) - 1
      = ((u : Matrix Y Y ℂ) * (v : Matrix Y Y ℂ)
          - (v : Matrix Y Y ℂ) * (u : Matrix Y Y ℂ))
        * ((v : Matrix Y Y ℂ) * (u : Matrix Y Y ℂ))ᴴ := by
    rw [commutatorElement_def]
    simp only [coe_mulU, coe_invU]
    rw [Matrix.conjTranspose_mul, Matrix.sub_mul]
    have hcancel : (v : Matrix Y Y ℂ) * (u : Matrix Y Y ℂ)
        * ((u : Matrix Y Y ℂ)ᴴ * (v : Matrix Y Y ℂ)ᴴ) = 1 := by
      calc (v : Matrix Y Y ℂ) * (u : Matrix Y Y ℂ)
            * ((u : Matrix Y Y ℂ)ᴴ * (v : Matrix Y Y ℂ)ᴴ)
          = (v : Matrix Y Y ℂ)
            * ((u : Matrix Y Y ℂ) * (u : Matrix Y Y ℂ)ᴴ)
            * (v : Matrix Y Y ℂ)ᴴ := by noncomm_ring
        _ = 1 := by rw [hu, Matrix.mul_one, hv]
    rw [hcancel]
    noncomm_ring
  rw [opLength, hsplit, CStarRing.norm_mul_mem_unitary _ hstar]

theorem opLength_stable_le (m : ℕ) :
    opLength (site m)
        (stableU m * gammaU m * (stableU m)⁻¹ * (gammaU m * gammaU m)⁻¹)
      ≤ ‖defectPhase m + 1‖ := by
  have hGG : (gammaMatrix m * gammaMatrix m)
      * (gammaMatrix m * gammaMatrix m)ᴴ = 1 := by
    have h := gammaSq_mem m
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have hstar : ((gammaMatrix m * gammaMatrix m)ᴴ)
      ∈ Matrix.unitaryGroup (site m) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem (gammaSq_mem m)
  have hcoe : ((stableU m * gammaU m * (stableU m)⁻¹
        * (gammaU m * gammaU m)⁻¹ : Matrix.unitaryGroup (site m) ℂ) :
        Matrix (site m) (site m) ℂ) - 1
      = (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
          - gammaMatrix m * gammaMatrix m)
        * (gammaMatrix m * gammaMatrix m)ᴴ := by
    -- every `coe_*U` lemma of this file is `rfl`, so the coercion can be
    -- discharged by `show` rather than by a `simp only` whose arguments the
    -- global coercion lemmas make redundant
    show stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ *
        (gammaMatrix m * gammaMatrix m)ᴴ - 1
      = (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
          - gammaMatrix m * gammaMatrix m)
        * (gammaMatrix m * gammaMatrix m)ᴴ
    rw [Matrix.sub_mul, hGG]
  rw [opLength, hcoe, CStarRing.norm_mul_mem_unitary _ hstar]
  exact norm_conj_sub_sq_le m

theorem opLength_lampGamma_le (m : ℕ) :
    opLength (site m) (⁅lampU m, gammaU m⁆) ≤ 2 * ‖defectPhase m + 1‖ := by
  have hTT : (stableMatrix m)ᴴ * stableMatrix m = 1 := by
    have h := Unitary.star_mul_self_of_mem (stableMatrix_mem m)
    rwa [Matrix.star_eq_conjTranspose] at h
  have hTstar : ((stableMatrix m)ᴴ) ∈ Matrix.unitaryGroup (site m) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem (stableMatrix_mem m)
  have hlamp : ((lampU m : Matrix.unitaryGroup (site m) ℂ) :
      Matrix (site m) (site m) ℂ)
      = (stableMatrix m)ᴴ * lampBase m * stableMatrix m := by
    -- `lampU` is a product of the model unitaries and every coercion lemma
    -- above is `rfl`, so this is definitional
    rfl
  rw [opLength_commutator, hlamp, coe_gammaU]
  -- transport the commutator through `t`
  have hsplit : ((stableMatrix m)ᴴ * lampBase m * stableMatrix m)
        * gammaMatrix m
      - gammaMatrix m * ((stableMatrix m)ᴴ * lampBase m * stableMatrix m)
      = (stableMatrix m)ᴴ
        * (lampBase m * (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ)
          - (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ) * lampBase m)
        * stableMatrix m := by
    have e1 : (stableMatrix m)ᴴ
        * (lampBase m * (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ))
        * stableMatrix m
        = ((stableMatrix m)ᴴ * lampBase m * stableMatrix m)
          * gammaMatrix m := by
      calc (stableMatrix m)ᴴ
            * (lampBase m
              * (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ))
            * stableMatrix m
          = (stableMatrix m)ᴴ * lampBase m * stableMatrix m * gammaMatrix m
            * ((stableMatrix m)ᴴ * stableMatrix m) := by noncomm_ring
        _ = ((stableMatrix m)ᴴ * lampBase m * stableMatrix m)
            * gammaMatrix m := by rw [hTT, Matrix.mul_one]
    have e2 : (stableMatrix m)ᴴ
        * ((stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ) * lampBase m)
        * stableMatrix m
        = gammaMatrix m
          * ((stableMatrix m)ᴴ * lampBase m * stableMatrix m) := by
      calc (stableMatrix m)ᴴ
            * ((stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ)
              * lampBase m)
            * stableMatrix m
          = ((stableMatrix m)ᴴ * stableMatrix m) * gammaMatrix m
            * ((stableMatrix m)ᴴ * lampBase m * stableMatrix m) := by
            noncomm_ring
        _ = gammaMatrix m
            * ((stableMatrix m)ᴴ * lampBase m * stableMatrix m) := by
            rw [hTT, Matrix.one_mul]
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  rw [hsplit, CStarRing.norm_mul_mem_unitary _ (stableMatrix_mem m),
    CStarRing.norm_mem_unitary_mul _ hTstar]
  -- only the doubling defect survives, because the lamp commutes with `γ₀²`
  have hcomm : lampBase m * (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ)
      - (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ) * lampBase m
      = lampBase m * (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
          - gammaMatrix m * gammaMatrix m)
        - (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
          - gammaMatrix m * gammaMatrix m) * lampBase m := by
    have hDG := lampBase_comm_gammaSq m
    calc lampBase m * (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ)
          - (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ) * lampBase m
        = lampBase m * (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
            - gammaMatrix m * gammaMatrix m)
          - (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
            - gammaMatrix m * gammaMatrix m) * lampBase m
          + (lampBase m * (gammaMatrix m * gammaMatrix m)
            - (gammaMatrix m * gammaMatrix m) * lampBase m) := by noncomm_ring
      _ = _ := by rw [hDG, sub_self, add_zero]
  rw [hcomm]
  have hE := norm_conj_sub_sq_le m
  calc ‖lampBase m * (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
          - gammaMatrix m * gammaMatrix m)
        - (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
          - gammaMatrix m * gammaMatrix m) * lampBase m‖
      ≤ ‖lampBase m * (stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
          - gammaMatrix m * gammaMatrix m)‖
        + ‖(stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
          - gammaMatrix m * gammaMatrix m) * lampBase m‖ := norm_sub_le _ _
    _ = ‖stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
          - gammaMatrix m * gammaMatrix m‖
        + ‖stableMatrix m * gammaMatrix m * (stableMatrix m)ᴴ
          - gammaMatrix m * gammaMatrix m‖ := by
        rw [CStarRing.norm_mem_unitary_mul _ (lampBase_mem m),
          CStarRing.norm_mul_mem_unitary _ (lampBase_mem m)]
    _ ≤ ‖defectPhase m + 1‖ + ‖defectPhase m + 1‖ := by linarith
    _ = 2 * ‖defectPhase m + 1‖ := by ring

theorem two_le_opLength_negOne (m : ℕ) :
    2 ≤ opLength (site m) (negOneU m) := by
  obtain ⟨i⟩ := instNonemptySite m
  have hentry : Complex.normSq
      ((((negOneU m : Matrix.unitaryGroup (site m) ℂ) :
        Matrix (site m) (site m) ℂ) - 1) i i) = 4 := by
    -- one `Matrix.one_apply_eq` rewrites both occurrences at once, so a second
    -- copy has nothing left to match
    rw [coe_negOneU, Matrix.sub_apply, Matrix.neg_apply, Matrix.one_apply_eq,
      show (-(1 : ℂ) - 1 = -2) from by ring, Complex.normSq_apply]
    norm_num
  have hle := normSq_entry_le_sq_l2_opNorm (site m)
    (((negOneU m : Matrix.unitaryGroup (site m) ℂ) :
      Matrix (site m) (site m) ℂ) - 1) i i
  rw [hentry] at hle
  have hnn : (0 : ℝ) ≤ opLength (site m) (negOneU m) := opLength_nonneg _ _
  rw [opLength] at hnn ⊢
  nlinarith

/-! ## The corona representation of `E_BS` -/

/-- The generators of `E_BS`, as sequences of unitaries. -/
noncomputable def genSeq : Generator → (∀ n, Matrix.unitaryGroup (site n) ℂ)
  | 0 => fun n ↦ gammaU n
  | 1 => fun n ↦ stableU n
  | 2 => fun n ↦ lampU n

@[simp] theorem genSeq_gamma : genSeq gammaIndex = fun n ↦ gammaU n := rfl
@[simp] theorem genSeq_stable : genSeq stableIndex = fun n ↦ stableU n := rfl
@[simp] theorem genSeq_lamp : genSeq lampIndex = fun n ↦ lampU n := rfl

/-- The generators of `E_BS`, in the cofinite norm-matrix corona. -/
noncomputable def coronaGen (i : Generator) : NormMatrixCoronaUnitary site :=
  QuotientGroup.mk (genSeq i)

theorem lift_coronaGen (w : FreeGroup Generator) :
    FreeGroup.lift coronaGen w
      = QuotientGroup.mk (FreeGroup.lift genSeq w) := by
  have h : FreeGroup.lift coronaGen
      = (QuotientGroup.mk' (nullCofiniteOpSubgroup site)).comp
        (FreeGroup.lift genSeq) := by
    apply FreeGroup.ext_hom
    intro i
    simp [coronaGen]
  rw [h]
  rfl

theorem stableRelator_null :
    FreeGroup.lift genSeq stableRelator ∈ nullCofiniteOpSubgroup site := by
  have hlift : FreeGroup.lift genSeq stableRelator
      = fun n ↦ stableU n * gammaU n * (stableU n)⁻¹
        * (gammaU n * gammaU n)⁻¹ := by
    rw [CyclicBaseLEFObstruction.lift_stableRelator, pow_two]
    funext n
    rfl
  rw [hlift]
  intro ε hε
  filter_upwards [eventually_defect_lt ε hε] with n hn
  show opLength (site n) (stableU n * gammaU n * (stableU n)⁻¹
    * (gammaU n * gammaU n)⁻¹) < ε
  have h1 := opLength_stable_le n
  have h2 : (0 : ℝ) ≤ ‖defectPhase n + 1‖ := norm_nonneg _
  linarith

theorem lampGammaRelator_null :
    FreeGroup.lift genSeq lampGammaRelator ∈ nullCofiniteOpSubgroup site := by
  have hlift : FreeGroup.lift genSeq lampGammaRelator
      = fun n ↦ ⁅lampU n, gammaU n⁆ := by
    rw [CyclicBaseLEFObstruction.lift_lampGammaRelator]
    funext n
    rfl
  rw [hlift]
  intro ε hε
  filter_upwards [eventually_defect_lt ε hε] with n hn
  show opLength (site n) (⁅lampU n, gammaU n⁆) < ε
  exact lt_of_le_of_lt (opLength_lampGamma_le n) hn

/-- The marked word evaluates, in every coordinate, to `-1`. -/
theorem lift_genSeq_marked :
    FreeGroup.lift genSeq markedWord = fun n ↦ negOneU n := by
  rw [CyclicBaseLEFObstruction.lift_markedWord]
  funext n
  show markedCompressionWord (stableU n) (gammaU n) (lampU n) = negOneU n
  exact marked_value n

theorem negOneSeq_not_null :
    (fun n ↦ negOneU n) ∉ nullCofiniteOpSubgroup site := by
  intro hmem
  obtain ⟨n, hn⟩ := (hmem 1 one_pos).exists
  have h2 := two_le_opLength_negOne n
  have hval : ((fun k ↦ negOneU k : ∀ k, Matrix.unitaryGroup (site k) ℂ) n)
      = negOneU n := rfl
  rw [hval] at hn
  linarith

/-- All seven printed relators of `E_BS` hold in the corona. -/
theorem coronaGen_kills_relators :
    ∀ r ∈ relators, FreeGroup.lift coronaGen r = 1 := by
  intro r hr
  rw [lift_coronaGen, QuotientGroup.eq_one_iff]
  simp [relators] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact stableRelator_null
  · have hval : FreeGroup.lift genSeq lampSqRelator = 1 := by
      have hlift : FreeGroup.lift genSeq lampSqRelator
          = (genSeq lampIndex) ^ 2 := by
        simp only [lampSqRelator, lampWord, map_pow, FreeGroup.lift_apply_of]
      rw [hlift, pow_two]
      funext n
      show lampU n * lampU n = 1
      exact lampU_mul_self n
    rw [hval]
    exact one_mem _
  · exact lampGammaRelator_null
  · have hval : FreeGroup.lift genSeq markedSqRelator = 1 := by
      have hlift : FreeGroup.lift genSeq markedSqRelator
          = (FreeGroup.lift genSeq markedWord) ^ 2 := by
        simp only [markedSqRelator, map_pow]
      rw [hlift, lift_genSeq_marked, pow_two]
      funext n
      show negOneU n * negOneU n = 1
      exact negOneU_mul_self n
    rw [hval]
    exact one_mem _
  · have hval : FreeGroup.lift genSeq markedGammaRelator = 1 := by
      have hlift : FreeGroup.lift genSeq markedGammaRelator
          = ⁅FreeGroup.lift genSeq markedWord, genSeq gammaIndex⁆ := by
        simp only [markedGammaRelator, commutatorWord, gammaWord,
          commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [hlift, lift_genSeq_marked]
      funext n
      show ⁅negOneU n, gammaU n⁆ = 1
      exact commutatorElement_eq_one_iff_commute.mpr (negOneU_commute n _)
    rw [hval]
    exact one_mem _
  · have hval : FreeGroup.lift genSeq markedStableRelator = 1 := by
      have hlift : FreeGroup.lift genSeq markedStableRelator
          = ⁅FreeGroup.lift genSeq markedWord, genSeq stableIndex⁆ := by
        simp only [markedStableRelator, commutatorWord, stableWord,
          commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [hlift, lift_genSeq_marked]
      funext n
      show ⁅negOneU n, stableU n⁆ = 1
      exact commutatorElement_eq_one_iff_commute.mpr (negOneU_commute n _)
    rw [hval]
    exact one_mem _
  · have hval : FreeGroup.lift genSeq markedLampRelator = 1 := by
      have hlift : FreeGroup.lift genSeq markedLampRelator
          = ⁅FreeGroup.lift genSeq markedWord, genSeq lampIndex⁆ := by
        simp only [markedLampRelator, commutatorWord, lampWord,
          commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [hlift, lift_genSeq_marked]
      funext n
      show ⁅negOneU n, lampU n⁆ = 1
      exact commutatorElement_eq_one_iff_commute.mpr (negOneU_commute n _)
    rw [hval]
    exact one_mem _

/-- **The corona representation of `E_BS`.**  Every printed relator holds in
the corona.  At each single stage five of the seven hold exactly, and the two
others -- the doubling relator and the lamp commutator -- hold with defect
`O(1/m)`; `finiteStageSpecification` is the stagewise statement. -/
noncomputable def coronaRep : LiteralGroup →* NormMatrixCoronaUnitary site :=
  PresentedGroup.toGroup coronaGen_kills_relators

theorem coronaRep_mark :
    coronaRep mark = QuotientGroup.mk (fun n ↦ negOneU n) := by
  change PresentedGroup.toGroup coronaGen_kills_relators
    (PresentedGroup.mk _ markedWord) = _
  rw [presentedToGroup_mk, lift_coronaGen, lift_genSeq_marked]

/-- **The marked word survives in the corona.** -/
theorem coronaRep_mark_ne_one : coronaRep mark ≠ 1 := by
  rw [coronaRep_mark]
  intro h
  exact negOneSeq_not_null ((QuotientGroup.eq_one_iff _).mp h)

/-! ## The finite-stage specification

Everything above the corona is a limit statement: `coronaGen_kills_relators`
says the seven printed relators hold *in the corona*, and
`coronaRep_mark_ne_one` that the mark survives there.  Neither records what
happens at one stage, and the split between the exact and the approximate
relators is a stagewise fact that a prose summary can get wrong -- as the
module docstring of this file did, for "six of the seven".

`finiteStageSpecification` states every stagewise fact at once. -/

/-- The generator assignment of the `m`-th model. -/
noncomputable def stageGen (m : ℕ) (i : Generator) :
    Matrix.unitaryGroup (site m) ℂ :=
  genSeq i m

@[simp] theorem stageGen_gamma (m : ℕ) : stageGen m gammaIndex = gammaU m := rfl
@[simp] theorem stageGen_stable (m : ℕ) :
    stageGen m stableIndex = stableU m := rfl
@[simp] theorem stageGen_lamp (m : ℕ) : stageGen m lampIndex = lampU m := rfl

/-- **The marked word is the scalar `-1` at every single stage**, not merely
in the limit. -/
theorem lift_stageGen_marked (m : ℕ) :
    FreeGroup.lift (stageGen m) markedWord = negOneU m := by
  rw [CyclicBaseLEFObstruction.lift_markedWord, stageGen_stable, stageGen_gamma,
    stageGen_lamp]
  exact marked_value m

/-! ### The five exact relators -/

theorem lift_stageGen_lampSq (m : ℕ) :
    FreeGroup.lift (stageGen m) lampSqRelator = 1 := by
  have hlift : FreeGroup.lift (stageGen m) lampSqRelator
      = (stageGen m lampIndex) ^ 2 := by
    simp only [lampSqRelator, lampWord, map_pow, FreeGroup.lift_apply_of]
  rw [hlift, stageGen_lamp, pow_two]
  exact lampU_mul_self m

theorem lift_stageGen_markedSq (m : ℕ) :
    FreeGroup.lift (stageGen m) markedSqRelator = 1 := by
  have hlift : FreeGroup.lift (stageGen m) markedSqRelator
      = (FreeGroup.lift (stageGen m) markedWord) ^ 2 := by
    simp only [markedSqRelator, map_pow]
  rw [hlift, lift_stageGen_marked, pow_two]
  exact negOneU_mul_self m

theorem lift_stageGen_markedGamma (m : ℕ) :
    FreeGroup.lift (stageGen m) markedGammaRelator = 1 := by
  have hlift : FreeGroup.lift (stageGen m) markedGammaRelator
      = ⁅FreeGroup.lift (stageGen m) markedWord, stageGen m gammaIndex⁆ := by
    simp only [markedGammaRelator, commutatorWord, gammaWord,
      commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]
  rw [hlift, lift_stageGen_marked]
  exact commutatorElement_eq_one_iff_commute.mpr (negOneU_commute m _)

theorem lift_stageGen_markedStable (m : ℕ) :
    FreeGroup.lift (stageGen m) markedStableRelator = 1 := by
  have hlift : FreeGroup.lift (stageGen m) markedStableRelator
      = ⁅FreeGroup.lift (stageGen m) markedWord, stageGen m stableIndex⁆ := by
    simp only [markedStableRelator, commutatorWord, stableWord,
      commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]
  rw [hlift, lift_stageGen_marked]
  exact commutatorElement_eq_one_iff_commute.mpr (negOneU_commute m _)

theorem lift_stageGen_markedLamp (m : ℕ) :
    FreeGroup.lift (stageGen m) markedLampRelator = 1 := by
  have hlift : FreeGroup.lift (stageGen m) markedLampRelator
      = ⁅FreeGroup.lift (stageGen m) markedWord, stageGen m lampIndex⁆ := by
    simp only [markedLampRelator, commutatorWord, lampWord,
      commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]
  rw [hlift, lift_stageGen_marked]
  exact commutatorElement_eq_one_iff_commute.mpr (negOneU_commute m _)

/-! ### The two approximate relators -/

theorem opLength_stageGen_stableRelator (m : ℕ) :
    opLength (site m) (FreeGroup.lift (stageGen m) stableRelator)
      ≤ ‖defectPhase m + 1‖ := by
  rw [CyclicBaseLEFObstruction.lift_stableRelator, stageGen_stable,
    stageGen_gamma, pow_two]
  exact opLength_stable_le m

theorem opLength_stageGen_lampGammaRelator (m : ℕ) :
    opLength (site m) (FreeGroup.lift (stageGen m) lampGammaRelator)
      ≤ 2 * ‖defectPhase m + 1‖ := by
  rw [CyclicBaseLEFObstruction.lift_lampGammaRelator, stageGen_lamp,
    stageGen_gamma]
  exact opLength_lampGamma_le m

/-- Both approximate relators have defect tending to zero.  The marked word
does not: it is the scalar `-1` at every stage. -/
theorem finiteStage_defects_vanish (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in Filter.cofinite,
      opLength (site m) (FreeGroup.lift (stageGen m) stableRelator) < ε ∧
        opLength (site m) (FreeGroup.lift (stageGen m) lampGammaRelator) < ε := by
  filter_upwards [eventually_defect_lt ε hε] with m hm
  have h0 : (0 : ℝ) ≤ ‖defectPhase m + 1‖ := norm_nonneg _
  exact ⟨lt_of_le_of_lt (opLength_stageGen_stableRelator m) (by linarith),
    lt_of_le_of_lt (opLength_stageGen_lampGammaRelator m) hm⟩

/-! ### The lamp is not a monomial matrix

The module docstring calls the models monomial, and `γ₀` and `t` are.  The
lamp is not: `D = 2^{-1/2}(X + Z)` has two nonzero entries in every row, which
is exactly the room the permutation dichotomy of
`Analysis.AmenableQuasidiagonal` leaves open. -/

theorem half2_ne_zero : half2 ≠ 0 := by
  intro h
  have hsq := half2_mul_half2
  rw [h, mul_zero] at hsq
  exact absurd hsq.symm (by norm_num)

theorem monomialMatrix_row_unique (Y : FiniteModel) (d : Y → ℂ)
    (σ : Equiv.Perm Y) {i j j' : Y}
    (hj : monomialMatrix Y d σ i j ≠ 0)
    (hj' : monomialMatrix Y d σ i j' ≠ 0) : j = j' := by
  have h1 : σ i = j := by
    by_contra hc
    exact hj (by rw [monomialMatrix_apply, if_neg hc])
  have h2 : σ i = j' := by
    by_contra hc
    exact hj' (by rw [monomialMatrix_apply, if_neg hc])
  rw [← h1, ← h2]

theorem lampBase_apply (m : ℕ) (i j : site m) :
    lampBase m i j = half2 * (flipMatrix m i j + spinMatrix m i j) := by
  show (half2 • (flipMatrix m + spinMatrix m)) i j = _
  rw [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]

theorem lampBase_apply_diag (m : ℕ) :
    lampBase m ((0 : Fin 2), (0 : ZMod (modulus m)))
      ((0 : Fin 2), (0 : ZMod (modulus m))) = half2 := by
  have hf : flipMatrix m ((0 : Fin 2), (0 : ZMod (modulus m)))
      ((0 : Fin 2), (0 : ZMod (modulus m))) = 0 := by
    rw [flipMatrix, monomialMatrix_apply, if_neg]
    intro hc
    rw [flipPerm_apply, Prod.ext_iff] at hc
    exact absurd hc.1 (by decide)
  have hs : spinMatrix m ((0 : Fin 2), (0 : ZMod (modulus m)))
      ((0 : Fin 2), (0 : ZMod (modulus m))) = 1 := by
    rw [spinMatrix, monomialMatrix_apply, if_pos rfl]
    exact spin_zero
  rw [lampBase_apply, hf, hs, zero_add, mul_one]

theorem lampBase_apply_offdiag (m : ℕ) :
    lampBase m ((0 : Fin 2), (0 : ZMod (modulus m)))
      ((1 : Fin 2), (0 : ZMod (modulus m))) = half2 := by
  have hf : flipMatrix m ((0 : Fin 2), (0 : ZMod (modulus m)))
      ((1 : Fin 2), (0 : ZMod (modulus m))) = 1 := by
    rw [flipMatrix, monomialMatrix_apply, if_pos]
    rw [flipPerm_apply, Prod.ext_iff]
    exact ⟨by decide, rfl⟩
  have hs : spinMatrix m ((0 : Fin 2), (0 : ZMod (modulus m)))
      ((1 : Fin 2), (0 : ZMod (modulus m))) = 0 := by
    rw [spinMatrix, monomialMatrix_apply, if_neg]
    intro hc
    rw [Equiv.Perm.coe_one, id_eq, Prod.ext_iff] at hc
    exact absurd hc.1 (by decide)
  rw [lampBase_apply, hf, hs, add_zero, mul_one]

/-- **The lamp is not a monomial matrix.**  Two entries of one row are
nonzero, and a monomial matrix has at most one. -/
theorem lampBase_not_monomial (m : ℕ) (d : site m → ℂ)
    (σ : Equiv.Perm (site m)) :
    lampBase m ≠ monomialMatrix (site m) d σ := by
  intro hEq
  have h1 : monomialMatrix (site m) d σ
      ((0 : Fin 2), (0 : ZMod (modulus m)))
      ((0 : Fin 2), (0 : ZMod (modulus m))) ≠ 0 := by
    rw [← hEq, lampBase_apply_diag]
    exact half2_ne_zero
  have h2 : monomialMatrix (site m) d σ
      ((0 : Fin 2), (0 : ZMod (modulus m)))
      ((1 : Fin 2), (0 : ZMod (modulus m))) ≠ 0 := by
    rw [← hEq, lampBase_apply_offdiag]
    exact half2_ne_zero
  have := monomialMatrix_row_unique (site m) d σ h1 h2
  rw [Prod.ext_iff] at this
  exact absurd this.1 (by decide)

/-! ### The specification -/

/-- **The finite-stage specification of the cyclic models.**

At one fixed stage `m`, in one statement:

* the lamp involution and the four centrality relators of the mark hold
  **exactly**;
* the doubling relator and the lamp commutator hold only **approximately**,
  with defects `‖ζ^{m+1} + 1‖` and at most twice that
  (`finiteStage_defects_vanish` sends both to zero);
* the marked word is **exactly** the scalar `-1`;
* the lamp is a sum of two monomial matrices and is not itself monomial.

Read this together with `Monsters.CyclicBaseLEFObstruction`, which proves that
no *exact* finite model can do this: the two approximate relators are not slack
in the construction, they are forced.

Nothing here says that the realized Clifford quotient is MF, and nothing here
may be read as saying it.  What the models certify is the survival of the
marked word in one corona, which is all the sharpness paragraph consumes; MF of
the quotient is `CliffordBSPrintedRoute.isOperatorMF_realizedQuotient` and
still carries its hypothesis. -/
theorem finiteStageSpecification (m : ℕ) :
    (FreeGroup.lift (stageGen m) lampSqRelator = 1 ∧
        FreeGroup.lift (stageGen m) markedSqRelator = 1 ∧
        FreeGroup.lift (stageGen m) markedGammaRelator = 1 ∧
        FreeGroup.lift (stageGen m) markedStableRelator = 1 ∧
        FreeGroup.lift (stageGen m) markedLampRelator = 1) ∧
      opLength (site m) (FreeGroup.lift (stageGen m) stableRelator)
          ≤ ‖defectPhase m + 1‖ ∧
      opLength (site m) (FreeGroup.lift (stageGen m) lampGammaRelator)
          ≤ 2 * ‖defectPhase m + 1‖ ∧
      FreeGroup.lift (stageGen m) markedWord = negOneU m ∧
      lampBase m = half2 • (flipMatrix m + spinMatrix m) ∧
      (∀ (d : site m → ℂ) (σ : Equiv.Perm (site m)),
        lampBase m ≠ monomialMatrix (site m) d σ) :=
  ⟨⟨lift_stageGen_lampSq m, lift_stageGen_markedSq m,
      lift_stageGen_markedGamma m, lift_stageGen_markedStable m,
      lift_stageGen_markedLamp m⟩,
    opLength_stageGen_stableRelator m, opLength_stageGen_lampGammaRelator m,
    lift_stageGen_marked m, rfl, lampBase_not_monomial m⟩

/-! ## The concrete group, and why no elementary route reaches it

The group the sharpness paragraph is about is the realized Clifford quotient
of Theorem C: the subgroup of

`CliffordBS = lampGroup (BSLike ⧸ ⟨γ₀⟩) ⋊ BSLike`,
`BSLike = Multiplicative ℚ ⋊ Multiplicative ℤ` with `ℤ` acting by doubling,

generated by the three displayed elements `γ₀`, `t`, `c`.  It is amenable --
locally finite by solvable -- and it is finitely generated
(`realizedQuotient_finitelyGenerated`).

Every elementary positive-MF criterion in this repository asks for *exact*
finite models, and each one provably fails here.  The theorems below are the
reason the corona representation above had to be built by hand rather than
assembled from `isOperatorMF_of_residuallyFinite`,
`isOperatorMF_of_locallyFinite` or
`isOperatorMF_of_forall_finset_residuallyFinite`: all three criteria factor
through `IsLEF`, and `CyclicBaseLEFObstruction` refutes that.  The last one
refutes it not merely for this quotient but for every homomorphic image in
which the marked word survives, so no other choice of witness group can
rescue the elementary route. -/

/-- The concrete group of the sharpness paragraph is amenable.  This is the
half of the printed sentence that is fully machine-checked, restated here at
the group the paragraph applies it to. -/
theorem realizedQuotient_isAmenable :
    Amenability.IsAmenable RealizedQuotient :=
  CyclicBaseCalibration.isAmenable_subgroup_CliffordBS realization.range

/-- Local finiteness fails, so `isOperatorMF_of_locallyFinite` does not
apply. -/
theorem realizedQuotient_not_isLocallyFiniteGroup :
    ¬ IsLocallyFiniteGroup RealizedQuotient :=
  fun h ↦ CyclicBaseLEFObstruction.realizedQuotient_not_isLEF
    (isLEF_of_locallyFinite h)

/-- Exhaustion by residually finite subgroups fails, so
`isOperatorMF_of_forall_finset_residuallyFinite` does not apply.  For a
finitely generated group the hypothesis collapses to residual finiteness of
the group itself, and that is refuted by the marked word. -/
theorem realizedQuotient_not_locallyResiduallyFinite :
    ¬ (∀ s : Finset RealizedQuotient, ∃ H : Subgroup RealizedQuotient,
        (∀ x ∈ s, x ∈ H) ∧ Group.ResiduallyFinite H) :=
  fun h ↦ CyclicBaseLEFObstruction.realizedQuotient_not_isLEF
    (isLEF_of_forall_finset_residuallyFinite h)

/-- **No quotient of `E_BS` in which the mark survives is LEF.**  So the
failure is not an artifact of the particular quotient the manuscript chose:
*every* group that could serve the sharpness paragraph lies outside the reach
of the exact-model criteria.  This is
`CyclicBaseLEFObstruction.not_isLEF_of_markedCompression`, instantiated along
an arbitrary homomorphism rather than along `quotientMap`. -/
theorem not_isLEF_of_mark_survives {Q : Type*} [Group Q]
    (f : LiteralGroup →* Q) (hf : f mark ≠ 1) : ¬ IsLEF Q := by
  refine CyclicBaseLEFObstruction.not_isLEF_of_markedCompression
    (f stable) (f gamma) (f lamp) ?_ (lamp_comm_gamma.map f) ?_
  · rw [← map_inv, ← map_mul, ← map_mul, stable_relation, map_pow]
  · rw [← map_markedCompressionWord, ← mark_eq_markedCompressionWord]
    exact hf

/-- **The elementary routes are closed, all four at once.**  An amenable,
finitely generated group on which residual finiteness, local finiteness,
exhaustion by residually finite subgroups and local embeddability into finite
groups all fail: the sharpness paragraph cannot be discharged by any exact
finite model, which is why the approximate model above is not a matter of
convenience. -/
theorem realizedQuotient_elementary_routes_closed :
    Amenability.IsAmenable RealizedQuotient ∧
      ¬ Group.ResiduallyFinite RealizedQuotient ∧
      ¬ IsLocallyFiniteGroup RealizedQuotient ∧
      ¬ (∀ s : Finset RealizedQuotient, ∃ H : Subgroup RealizedQuotient,
          (∀ x ∈ s, x ∈ H) ∧ Group.ResiduallyFinite H) ∧
      ¬ IsLEF RealizedQuotient :=
  ⟨realizedQuotient_isAmenable,
    CyclicBaseLEFObstruction.realizedQuotient_not_residuallyFinite,
    realizedQuotient_not_isLocallyFiniteGroup,
    realizedQuotient_not_locallyResiduallyFinite,
    CyclicBaseLEFObstruction.realizedQuotient_not_isLEF⟩

/-! ## The endpoint of the sharpness paragraph -/

/-- **The manuscript's sharpness step, unconditionally.**  The marked word of
`E_BS` is not invisible to cofinite norm-matrix coronas: one explicit sequence
of finite matrix models separates it from the identity.  No amenability, no
quasidiagonality and no citation enters. -/
theorem mark_not_coronaMFInvisible :
    ¬ CoronaMFInvisible (mark : LiteralGroup) :=
  fun h ↦ coronaRep_mark_ne_one (h site card_site_pos coronaRep)

/-- The same statement in the radical language of `\section{Consequences}`:
`w_BS ∉ Res_MF(E_BS)`. -/
theorem mark_notMem_coronaMFResidual :
    (mark : LiteralGroup) ∉ coronaMFResidual LiteralGroup :=
  fun h ↦ mark_not_coronaMFInvisible h

/-- The same for the genuine C-star-corona radical. -/
theorem mark_not_actualCoronaMFInvisible :
    ¬ ActualCoronaMFInvisible (mark : LiteralGroup) :=
  fun h ↦ mark_not_coronaMFInvisible
    (actualCoronaMFInvisible_iff_coronaMFInvisible.mp h)

/-- The same for the universal-ultraproduct residual. -/
theorem mark_notMem_normMFResidual :
    (mark : LiteralGroup) ∉ normMFResidual LiteralGroup := by
  rw [← coronaMFResidual_eq_normMFResidual]
  exact mark_notMem_coronaMFResidual

/-- The image of the explicit corona representation is an operator-MF group:
it sits inside a cofinite norm-matrix corona by construction. -/
theorem coronaRep_range_isOperatorMF : IsOperatorMF coronaRep.range :=
  ⟨site, card_site_pos, coronaRep.range.subtype, Subtype.val_injective⟩

theorem rangeRestrict_mark_ne_one : coronaRep.rangeRestrict mark ≠ 1 := by
  intro h
  apply coronaRep_mark_ne_one
  exact congrArg (fun z : coronaRep.range ↦
    (z : NormMatrixCoronaUnitary site)) h

/-- **A concrete MF quotient of `E_BS` in which the marked word survives.**
This is the shape of the printed argument -- *some* MF quotient detects
`w_BS` -- with the quotient exhibited instead of obtained from amenability and
Tikuisis--White--Winter.  The realized Clifford quotient of Theorem C is a
different group, and no claim is made about it here. -/
theorem exists_isOperatorMF_image_detecting_mark :
    IsOperatorMF coronaRep.range ∧ coronaRep.rangeRestrict mark ≠ 1 :=
  ⟨coronaRep_range_isOperatorMF, rangeRestrict_mark_ne_one⟩

/-- **The sharpness paragraph, in one closed statement.**  The marked word of
the cyclic-base group is nontrivial, is in none of the repository's MF
radicals, and the corona representation that detects it is exhibited rather
than asserted.

What is *not* claimed: that amenable groups are MF, that the realized Clifford
quotient is MF, or that any quasidiagonality theorem holds.  The paragraph's
conclusion never needed them. -/
theorem manuscriptSharpnessOfKazhdanHypothesis :
    (mark : LiteralGroup) ≠ 1 ∧
      (mark : LiteralGroup) ∉ coronaMFResidual LiteralGroup ∧
      (mark : LiteralGroup) ∉ normMFResidual LiteralGroup ∧
      IsOperatorMF coronaRep.range ∧
      ∃ (X : ℕ → FiniteModel), (∀ n, 0 < Fintype.card (X n)) ∧
        ∃ rho : LiteralGroup →* NormMatrixCoronaUnitary X, rho mark ≠ 1 :=
  ⟨mark_ne_one, mark_notMem_coronaMFResidual, mark_notMem_normMFResidual,
    coronaRep_range_isOperatorMF,
    site, card_site_pos, coronaRep, coronaRep_mark_ne_one⟩

end CliffordBSAmenableMF
end GroupApproximation

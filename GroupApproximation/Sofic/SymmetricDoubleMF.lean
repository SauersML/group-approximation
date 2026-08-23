import GroupApproximation.Sofic.TerminalQuotientPresentation
import GroupApproximation.Monsters.CyclicBaseLEFObstruction

/-!
# The exact-model route to the symmetric double is closed

`AmalgamMFTrace` reduces the manuscript's exact MF-radical identity to one
analytic input: operator MF of the symmetric double `Σ *_B Σ`, equivalently of
the free-lamp amalgam `TerminalAmalgam = Σ *_B (B × C₂)`.  Two exact-model
routes to that input are available in this library, both unconditional once
their hypothesis is met:

* `LEFSofic.isLEF_of_residuallyFinite` plus `LocallyFiniteMF.isOperatorMF_of_isLEF`
  — residual finiteness of the amalgam would suffice;
* `LEFSofic.isLEF_of_forall_finset_residuallyFinite` — the weaker *local*
  criterion, that every finite subset lies in a residually finite subgroup.

**Both routes are closed, and this file proves it.**  The obstruction is a
separability failure, and it is completely explicit.

## The obstruction, in one sentence

`Σ = Vertical alpha conjD_injective` is the ascending HNN extension of the
affine base along doubling, and `B = sigmaBase` is its level-zero copy.  On the
marked translation `v₁` the compression is literally squaring —
`LiteralNonMFLinearWitness.conjD_v1G : conjD v1G = v1G ^ 2` — so `Σ` contains
the Baumslag–Solitar pattern `t v₁ t⁻¹ = v₁²`.  In *any* finite group that
pattern is degenerate: `v₁` is conjugate to its own square, so iterating around
the finite order of `t` recovers `v₁` from `v₁²`, and the half-translation
`s = t⁻¹ v₁ t` becomes a *power of `v₁`*.  Hence

* `sigmaBase_not_separable` — every homomorphism from `Σ` to a finite group
  sends `s` into the image of `B`, although `s ∉ B`
  (`escapeElement_not_mem_sigmaBase`, from
  `MarkedCompression.tVertical_inv_conj_not_mem` and
  `ExplicitLinearModel.v1G_not_mem_range`).  `B` is *not* a separable subgroup
  of `Σ`: its closure in the profinite topology already swallows the next
  telescope level.

In the amalgam the lamp `d` centralizes `B` by construction, so the moment `s`
is indistinguishable from an element of `B` the Bass–Serre witness
`⁅d, s⁆ = d s d⁻¹ s⁻¹` dies.  That witness is nontrivial — it is exactly
`FreeLampReduction.lampCore_ne_one` at `s ∉ B` and the order-two lamp.  The two
statements together are:

* `terminalAmalgam_not_residuallyFinite` — `Σ *_B (B × C₂)` is **not**
  residually finite;
* `terminalAmalgam_not_isLEF` — it is not even locally embeddable into finite
  groups, so `not_forall_finset_residuallyFinite` says the local criterion
  `isLEF_of_forall_finset_residuallyFinite` cannot be fed either;
* `symmetricDouble_not_residuallyFinite` — the symmetric double `Σ *_B Σ` is
  not residually finite, through the index-two identification
  `lampKernelFlip_equiv_symmetricDouble` and
  `LEFSofic.residuallyFinite_of_finiteIndex`.

The LEF statement, not merely the residual-finiteness one, is what closes the
route: LEF is strictly weaker than residual finiteness, so refuting residual
finiteness alone would leave `isLEF_of_forall_finset_residuallyFinite` and
`isOperatorMF_of_isLEF` formally open.  The mechanism is the one
`Monsters/CyclicBaseLEFObstruction` isolated for the cyclic base, reused here:
the two relations `t a t⁻¹ = a²` and `[c, a] = 1` are short words, so a local
embedding transports them verbatim into a finite permutation group, where
`coreWord_eq_one_of_finite` kills the witness.

## What this does *not* say

It says nothing against `IsOperatorMF (SymmetricDouble SigmaGroup sigmaBase)`
itself.  MF is an *approximate* matrix-model property; the groups excluded here
are excluded only from *exact* finite models.  What the file establishes is that
the analytic input must come from a genuinely approximate source — Shulman's
symmetric-amalgamation theorem or another operator-algebraic route — and never
from residual finiteness, local residual finiteness, or LEF.  In particular no
amalgam permanence theorem for `Monoid.PushoutI` can supply it, because the
conclusion such a theorem would have to reach is false here.

Nor does it disturb `WitnessVerticalResiduallyFinite.vertical_residuallyFinite`:
`Σ` itself *is* residually finite.  Residual finiteness of the vertex group is
simply not inherited by the amalgam, precisely because the edge group is not
separable in it.
-/

namespace GroupApproximation
namespace SymmetricDoubleMF

/-! ## The finite-model collapse of the squaring pattern

Nothing in this section mentions the amalgam.  Three elements `t`, `a`, `c` of
an arbitrary *finite* group satisfying `t a t⁻¹ = a²` and `[c, a] = 1` already
satisfy `[c, t⁻¹ a t] = 1`, because in a finite group the conjugate `t⁻¹ a t`
is a power of `a`. -/

section FiniteCollapse

variable {H : Type*} [Group H]

/-- **The half-translation is a power.**  In a finite group the squaring
relation `t a t⁻¹ = a²` forces `t⁻¹ a t` to be a power of `a`: conjugating `a`
by `t ^ j` raises it to the `2 ^ j`, and `t ^ (orderOf t - 1) = t⁻¹`. -/
theorem exists_conj_inv_eq_pow [Finite H] {t a : H} (hst : t * a * t⁻¹ = a ^ 2) :
    ∃ j : ℕ, t⁻¹ * a * t = a ^ (2 ^ j) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, orderOf t = M + 1 := by
    have hpos : 0 < orderOf t := orderOf_pos t
    exact ⟨orderOf t - 1, by omega⟩
  refine ⟨M, ?_⟩
  have hpow : t ^ (M + 1) = 1 := by
    rw [← hM]
    exact pow_orderOf_eq_one t
  have hmul : t ^ M * t = 1 := by
    rw [← pow_succ]
    exact hpow
  have htM : t ^ M = t⁻¹ := by
    rw [← mul_inv_cancel_right (t ^ M) t, hmul, one_mul]
  have hconj := CyclicBaseLEFObstruction.conj_pow_two_pow hst M
  rw [htM, inv_inv] at hconj
  exact hconj

/-- **The finite-model collapse.**  In every finite group the four-letter
Bass–Serre word `c (t⁻¹ a t) c⁻¹ (t⁻¹ a t)⁻¹` is trivial as soon as the
squaring relation and the commutation `[c, a] = 1` hold.  No representation
theory and no dimension hypothesis enter: only finiteness. -/
theorem coreWord_eq_one_of_finite [Finite H] {t a c : H}
    (hst : t * a * t⁻¹ = a ^ 2) (hca : Commute c a) :
    c * (t⁻¹ * a * t) * c⁻¹ * (t⁻¹ * a * t)⁻¹ = 1 := by
  obtain ⟨j, hj⟩ := exists_conj_inv_eq_pow hst
  have hcomm : Commute c (a ^ (2 ^ j)) := hca.pow_right _
  rw [hj, hcomm.mul_inv_cancel, mul_inv_cancel]

end FiniteCollapse

/-! ## Transporting the two relations into a local model

Three letters and two relators.  This is the free-group bookkeeping that turns
`coreWord_eq_one_of_finite` into a genuine non-embeddability statement, in the
shape `Monsters/CyclicBaseLEFObstruction` uses for the cyclic base. -/

section LocalObstruction

/-- The three test letters `t`, `a`, `c`. -/
abbrev Letter := Fin 3

/-- The stable letter `t`. -/
abbrev stableLetter : Letter := 0
/-- The compressed letter `a`. -/
abbrev baseLetter : Letter := 1
/-- The lamp letter `c`. -/
abbrev lampLetter : Letter := 2

/-- The word `t`. -/
abbrev stableFree : FreeGroup Letter := FreeGroup.of stableLetter
/-- The word `a`. -/
abbrev baseFree : FreeGroup Letter := FreeGroup.of baseLetter
/-- The word `c`. -/
abbrev lampFree : FreeGroup Letter := FreeGroup.of lampLetter

/-- The squaring relator `t a t⁻¹ a⁻²`. -/
abbrev stableRelatorFree : FreeGroup Letter :=
  stableFree * baseFree * stableFree⁻¹ * (baseFree ^ 2)⁻¹

/-- The commutation relator `[c, a]`. -/
abbrev lampRelatorFree : FreeGroup Letter :=
  lampFree * baseFree * lampFree⁻¹ * baseFree⁻¹

/-- The half-translation word `t⁻¹ a t`. -/
abbrev escapeFree : FreeGroup Letter :=
  stableFree⁻¹ * baseFree * stableFree

/-- The tracked witness `[c, t⁻¹ a t]`. -/
abbrev escapeWitnessFree : FreeGroup Letter :=
  lampFree * escapeFree * lampFree⁻¹ * escapeFree⁻¹

/-- The assignment of the three letters to three elements of a group. -/
def letterMap {G : Type*} (t a c : G) : Letter → G
  | 0 => t
  | 1 => a
  | 2 => c

@[simp] theorem letterMap_stable {G : Type*} (t a c : G) :
    letterMap t a c stableLetter = t := rfl

@[simp] theorem letterMap_base {G : Type*} (t a c : G) :
    letterMap t a c baseLetter = a := rfl

@[simp] theorem letterMap_lamp {G : Type*} (t a c : G) :
    letterMap t a c lampLetter = c := rfl

/-- The squaring relator, evaluated in an arbitrary group. -/
theorem lift_stableRelatorFree {H : Type*} [Group H] (u : Letter → H) :
    FreeGroup.lift u stableRelatorFree =
      u stableLetter * u baseLetter * (u stableLetter)⁻¹ *
        ((u baseLetter) ^ 2)⁻¹ := by
  simp only [stableRelatorFree, stableFree, baseFree, map_mul, map_inv, map_pow,
    FreeGroup.lift_apply_of]

/-- The commutation relator, evaluated in an arbitrary group. -/
theorem lift_lampRelatorFree {H : Type*} [Group H] (u : Letter → H) :
    FreeGroup.lift u lampRelatorFree =
      u lampLetter * u baseLetter * (u lampLetter)⁻¹ * (u baseLetter)⁻¹ := by
  simp only [lampRelatorFree, lampFree, baseFree, map_mul, map_inv,
    FreeGroup.lift_apply_of]

/-- The tracked witness, evaluated in an arbitrary group. -/
theorem lift_escapeWitnessFree {H : Type*} [Group H] (u : Letter → H) :
    FreeGroup.lift u escapeWitnessFree =
      u lampLetter * ((u stableLetter)⁻¹ * u baseLetter * u stableLetter) *
        (u lampLetter)⁻¹ *
        ((u stableLetter)⁻¹ * u baseLetter * u stableLetter)⁻¹ := by
  simp only [escapeWitnessFree, escapeFree, lampFree, baseFree, stableFree,
    map_mul, map_inv, FreeGroup.lift_apply_of]

/-- **The squaring pattern is not locally embeddable into finite groups.**  A
group carrying `t a t⁻¹ = a²` and `[c, a] = 1`, in which the Bass–Serre witness
`[c, t⁻¹ a t]` survives, has no exact finite local model: local
multiplicativity on a large enough test set transports both relations verbatim
into a finite permutation group, where `coreWord_eq_one_of_finite` kills the
witness while injectivity of the local embedding keeps it alive. -/
theorem not_isLEF_of_squareCompression {G : Type*} [Group G] (t a c : G)
    (hst : t * a * t⁻¹ = a ^ 2) (hca : Commute c a)
    (hne : c * (t⁻¹ * a * t) * c⁻¹ * (t⁻¹ * a * t)⁻¹ ≠ 1) : ¬ IsLEF G := by
  classical
  intro hlef
  set φ : FreeGroup Letter →* G := FreeGroup.lift (letterMap t a c) with hφ
  have hφstable : φ stableRelatorFree = 1 := by
    rw [hφ, lift_stableRelatorFree, letterMap_stable, letterMap_base, hst,
      mul_inv_cancel]
  have hφlamp : φ lampRelatorFree = 1 := by
    rw [hφ, lift_lampRelatorFree, letterMap_lamp, letterMap_base,
      hca.mul_inv_cancel, mul_inv_cancel]
  have hφwitness : φ escapeWitnessFree
      = c * (t⁻¹ * a * t) * c⁻¹ * (t⁻¹ * a * t)⁻¹ := by
    rw [hφ, lift_escapeWitnessFree, letterMap_stable, letterMap_base,
      letterMap_lamp]
  set tracked : Finset (FreeGroup Letter) :=
    {stableRelatorFree, lampRelatorFree, escapeWitnessFree} with htracked
  have hcontrols : ∀ q : FreeGroup Letter, ∃ s : Finset G,
      ∀ (H : Type) [Group H] (f : G → H), LocalMultiplicativeOn s f →
        FreeGroup.lift (fun i ↦ f (φ (FreeGroup.of i))) q = f (φ q) :=
    fun q ↦ exists_local_word_control φ q
  choose controls hcontrolspec using hcontrols
  set support : Finset G :=
    insert 1 (insert (φ escapeWitnessFree) (tracked.biUnion controls))
    with hsupport
  obtain ⟨n, f, hinj, hlocal⟩ := hlef support
  set u : Letter → Equiv.Perm (Fin n) := fun i ↦ f (φ (FreeGroup.of i))
  set ψ : FreeGroup Letter →* Equiv.Perm (Fin n) := FreeGroup.lift u
  have hword : ∀ q ∈ tracked, ψ q = f (φ q) := by
    intro q hq
    apply hcontrolspec q (Equiv.Perm (Fin n)) f
    apply hlocal.mono
    intro z hz
    simp only [hsupport, Finset.mem_insert, Finset.mem_biUnion]
    exact Or.inr (Or.inr ⟨q, hq, hz⟩)
  have hψstable : ψ stableRelatorFree = 1 := by
    rw [hword stableRelatorFree (by simp [htracked]), hφstable, hlocal.map_one]
  have hψlamp : ψ lampRelatorFree = 1 := by
    rw [hword lampRelatorFree (by simp [htracked]), hφlamp, hlocal.map_one]
  have hmodelStable : u stableLetter * u baseLetter * (u stableLetter)⁻¹
      = (u baseLetter) ^ 2 := by
    apply mul_inv_eq_one.mp
    rw [← lift_stableRelatorFree u]
    exact hψstable
  have hmodelLamp : Commute (u lampLetter) (u baseLetter) := by
    have hraw : u lampLetter * u baseLetter * (u lampLetter)⁻¹ *
        (u baseLetter)⁻¹ = 1 := by
      rw [← lift_lampRelatorFree u]
      exact hψlamp
    have hfix : u lampLetter * u baseLetter * (u lampLetter)⁻¹
        = u baseLetter := mul_inv_eq_one.mp hraw
    show u lampLetter * u baseLetter = u baseLetter * u lampLetter
    calc u lampLetter * u baseLetter
        = u lampLetter * u baseLetter * (u lampLetter)⁻¹ * u lampLetter := by
          group
      _ = u baseLetter * u lampLetter := by rw [hfix]
  have hψwitness : ψ escapeWitnessFree = 1 := by
    rw [lift_escapeWitnessFree u]
    exact coreWord_eq_one_of_finite hmodelStable hmodelLamp
  apply hne
  rw [← hφwitness]
  apply hinj
  · simp [hsupport]
  · simp [hsupport]
  calc f (φ escapeWitnessFree) = ψ escapeWitnessFree :=
        (hword escapeWitnessFree (by simp [htracked])).symm
    _ = 1 := hψwitness
    _ = f 1 := hlocal.map_one.symm

/-- The same pattern rules out residual finiteness, since residually finite
groups are LEF. -/
theorem not_residuallyFinite_of_squareCompression {G : Type*} [Group G]
    (t a c : G) (hst : t * a * t⁻¹ = a ^ 2) (hca : Commute c a)
    (hne : c * (t⁻¹ * a * t) * c⁻¹ * (t⁻¹ * a * t)⁻¹ ≠ 1) :
    ¬ Group.ResiduallyFinite G := by
  intro h
  haveI := h
  exact not_isLEF_of_squareCompression t a c hst hca hne isLEF_of_residuallyFinite

end LocalObstruction

/-! ## The squaring pattern inside `Σ`, and the inseparable half-translation -/

open TerminalQuotientPresentation MarkedCompression ExplicitLinearModel
open LiteralNonMFLinearWitness

noncomputable section

/-- The stable letter of `Σ`.  This is the ambient of
`TerminalQuotientPresentation.amalgamStable`. -/
abbrev sigmaStable : SigmaGroup := tVertical alpha conjD_injective

/-- The marked translation `v₁`, at telescope level zero: an element of `B`. -/
abbrev sigmaUnit : SigmaGroup := iotaVertical alpha conjD_injective v1G

/-- **The half-translation** `s = t⁻¹ v₁ t`, at telescope level one. -/
abbrev escapeElement : SigmaGroup := sigmaStable⁻¹ * sigmaUnit * sigmaStable

theorem escapeElement_eq :
    escapeElement = sigmaStable⁻¹ * sigmaUnit * sigmaStable := rfl

theorem sigmaUnit_mem_sigmaBase : sigmaUnit ∈ sigmaBase :=
  iotaVertical_mem_sigmaBase v1G

/-- **The compression squares the marked translation.**  This is
`LiteralNonMFLinearWitness.conjD_v1G`, `conjD v1G = v1G ^ 2`, transported
through the ascending-HNN relation `t γ t⁻¹ = α γ`: on `v₁` the doubling
matrix `D = diag(2,2,2,1)` acts by doubling the translation. -/
theorem sigma_square_compression :
    sigmaStable * sigmaUnit * sigmaStable⁻¹ = sigmaUnit ^ 2 := by
  have hsq : alpha v1G = v1G ^ 2 := conjD_v1G
  have hc := vertical_compress alpha conjD_injective v1G
  rw [hsq, map_pow] at hc
  exact hc

/-- **The half-translation escapes the base copy.**  `s ∉ B`, because `v₁` is
not in the range of the compression: `ExplicitLinearModel.v1G_not_mem_range`
through `MarkedCompression.tVertical_inv_conj_not_mem`. -/
theorem escapeElement_not_mem_sigmaBase : escapeElement ∉ sigmaBase := by
  have hrange : v1G ∉ Set.range alpha := v1G_not_mem_range
  exact tVertical_inv_conj_not_mem alpha conjD_injective hrange

/-- **`B` is not a separable subgroup of `Σ`.**  Every homomorphism of `Σ` to a
finite group identifies the half-translation `s ∉ B` with an element of `B` —
indeed with a power of `v₁`.  Equivalently, the closure of `B` in the profinite
topology of `Σ` already contains telescope level one, so no finite quotient of
`Σ` can see the difference between `B` and the next level up.

This is the exact obstruction: an amalgam is residually finite only if its edge
group is separable in each vertex group, and here it is not. -/
theorem sigmaBase_not_separable {Q : Type*} [Group Q] [Finite Q]
    (φ : SigmaGroup →* Q) : ∃ b ∈ sigmaBase, φ escapeElement = φ b := by
  have hrel : φ sigmaStable * φ sigmaUnit * (φ sigmaStable)⁻¹
      = (φ sigmaUnit) ^ 2 := by
    rw [← map_inv, ← map_mul, ← map_mul, sigma_square_compression, map_pow]
  obtain ⟨j, hj⟩ := exists_conj_inv_eq_pow hrel
  refine ⟨sigmaUnit ^ (2 ^ j), pow_mem sigmaUnit_mem_sigmaBase _, ?_⟩
  rw [escapeElement_eq, map_mul, map_mul, map_inv, hj, map_pow]

/-! ## The amalgam `Σ *_B (B × C₂)` -/

/-- The order-two lamp is nontrivial. -/
theorem swap_ne_one : (FlipC2.swap : FlipC2) ≠ 1 := by decide

/-- The stable letter in the amalgam; this is
`TerminalQuotientPresentation.amalgamStable`. -/
abbrev amStable : TerminalAmalgam :=
  inAmbient SigmaGroup sigmaBase FlipC2 sigmaStable

/-- The marked translation in the amalgam. -/
abbrev amUnit : TerminalAmalgam :=
  inAmbient SigmaGroup sigmaBase FlipC2 sigmaUnit

/-- The lamp in the amalgam; this is
`TerminalQuotientPresentation.amalgamLampRoot`. -/
abbrev amLamp : TerminalAmalgam :=
  inLamp SigmaGroup sigmaBase FlipC2 FlipC2.swap

theorem am_square_compression : amStable * amUnit * amStable⁻¹ = amUnit ^ 2 := by
  have h : inAmbient SigmaGroup sigmaBase FlipC2
        (sigmaStable * sigmaUnit * sigmaStable⁻¹)
      = inAmbient SigmaGroup sigmaBase FlipC2 (sigmaUnit ^ 2) := by
    rw [sigma_square_compression]
  rw [map_mul, map_mul, map_inv, map_pow] at h
  exact h

/-- The imposed relation of the free-lamp amalgam, at `v₁`. -/
theorem am_lamp_commute : Commute amLamp amUnit :=
  inLamp_commute_inAmbient SigmaGroup sigmaBase FlipC2 FlipC2.swap
    sigmaUnit_mem_sigmaBase

theorem am_escape_eq :
    amStable⁻¹ * amUnit * amStable
      = inAmbient SigmaGroup sigmaBase FlipC2 escapeElement := by
  show (inAmbient SigmaGroup sigmaBase FlipC2 sigmaStable)⁻¹ *
      inAmbient SigmaGroup sigmaBase FlipC2 sigmaUnit *
      inAmbient SigmaGroup sigmaBase FlipC2 sigmaStable
    = inAmbient SigmaGroup sigmaBase FlipC2 escapeElement
  rw [escapeElement_eq, map_mul, map_mul, map_inv]

/-- **The Bass–Serre witness survives.**  The lamp and its `s`-conjugate sit at
distinct cosets of `B`, because `s ∉ B`; this is
`FreeLampReduction.lampCore_ne_one`, whose proof is the reduced-word theorem for
`Monoid.PushoutI`. -/
theorem am_escapeWitness_ne_one :
    amLamp * (amStable⁻¹ * amUnit * amStable) * amLamp⁻¹ *
      (amStable⁻¹ * amUnit * amStable)⁻¹ ≠ 1 := by
  rw [am_escape_eq]
  exact lampCore_ne_one SigmaGroup sigmaBase FlipC2
    escapeElement_not_mem_sigmaBase swap_ne_one

/-- **`Σ *_B (B × C₂)` is not locally embeddable into finite groups.**

The two hypotheses of `not_isLEF_of_squareCompression` are the two structural
relations of the amalgam at `v₁`: the ascending-HNN relation of `Σ`, which on
`v₁` is literally squaring, and the imposed centralizing relation `[d, B] = 1`.
The surviving witness is the Bass–Serre commutator at the half-translation. -/
theorem terminalAmalgam_not_isLEF : ¬ IsLEF TerminalAmalgam :=
  not_isLEF_of_squareCompression amStable amUnit amLamp
    am_square_compression am_lamp_commute am_escapeWitness_ne_one

/-- **`Σ *_B (B × C₂)` is not residually finite** — although its vertex group
`Σ` is (`WitnessVerticalResiduallyFinite.vertical_residuallyFinite`).  Residual
finiteness is not inherited by the amalgam because the edge group `B` is not
separable in `Σ`. -/
theorem terminalAmalgam_not_residuallyFinite :
    ¬ Group.ResiduallyFinite TerminalAmalgam := by
  intro h
  haveI := h
  exact terminalAmalgam_not_isLEF isLEF_of_residuallyFinite

/-- **The local criterion is unusable too.**  The hypothesis of
`LEFSofic.isLEF_of_forall_finset_residuallyFinite` — every finite subset of the
amalgam lies in a residually finite subgroup — is false, since it would deliver
the LEF conclusion just refuted.  This closes the cheapest-looking route by the
same stroke as the global one. -/
theorem not_forall_finset_residuallyFinite :
    ¬ (∀ s : Finset TerminalAmalgam, ∃ H : Subgroup TerminalAmalgam,
        (∀ x ∈ s, x ∈ H) ∧ Group.ResiduallyFinite H) := fun h ↦
  terminalAmalgam_not_isLEF (isLEF_of_forall_finset_residuallyFinite h)

/-! ## The symmetric double -/

/-- **The symmetric double `Σ *_B Σ` is not residually finite.**  It is the
kernel of the retraction `Σ *_B (B × C₂) → C₂`
(`lampKernelFlip_equiv_symmetricDouble`), a subgroup of index two
(`lampKernel_finiteIndex`); residual finiteness would therefore climb to the
amalgam by `LEFSofic.residuallyFinite_of_finiteIndex`, which
`terminalAmalgam_not_residuallyFinite` forbids. -/
theorem symmetricDouble_not_residuallyFinite :
    ¬ Group.ResiduallyFinite (SymmetricDouble SigmaGroup sigmaBase) := by
  intro h
  haveI := h
  obtain ⟨e⟩ := lampKernelFlip_equiv_symmetricDouble SigmaGroup sigmaBase
  haveI : Group.ResiduallyFinite ↥(lampKernel SigmaGroup sigmaBase FlipC2) :=
    residuallyFinite_of_mulEquiv e.symm
  exact terminalAmalgam_not_residuallyFinite
    (residuallyFinite_of_finiteIndex (lampKernel SigmaGroup sigmaBase FlipC2))

/-- **The exact-model status of the amalgam obligation, in one statement.**
The half-translation is invisible to every finite quotient of `Σ` although it
lies outside `B`; the amalgam is neither residually finite nor LEF; the local
residual-finiteness criterion has a false hypothesis; and the symmetric double
is not residually finite.

Consequently `IsOperatorMF (SymmetricDouble SigmaGroup sigmaBase)` — the one
analytic input left open by
`TerminalQuotientPresentation.manuscriptExactRadical_of_terminalIdentification`
— cannot be obtained from `isOperatorMF_of_isLEF`, from
`isLEF_of_residuallyFinite`, from `isLEF_of_forall_finset_residuallyFinite`, or
from any residual-finiteness permanence theorem for amalgamated free products.
It must come from a genuinely approximate matrix model. -/
theorem exactModelRoute_closed :
    escapeElement ∉ sigmaBase ∧
      (∀ {Q : Type} [Group Q] [Finite Q] (φ : SigmaGroup →* Q),
        ∃ b ∈ sigmaBase, φ escapeElement = φ b) ∧
      ¬ Group.ResiduallyFinite TerminalAmalgam ∧
      ¬ IsLEF TerminalAmalgam ∧
      ¬ (∀ s : Finset TerminalAmalgam, ∃ H : Subgroup TerminalAmalgam,
          (∀ x ∈ s, x ∈ H) ∧ Group.ResiduallyFinite H) ∧
      ¬ Group.ResiduallyFinite (SymmetricDouble SigmaGroup sigmaBase) :=
  ⟨escapeElement_not_mem_sigmaBase, fun φ ↦ sigmaBase_not_separable φ,
    terminalAmalgam_not_residuallyFinite, terminalAmalgam_not_isLEF,
    not_forall_finset_residuallyFinite, symmetricDouble_not_residuallyFinite⟩

end

end SymmetricDoubleMF
end GroupApproximation

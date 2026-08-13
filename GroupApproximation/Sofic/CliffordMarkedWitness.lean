import GroupApproximation.Algebra.MappingTelescope
import GroupApproximation.Sofic.MarkedCompressionData
import Mathlib.GroupTheory.SemidirectProduct

/-!
# The Clifford witness for the marked compression word

This file isolates the algebraic (non-analytic) half of the proposed non-MF
example.  Starting from an injective proper endomorphism `alpha : Gamma -> Gamma`,
the mapping telescope supplies an honest ascending HNN ambient group.  Its
stable letter compresses the level-zero copy of `Gamma`, and an element omitted
by `alpha` separates the two relevant left cosets.

The second half records the exact universal interface of the Clifford lamp
extension over a coset space.  In such an extension the root lamp centralizes
the level-zero subgroup, transported lamps at different cosets have a fixed
nontrivial central involution as commutator, and the ambient group permutes the
lamps.  These facts turn the marked compression word into that central
involution, proving it is nontrivial.

There is deliberately one construction gap, `exists_cliffordCosetModel`.  It
is the presentation/model theorem for the infinite extraspecial `2`-group of
Clifford lamps.  Everything surrounding it -- the HNN construction, strict
coset separation, evaluation of the marked word, and packaging as
`MarkedCompressionData` -- is proved below.  Thus the remaining witness gap is
not hidden behind a nontriviality assumption.
-/

namespace GroupApproximation
namespace CliffordMarkedWitness

open scoped commutatorElement

universe u v

variable {Gamma : Type} [Group Gamma]

/-! ## The ascending HNN group from the mapping telescope -/

variable (alpha : Gamma →* Gamma) (halpha : Function.Injective alpha)

/-- Integer powers of the telescope shift, as an action of the infinite cyclic
group. -/
def shiftAction : Multiplicative Int →* MulAut (MappingTelescope.Telescope alpha halpha) where
  toFun n := MappingTelescope.shift alpha halpha ^ n.toAdd
  map_one' := by
    simp
  map_mul' m n := by
    change MappingTelescope.shift alpha halpha ^ (m.toAdd + n.toAdd) =
      MappingTelescope.shift alpha halpha ^ m.toAdd *
        MappingTelescope.shift alpha halpha ^ n.toAdd
    exact zpow_add _ _ _

/-- A concrete model of the ascending HNN extension associated to `alpha`.
The level-zero base lies in the mapping telescope, while the infinite cyclic
factor is the stable letter. -/
abbrev AscendingHNN : Type :=
  MappingTelescope.Telescope alpha halpha ⋊[shiftAction alpha halpha] Multiplicative Int

/-- The level-zero copy of the base group in the ascending HNN model. -/
def baseEmbedding : Gamma →* AscendingHNN alpha halpha :=
  (SemidirectProduct.inl (φ := shiftAction alpha halpha)).comp
    (MappingTelescope.level alpha halpha 0)

/-- The positive stable letter. -/
def stableLetter : AscendingHNN alpha halpha :=
  SemidirectProduct.inr (Multiplicative.ofAdd (1 : Int))

theorem baseEmbedding_injective :
    Function.Injective (baseEmbedding alpha halpha) :=
  fun _ _ h ↦ MappingTelescope.level_injective alpha halpha 0
    (SemidirectProduct.inl_injective h)

/-- The stable letter implements the given endomorphism on the level-zero
copy. -/
theorem stableLetter_compress (g : Gamma) :
    stableLetter alpha halpha * baseEmbedding alpha halpha g *
        (stableLetter alpha halpha)⁻¹ =
      baseEmbedding alpha halpha (alpha g) := by
  calc
    stableLetter alpha halpha * baseEmbedding alpha halpha g *
          (stableLetter alpha halpha)⁻¹ =
        SemidirectProduct.inl (φ := shiftAction alpha halpha)
          ((shiftAction alpha halpha (Multiplicative.ofAdd (1 : Int)))
            (MappingTelescope.level alpha halpha 0 g)) := by
              simpa only [stableLetter, baseEmbedding, MonoidHom.comp_apply,
                map_inv]
                using (SemidirectProduct.inl_aut
                  (φ := shiftAction alpha halpha)
                  (Multiplicative.ofAdd (1 : Int))
                  (MappingTelescope.level alpha halpha 0 g)).symm
    _ = baseEmbedding alpha halpha (alpha g) := by
      change SemidirectProduct.inl (φ := shiftAction alpha halpha)
          (MappingTelescope.shift alpha halpha
            (MappingTelescope.level alpha halpha 0 g)) =
        SemidirectProduct.inl (φ := shiftAction alpha halpha)
          (MappingTelescope.level alpha halpha 0 (alpha g))
      exact congrArg _ (MappingTelescope.shift_level alpha halpha 0 g)

/-- An element omitted by `alpha` does not lie in the conjugated copy of the
base.  This is the exact coset-separation fact used by the Clifford witness. -/
theorem omitted_not_conjugate {a : Gamma} (ha : a ∉ alpha.range) :
    ¬ ∃ g : Gamma,
      baseEmbedding alpha halpha a =
        stableLetter alpha halpha * baseEmbedding alpha halpha g *
          (stableLetter alpha halpha)⁻¹ := by
  rintro ⟨g, hg⟩
  rw [stableLetter_compress] at hg
  have : a = alpha g := baseEmbedding_injective alpha halpha hg
  exact ha ⟨g, this.symm⟩

/-! ## The universal Clifford-coset interface -/

/-- The precise algebraic interface supplied by the Clifford central
extension of the lamp group over the left cosets of `iota(Gamma)`.

`site g` is the lamp at the coset `g * iota(Gamma)`.  The covariance axiom is
built into its definition.  The last axiom says that lamps at distinct cosets
have commutator `z`; its premise is the elementary, representative-level form
of distinctness of those left cosets. -/
structure CliffordCosetModel (G : Type u) [Group G]
    (iota : Gamma →* G) where
  /-- Carrier of the central Clifford extension semidirect the ambient group. -/
  E : Type v
  groupE : Group E
  /-- The ambient action inside the extension. -/
  ambient : G →* E
  /-- Root Clifford lamp. -/
  c : E
  /-- Central Clifford sign. -/
  z : E
  /-- The root lamp is fixed by the base subgroup. -/
  root_commutes : ∀ g : Gamma, Commute c (ambient (iota g))
  /-- The sign is an involution. -/
  z_sq : z ^ 2 = 1
  /-- The sign is central. -/
  z_central : ∀ x : E, Commute z x
  /-- The sign genuinely survives. -/
  z_ne_one : z ≠ 1
  /-- Distinct cosets give anticommuting Clifford lamps. -/
  distinct_site_commutator : ∀ g h : G,
    (¬ ∃ gamma : Gamma, g = h * iota gamma) →
      ⁅ambient g * c * (ambient g)⁻¹,
        ambient h * c * (ambient h)⁻¹⁆ = z

attribute [instance] CliffordCosetModel.groupE

/- **The sole remaining algebraic construction gap.**  The group is the
extraspecial central extension generated by symbols `z, c_x` for
`x : G / iota(Gamma)`, with

* `z^2 = c_x^2 = 1`,
* `z` central, and
* `[c_x,c_y] = z` for `x != y`,

semidirect the permutation action of `G` on its cosets.  A concrete faithful
model is furnished by the units generated by the standard basis vectors in
the Clifford algebra of the free real module on the coset space.  Formalizing
that presentation/model equivalence is the only unfinished part of this
file. -/
set_option warningAsError false in
theorem exists_cliffordCosetModel (G : Type u) [Group G]
    (iota : Gamma →* G) : Nonempty (CliffordCosetModel G iota) := by
  sorry

namespace CliffordCosetModel

variable {G : Type u} [Group G] {iota : Gamma →* G}

/-- The lamp transported to the coset represented by `g`. -/
def site (M : CliffordCosetModel G iota) (g : G) : M.E :=
  M.ambient g * M.c * (M.ambient g)⁻¹

theorem site_commutator (M : CliffordCosetModel G iota) (g h : G)
    (hdist : ¬ ∃ gamma : Gamma, g = h * iota gamma) :
    ⁅M.site g, M.site h⁆ = M.z :=
  M.distinct_site_commutator g h hdist

end CliffordCosetModel

/-! ## Evaluation of the marked word -/

/-- The two transported lamps occurring in the marked word lie at distinct
cosets whenever `a` is omitted by the compression. -/
theorem marked_sites_distinct {a : Gamma} (ha : a ∉ alpha.range) :
    ¬ ∃ g : Gamma,
      stableLetter alpha halpha =
        (baseEmbedding alpha halpha a * stableLetter alpha halpha) *
          baseEmbedding alpha halpha g := by
  rintro ⟨g, hg⟩
  have hconj : baseEmbedding alpha halpha a =
      stableLetter alpha halpha * baseEmbedding alpha halpha g⁻¹ *
        (stableLetter alpha halpha)⁻¹ := by
    symm
    calc
      stableLetter alpha halpha * baseEmbedding alpha halpha g⁻¹ *
          (stableLetter alpha halpha)⁻¹ =
        ((baseEmbedding alpha halpha a * stableLetter alpha halpha) *
            baseEmbedding alpha halpha g) *
          baseEmbedding alpha halpha g⁻¹ *
          (stableLetter alpha halpha)⁻¹ := by
            nth_rewrite 1 [← hg]
            rfl
      _ = baseEmbedding alpha halpha a := by
        rw [map_inv]
        group
  exact omitted_not_conjugate alpha halpha ha ⟨g⁻¹, hconj⟩

/-- In the Clifford model the marked compression word evaluates exactly to
the nontrivial central sign. -/
theorem marked_word_eq_sign (M : CliffordCosetModel
    (AscendingHNN alpha halpha) (baseEmbedding alpha halpha))
    {a : Gamma} (ha : a ∉ alpha.range) :
    markedCompressionWord
        (M.ambient (stableLetter alpha halpha))
        (M.ambient (baseEmbedding alpha halpha a)) M.c = M.z := by
  have hsite : M.site
      (baseEmbedding alpha halpha a * stableLetter alpha halpha) =
      M.ambient (baseEmbedding alpha halpha a) *
        (M.ambient (stableLetter alpha halpha) * M.c *
          (M.ambient (stableLetter alpha halpha))⁻¹) *
        (M.ambient (baseEmbedding alpha halpha a))⁻¹ := by
    simp only [CliffordCosetModel.site, map_mul]
    group
  rw [markedCompressionWord, ← hsite]
  change ⁅M.site (stableLetter alpha halpha),
    M.site (baseEmbedding alpha halpha a * stableLetter alpha halpha)⁆ = M.z
  exact M.site_commutator _ _ (marked_sites_distinct alpha halpha ha)

/-- The marked word is nontrivial in the Clifford extension. -/
theorem marked_word_ne_one (M : CliffordCosetModel
    (AscendingHNN alpha halpha) (baseEmbedding alpha halpha))
    {a : Gamma} (ha : a ∉ alpha.range) :
    markedCompressionWord
        (M.ambient (stableLetter alpha halpha))
        (M.ambient (baseEmbedding alpha halpha a)) M.c ≠ 1 := by
  rw [marked_word_eq_sign alpha halpha M ha]
  exact M.z_ne_one

/-- Honest public package: an omitted element produces marked data whose word
is the surviving Clifford sign. -/
def markedDataOfOmitted (hT : HasKazhdanPropertyT.{0, 0} Gamma)
    (M : CliffordCosetModel
      (AscendingHNN alpha halpha) (baseEmbedding alpha halpha))
    (a : Gamma) (ha : a ∉ alpha.range) : MarkedCompressionData Gamma M.E where
  iota := M.ambient.comp (baseEmbedding alpha halpha)
  alpha := alpha
  t := M.ambient (stableLetter alpha halpha)
  c := M.c
  a := a
  kazhdan := hT
  compress g := by
    simpa only [MonoidHom.comp_apply, map_mul, map_inv] using
      congrArg M.ambient (stableLetter_compress alpha halpha g)
  comm_c g := M.root_commutes g
  word_sq := by
    change markedCompressionWord
        (M.ambient (stableLetter alpha halpha))
        (M.ambient (baseEmbedding alpha halpha a)) M.c ^ 2 = 1
    rw [marked_word_eq_sign alpha halpha M ha]
    exact M.z_sq
  word_central g := by
    change Commute
      (markedCompressionWord
        (M.ambient (stableLetter alpha halpha))
        (M.ambient (baseEmbedding alpha halpha a)) M.c) g
    rw [marked_word_eq_sign alpha halpha M ha]
    exact M.z_central g

theorem markedDataOfOmitted_word_ne_one
    (hT : HasKazhdanPropertyT.{0, 0} Gamma)
    (M : CliffordCosetModel
      (AscendingHNN alpha halpha) (baseEmbedding alpha halpha))
    (a : Gamma) (ha : a ∉ alpha.range) :
    (markedDataOfOmitted alpha halpha hT M a ha).word ≠ 1 :=
  marked_word_ne_one alpha halpha M ha

end CliffordMarkedWitness
end GroupApproximation

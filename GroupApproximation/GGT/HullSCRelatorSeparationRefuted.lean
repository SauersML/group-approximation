import GroupApproximation.GGT.HullSCRelatorSeparationValues
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# `HullSC.RelatorSeparation` is false: it lost Olshanskii's exclusion clause

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, Groups
Geom. Dyn. 10 (2016) 1077-1119, §6, after Olshanskii.

## Where the extra strength came from

`HullSC.RelWord.IsPiece` carries Olshanskii's exclusion clause in full: for `u`
to be an `eps`-piece of `w` the second word `w'` must be a *different* member of
the family, `w' ≠ w`.  `HullSC.RelWord.pieces_small_of_longMatch` destructures a
piece and drops that clause, so the hypothesis it asks for -- and therefore
`HullSC.RelatorChoice` and `HullSC.RelatorSeparation`, which are written to
match it -- quantifies over `w` and `w'` with no constraint, the diagonal
`w' = w` included.

On the diagonal the statement is no longer about small cancellation.  Take
`w = w'` and `u₀ = u₀'` the whole word: the match hypothesis reads
`V = y V z` for `V` the element the relator names, and the conclusion reads
`V = y V y⁻¹`, that is, `z = y⁻¹`, that is, `y` centralizes `V`.  So the leaf
demands that every `y` in the `eps`-ball whose `V`-conjugate is again in the
`eps`-ball commute with `V`.  Nothing in Hull's §6 proves that, and it is false.

## The refutation

`not_relatorSeparation_of_inverted` is the statement in full: on any Hull
instance carrying an element `y` of the `eps`-ball with

* `y` commuting with the loxodromic `E.lox`,
* `t · y · t⁻¹ = y⁻¹` for the target `t`, and
* `y ≠ y⁻¹`,

`HullSC.RelatorSeparation` fails.  The three conditions are invariant under
every choice the statement leaves free: the relator names `t⁻¹ E.lox^{Σ mᵢ}`
whatever the spelling `p` of `t⁻¹` and whatever the exponents, and `y` commutes
with `E.lox^{Σ mᵢ}`, so `y` centralizes the relator's value if and only if it
commutes with `t`, which the second condition forbids.  The constant `B` is
beaten by taking `L = B + 1`.

`not_relatorSeparation_of_inverted_lox` is the case `y = E.lox`, and it needs no
side condition at all beyond

> some `t` inverts the loxodromic: `t · E.lox · t⁻¹ = E.lox⁻¹`,

because the statement quantifies over `eps`, so `eps` may be taken to be
`|E.lox|` itself, and because a loxodromic element has infinite order and is
therefore not equal to its own inverse.

Inversion of a loxodromic is not exotic.  It happens exactly when the maximal
elementary subgroup `E(g)` surjects onto the infinite dihedral group rather than
onto `ℤ`, and `D∞ * ℤ` -- virtually free, hence hyperbolic, hence acylindrically
hyperbolic over any finite generating set, with no nontrivial finite normal
subgroup, so with the whole group suitable -- realizes it with `E(g) = D∞` the
first factor and the reflection as `t`.  Over a torsion-free ambient group it
cannot happen: a torsion-free virtually cyclic group is infinite cyclic, so no
element inverts a loxodromic, which is why the leaf survived a torsion-free
reading.

`inversion_configuration_dihedral` is the model test for the three conditions,
in `DihedralGroup 3`; `dihedral_sr_conj_r` proves the inversion identity for
every `n`, `DihedralGroup 0` -- the infinite dihedral group, where the rotation
inverted has infinite order -- included.

## What survives

Only the diagonal is refuted.  Restoring Olshanskii's `w' ≠ w`, which
`RelWord.IsPiece` never dropped, restores a statement this argument does not
touch, and `GGT/HullSCRelatorSeparationRepair.lean` proves
`HullSC.HullRelatorStatement` from it.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

namespace RelWord

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The diagonal instance the leaf forgot to exclude.**

At `w = w' = u₀ = u₀' = v` the match hypothesis of the separation clause is
`listVal v = y · listVal v · z` and its conclusion is
`listVal v = y · listVal v · y⁻¹`.  So a pair `y, z` in the `eps`-ball fixing
the relator's value from the two sides, with `y` not centralizing that value,
refutes the clause outright -- at every constant `B` shorter than the relator,
and with no geometry involved.

`RelWord.IsPiece` excludes this instance through its clause `v' ≠ v`, which
`pieces_small_of_longMatch` discards. -/
theorem not_longMatch_of_not_commute {D : GGT.RelGenSet G Λ}
    {v : List (GGT.RelLetter G Λ)} {eps B : ℕ} (y z : G)
    (hB : B < v.length) (hy : wordNorm D.alphabet.carrier y ≤ eps)
    (hz : wordNorm D.alphabet.carrier z ≤ eps)
    (hfix : y * GGT.RelLetter.listVal v * z = GGT.RelLetter.listVal v)
    (hmove : y * GGT.RelLetter.listVal v * y⁻¹ ≠ GGT.RelLetter.listVal v) :
    ¬ (∀ w w' u u' : List (GGT.RelLetter G Λ), Sym v w → Sym v w' →
        (∃ s, w = u ++ s) → (∃ s', w' = u' ++ s') → B < u.length →
          ∀ y' z' : G, wordNorm D.alphabet.carrier y' ≤ eps →
            wordNorm D.alphabet.carrier z' ≤ eps →
            GGT.RelLetter.listVal u' = y' * GGT.RelLetter.listVal u * z' →
              GGT.RelLetter.listVal w'
                = y' * GGT.RelLetter.listVal w * y'⁻¹) := by
  intro hmatch
  refine hmove ?_
  exact (hmatch v v v v Sym.base Sym.base ⟨[], (List.append_nil v).symm⟩
    ⟨[], (List.append_nil v).symm⟩ hB y z hy hz hfix.symm).symm

end RelWord

/-! ## The algebra of an inverting target -/

section Inversion

variable {G : Type u} [Group G]

/-- **An element inverted by `t` fixes `t⁻¹ a^M` from both sides**, when it
commutes with `a`.

`t y t⁻¹ = y⁻¹` says `y t⁻¹ = t⁻¹ y⁻¹`, so `y t⁻¹ y = t⁻¹`; and `y` passes
through `a^M` by hypothesis.  This is the match hypothesis of the separation
clause, met with `z = y`. -/
theorem mul_relatorValue_self {a t y : G} (hc : Commute a y)
    (hinv : t * y * t⁻¹ = y⁻¹) (M : ℕ) :
    y * (t⁻¹ * a ^ M) * y = t⁻¹ * a ^ M := by
  have hcm : a ^ M * y = y * a ^ M := (hc.pow_left M).eq
  have hyt : y * t⁻¹ = t⁻¹ * y⁻¹ := by
    rw [← hinv, mul_assoc t y t⁻¹, inv_mul_cancel_left]
  have h1 : y * (t⁻¹ * a ^ M) * y = y * t⁻¹ * (a ^ M * y) := by
    rw [← mul_assoc y t⁻¹ (a ^ M), mul_assoc (y * t⁻¹) (a ^ M) y]
  rw [h1, hcm, hyt, mul_assoc t⁻¹ y⁻¹ (y * a ^ M), inv_mul_cancel_left]

/-- **The same element does not centralize `t⁻¹ a^M`**, when it is not an
involution.

`y (t⁻¹ a^M) y⁻¹ = t⁻¹ y⁻¹ y⁻¹ a^M`, so centralizing would force `y⁻¹ y⁻¹ = 1`,
that is `y = y⁻¹`.  This is the conclusion of the separation clause, refuted. -/
theorem relatorValue_conj_ne {a t y : G} (hc : Commute a y)
    (hinv : t * y * t⁻¹ = y⁻¹) (hne : y ≠ y⁻¹) (M : ℕ) :
    y * (t⁻¹ * a ^ M) * y⁻¹ ≠ t⁻¹ * a ^ M := by
  intro hcon
  have hcm : a ^ M * y⁻¹ = y⁻¹ * a ^ M := ((hc.inv_right).pow_left M).eq
  have hyt : y * t⁻¹ = t⁻¹ * y⁻¹ := by
    rw [← hinv, mul_assoc t y t⁻¹, inv_mul_cancel_left]
  have h1 : y * (t⁻¹ * a ^ M) * y⁻¹ = y * t⁻¹ * (a ^ M * y⁻¹) := by
    rw [← mul_assoc y t⁻¹ (a ^ M), mul_assoc (y * t⁻¹) (a ^ M) y⁻¹]
  rw [h1, hcm, hyt, mul_assoc t⁻¹ y⁻¹ (y⁻¹ * a ^ M),
    ← mul_assoc y⁻¹ y⁻¹ (a ^ M)] at hcon
  have h2 : y⁻¹ * y⁻¹ * a ^ M = a ^ M := mul_left_cancel hcon
  have h3 : y⁻¹ * y⁻¹ * a ^ M = 1 * a ^ M := by
    rw [one_mul]
    exact h2
  have h4 : y⁻¹ * y⁻¹ = 1 := mul_right_cancel h3
  have h5 : (y⁻¹)⁻¹ = y⁻¹ := inv_eq_of_mul_eq_one_right h4
  rw [inv_inv] at h5
  exact hne h5

end Inversion

/-! ## The leaf, refuted -/

/-- **`HullSC.RelatorSeparation` fails on any Hull instance with a short element
inverted by the target.**

Given `y` with `|y| ≤ eps`, commuting with `E.lox` and satisfying
`t y t⁻¹ = y⁻¹` and `y ≠ y⁻¹`, take `eps = |y|` and `L = B + 1` against the
constant `B` the statement produces.  Whatever spelling `p` of `t⁻¹` and
whatever exponents `ms` come back, the relator names `t⁻¹ E.lox^{Σ mᵢ}`
(`listVal_relatorWord`), and it is longer than `B` (`length_relatorWord`).  Then
`mul_relatorValue_self` supplies the match with `z = y`,
`relatorValue_conj_ne` refutes the conclusion, and
`RelWord.not_longMatch_of_not_commute` puts the two together on the diagonal
`w = w'`.

Nothing here bounds the exponents or the spelling, so no choice available to §6
avoids it: the obstruction is the missing `w' ≠ w`, not the relator. -/
theorem not_relatorSeparation_of_inverted {G : Type u} [Group G]
    (A : HullGeneratingSet G) (N : Subgroup G) (E : HypEmbeddedCore A N)
    (hN : Suitable A.alphabet N) (t : G) {y : G} (hc : Commute E.lox y)
    (hinv : t * y * t⁻¹ = y⁻¹) (hne : y ≠ y⁻¹) : ¬ RelatorSeparation.{u} := by
  intro hsep
  obtain ⟨B, hB⟩ := hsep A N E hN t
    (wordNorm E.rel.alphabet.carrier y) 0
  obtain ⟨p, ms, -, hpprod, hlen, -, hmatch⟩ := hB (B + 1)
  have hval : GGT.RelLetter.listVal (relatorWord p E.lox ms)
      = t⁻¹ * E.lox ^ ms.sum := by
    rw [listVal_relatorWord, hpprod]
  have hlong : B < (relatorWord p E.lox ms).length := by
    rw [length_relatorWord]
    omega
  refine RelWord.not_longMatch_of_not_commute (D := E.rel)
    (v := relatorWord p E.lox ms)
    (eps := wordNorm E.rel.alphabet.carrier y) (B := B)
    y y hlong le_rfl le_rfl ?_ ?_ hmatch
  · rw [hval]
    exact mul_relatorValue_self hc hinv ms.sum
  · rw [hval]
    exact relatorValue_conj_ne hc hinv hne ms.sum

/-- **`HullSC.RelatorSeparation` fails on any Hull instance whose loxodromic is
inverted.**

The case `y = E.lox` of `not_relatorSeparation_of_inverted`.  Both side
conditions are free: `E.lox` commutes with itself, and `E.lox ≠ E.lox⁻¹` because
a loxodromic element has infinite order
(`HullGeometry.not_isOfFinOrder_of_isLoxodromic`), while the bound on `|y|` is
free because the statement quantifies over `eps` and `eps = |E.lox|` is
admissible.

So the leaf is refuted by the single hypothesis that some element inverts the
loxodromic of the hyperbolically embedded core -- which is what happens whenever
the maximal elementary subgroup `E(E.lox)` surjects onto the infinite dihedral
group, as in `D∞ * ℤ`. -/
theorem not_relatorSeparation_of_inverted_lox {G : Type u} [Group G]
    (A : HullGeneratingSet G) (N : Subgroup G) (E : HypEmbeddedCore A N)
    (hN : Suitable A.alphabet N) (t : G)
    (hinv : t * E.lox * t⁻¹ = E.lox⁻¹) : ¬ RelatorSeparation.{u} := by
  refine not_relatorSeparation_of_inverted A N E hN t (Commute.refl E.lox)
    hinv ?_
  intro hcon
  refine not_isOfFinOrder_of_isLoxodromic E.lox_isLoxodromic ?_
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by omega, ?_⟩
  rw [pow_two]
  exact mul_eq_one_iff_eq_inv.mpr hcon

/-! ## The configuration is realizable -/

/-- **A reflection inverts every rotation**, in every dihedral group, the
infinite one `DihedralGroup 0` included. -/
theorem dihedral_sr_conj_r (n : ℕ) (i : ZMod n) :
    DihedralGroup.sr (0 : ZMod n) * DihedralGroup.r i
        * (DihedralGroup.sr (0 : ZMod n))⁻¹ = (DihedralGroup.r i)⁻¹ := by
  rw [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
    DihedralGroup.inv_r, zero_add, zero_sub]

/-- **The three conditions of `not_relatorSeparation_of_inverted` are jointly
satisfiable**, so the refutation is not vacuous: in `DihedralGroup 3` the
rotation `r 1` commutes with itself, is inverted by the reflection `sr 0`, and
is not its own inverse.

The same configuration with `n = 0` -- the infinite dihedral group -- has `r 1`
of infinite order, which is the shape it takes inside the maximal elementary
subgroup of a loxodromic element. -/
theorem inversion_configuration_dihedral :
    Commute (DihedralGroup.r (1 : ZMod 3)) (DihedralGroup.r (1 : ZMod 3)) ∧
      DihedralGroup.sr (0 : ZMod 3) * DihedralGroup.r (1 : ZMod 3)
          * (DihedralGroup.sr (0 : ZMod 3))⁻¹
        = (DihedralGroup.r (1 : ZMod 3))⁻¹ ∧
      DihedralGroup.r (1 : ZMod 3) ≠ (DihedralGroup.r (1 : ZMod 3))⁻¹ :=
  ⟨Commute.refl _, dihedral_sr_conj_r 3 (1 : ZMod 3), by decide⟩

end HullSC
end GroupApproximation

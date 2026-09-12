import GroupApproximation.Analysis.CompressionTraceModel
import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Sofic.NormTraceGap

/-!
# The compression defect is `0` or `1`, and what that forces

`Analysis.CompressionTraceModel` reduced quasidiagonality of the canonical
trace, *for compression models*, to a single clause: the operator-norm
multiplicativity defect must tend to `0`.  This file computes that defect at
one well-chosen pair and finds that it never becomes small.

## The computation

Take the pair `(λ_{g⁻¹}, λ_g)`, whose product is the identity.  The
compression is unital, so the defect is

```text
    D  =  1  −  φ_e(λ_{g⁻¹}) φ_e(λ_g),
```

and both factors are incidence matrices of the enumeration
(`compressionMap_leftRegular_apply`).  Multiplying them out gives a **diagonal
projection**:

```text
    D_{pq}  =  0                       if  g · e q ∈ range e,
    D_{qq}  =  1                       otherwise.
```

So `D` is the orthogonal projection onto the coordinates that `g` moves out of
the compressed window (`inverseDefect_apply_of_mem_range`,
`inverseDefect_diag_of_not_mem_range`).  Its norm is therefore `1` if any
coordinate leaves and `0` if none does, and there is nothing in between
(`norm_inverseDefect_eq_zero_or_one_le`).

This is the operator-norm counterpart of the permutation rigidity of
`Analysis.AmenableQuasidiagonal`, stated at the maps quasidiagonality actually
asks for rather than at permutation matrices.  A Følner set makes the
*proportion* of escaping coordinates small; the operator norm cannot see a
proportion, only whether the set of escaping coordinates is empty.

## The consequence

A defect below `1` is a defect equal to `0`, which says `g · F ⊆ F` for the
window `F = range e`; as `F` is finite and left translation is injective, that
is `g · F = F`.  The elements with that property form a subgroup
(`leftStabilizer`), and that subgroup injects into `F`, so it is **finite**.
Hence:

> if the compressions of a family are asymptotically multiplicative, then
> every finite subset of `G` lies in a finite subgroup ---
> `isLocallyFiniteGroup_of_isAsymptoticallyMultiplicative`.

The compression route to the conclusion of Tikuisis--White--Winter therefore
certifies **only** locally finite groups.  `Analysis.CompressionTraceLocallyFinite` proves the
converse, so the characterization is exact, and
`Analysis.TikuisisWhiteWinterUnconditional` records what that leaves of the
printed sentence.

## Manuscript status

Certifies no manuscript step.  It is a negative result about a proof strategy,
and it is unconditional.
-/

namespace GroupApproximation
namespace Quasidiagonal

open Filter ReducedGroupCStarTrace
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

universe u

variable {G : Type u} [Group G]

local instance rigidityDecidableEq : DecidableEq G := Classical.decEq G

/-! ## The defect at the pair `(λ_{g⁻¹}, λ_g)` -/

/-- Translations of the reduced algebra multiply as they do in the group. -/
theorem reducedLeftRegular_inv_mul_self (g : G) :
    reducedLeftRegular G g⁻¹ * reducedLeftRegular G g = 1 := by
  apply Subtype.ext
  show leftRegularOperator G g⁻¹ * leftRegularOperator G g = 1
  rw [leftRegularOperator_mul, inv_mul_cancel, leftRegularOperator_one]

/-- **The multiplicativity defect of a compression at the pair
`(λ_{g⁻¹}, λ_g)`.**  This pair is chosen because its product is the identity,
on which the compression is exact, so the defect is the difference of two
explicitly computable matrices. -/
def inverseDefect {k : ℕ} (e : Fin k → G) (g : G) :
    Matrix (naturalFiniteModel k) (naturalFiniteModel k) ℂ :=
  compressionMap e (reducedLeftRegular G g⁻¹ * reducedLeftRegular G g)
    - compressionMap e (reducedLeftRegular G g⁻¹)
      * compressionMap e (reducedLeftRegular G g)

/-- The defect, before any case analysis: the identity matrix minus the
product of the two incidence matrices. -/
theorem inverseDefect_apply {k : ℕ} {e : Fin k → G}
    (he : Function.Injective e) (g : G) (p q : Fin k) :
    inverseDefect e g p q
      = (1 : Matrix (naturalFiniteModel k) (naturalFiniteModel k) ℂ) p q
        - ∑ z : Fin k, incidence e g⁻¹ p z * incidence e g z q := by
  have hprod : ∀ z : Fin k,
      compressionMap e (reducedLeftRegular G g⁻¹) p z
          * compressionMap e (reducedLeftRegular G g) z q
        = incidence e g⁻¹ p z * incidence e g z q := by
    intro z
    rw [compressionMap_leftRegular_apply, compressionMap_leftRegular_apply]
  show (compressionMap e (reducedLeftRegular G g⁻¹ * reducedLeftRegular G g)
      - compressionMap e (reducedLeftRegular G g⁻¹)
        * compressionMap e (reducedLeftRegular G g)) p q = _
  rw [Matrix.sub_apply, reducedLeftRegular_inv_mul_self, compressionMap_one he,
    Matrix.mul_apply, Finset.sum_congr rfl fun z _ ↦ hprod z]

/-- **A coordinate that stays inside the window contributes no defect.**

If `g · e q` is again one of the compressed coordinates, say `e z₀`, then the
sum over `z` collapses at `z₀` --- injectivity of `e` kills every other term
--- and what survives is `[e p = e q] = [p = q]`, which is exactly the entry
of the identity matrix that the defect subtracts it from. -/
theorem inverseDefect_apply_of_mem_range {k : ℕ} {e : Fin k → G}
    (he : Function.Injective e) (g : G) {q : Fin k}
    (hq : g * e q ∈ Set.range e) (p : Fin k) :
    inverseDefect e g p q = 0 := by
  obtain ⟨z₀, hz₀⟩ := hq
  have hcollapse : (∑ z : Fin k, incidence e g⁻¹ p z * incidence e g z q)
      = (1 : Matrix (naturalFiniteModel k) (naturalFiniteModel k) ℂ) p q := by
    rw [Finset.sum_eq_single z₀]
    · rw [incidence_eq_one hz₀, mul_one]
      by_cases hpq : p = q
      · subst hpq
        rw [incidence_eq_one (by rw [hz₀, inv_mul_cancel_left]),
          Matrix.one_apply_eq]
      · rw [incidence_eq_zero
          (fun hc ↦ hpq (he (by rw [hc, hz₀, inv_mul_cancel_left]))),
          Matrix.one_apply_ne hpq]
    · intro z _ hz
      have hne : ¬ (e z = g * e q) := fun hc ↦ hz (he (hc.trans hz₀.symm))
      rw [incidence_eq_zero hne, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ z₀) hcon
  rw [inverseDefect_apply he, hcollapse, sub_self]

/-- **A coordinate that leaves the window keeps the whole column of the
identity.**

If `g · e q` is not a compressed coordinate then every term of the sum
vanishes --- the second incidence factor is `0` for every `z` --- so the
defect is the `q`-th column of `1`. -/
theorem inverseDefect_apply_of_not_mem_range {k : ℕ} {e : Fin k → G}
    (he : Function.Injective e) (g : G) {q : Fin k}
    (hq : g * e q ∉ Set.range e) (p : Fin k) :
    inverseDefect e g p q
      = (1 : Matrix (naturalFiniteModel k) (naturalFiniteModel k) ℂ) p q := by
  have hzero : (∑ z : Fin k, incidence e g⁻¹ p z * incidence e g z q) = 0 := by
    refine Finset.sum_eq_zero fun z _ ↦ ?_
    have hne : ¬ (e z = g * e q) := fun hc ↦ hq ⟨z, hc⟩
    rw [incidence_eq_zero hne, mul_zero]
  rw [inverseDefect_apply he, hzero, sub_zero]

/-- **A coordinate that leaves the window contributes a full diagonal `1`.** -/
theorem inverseDefect_diag_of_not_mem_range {k : ℕ} {e : Fin k → G}
    (he : Function.Injective e) (g : G) {q : Fin k}
    (hq : g * e q ∉ Set.range e) :
    inverseDefect e g q q = 1 := by
  rw [inverseDefect_apply_of_not_mem_range he g hq q, Matrix.one_apply_eq]

/-- Off the diagonal an escaping coordinate contributes nothing either. -/
theorem inverseDefect_apply_of_not_mem_range_of_ne {k : ℕ} {e : Fin k → G}
    (he : Function.Injective e) (g : G) {q : Fin k}
    (hq : g * e q ∉ Set.range e) {p : Fin k} (hpq : p ≠ q) :
    inverseDefect e g p q = 0 := by
  rw [inverseDefect_apply_of_not_mem_range he g hq p, Matrix.one_apply_ne hpq]

/-! ## The dichotomy -/

/-- **No coordinate escapes: the defect vanishes.**  Exact multiplicativity at
the pair, not approximate. -/
theorem inverseDefect_eq_zero_of_forall_mem_range {k : ℕ} {e : Fin k → G}
    (he : Function.Injective e) {g : G}
    (hg : ∀ q : Fin k, g * e q ∈ Set.range e) :
    inverseDefect e g = 0 := by
  funext p q
  exact inverseDefect_apply_of_mem_range he g (hg q) p

/-- **One coordinate escapes: the defect has norm at least `1`.**

The escaping coordinate contributes a diagonal entry equal to `1`, and every
entry of a matrix is bounded by its operator norm
(`normSq_entry_le_sq_l2_opNorm`).  The bound is insensitive to how few
coordinates escape: one is enough. -/
theorem one_le_norm_inverseDefect_of_not_mem_range {k : ℕ} {e : Fin k → G}
    (he : Function.Injective e) {g : G} {q : Fin k}
    (hq : g * e q ∉ Set.range e) :
    1 ≤ ‖inverseDefect e g‖ := by
  have hentry : Complex.normSq (inverseDefect e g q q) = 1 := by
    rw [inverseDefect_diag_of_not_mem_range he g hq]
    simp
  have hbound := normSq_entry_le_sq_l2_opNorm (naturalFiniteModel k)
    (inverseDefect e g) q q
  rw [hentry] at hbound
  nlinarith [norm_nonneg (inverseDefect e g)]

/-- **The dichotomy.**  The multiplicativity defect of a compression at the
pair `(λ_{g⁻¹}, λ_g)` is either `0` or at least `1`.  There is no regime of
small positive defect, so an asymptotic hypothesis on it is in fact an exact
one from some stage on. -/
theorem norm_inverseDefect_eq_zero_or_one_le {k : ℕ} {e : Fin k → G}
    (he : Function.Injective e) (g : G) :
    ‖inverseDefect e g‖ = 0 ∨ 1 ≤ ‖inverseDefect e g‖ := by
  by_cases hall : ∀ q : Fin k, g * e q ∈ Set.range e
  · left
    rw [inverseDefect_eq_zero_of_forall_mem_range he hall, norm_zero]
  · right
    obtain ⟨q, hq⟩ := not_forall.mp hall
    exact one_le_norm_inverseDefect_of_not_mem_range he hq

/-- **A defect below `1` is an invariance statement.**  This is the form the
group-level argument consumes. -/
theorem mem_range_of_norm_inverseDefect_lt_one {k : ℕ} {e : Fin k → G}
    (he : Function.Injective e) {g : G} (h : ‖inverseDefect e g‖ < 1)
    (q : Fin k) : g * e q ∈ Set.range e := by
  by_contra hq
  exact absurd h (not_lt.mpr (one_le_norm_inverseDefect_of_not_mem_range he hq))

/-! ## Windows that a set of translations preserves -/

/-- **The elements that permute a finite subset of the group by left
translation.**  A submonoid for trivial reasons; a subgroup because a finite
set mapped into itself injectively is mapped onto itself. -/
def leftStabilizer (S : Finset G) : Subgroup G where
  carrier := {h : G | ∀ x ∈ S, h * x ∈ S}
  one_mem' := by
    intro x hx
    rwa [one_mul]
  mul_mem' := by
    intro h h' hh hh' x hx
    rw [mul_assoc]
    exact hh _ (hh' x hx)
  inv_mem' := by
    intro h hh
    have hsub : S.image (fun x ↦ h * x) ⊆ S := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact hh x hx
    have hcard : S.card ≤ (S.image (fun x ↦ h * x)).card :=
      le_of_eq (Finset.card_image_of_injective S (mul_right_injective h)).symm
    have himg : S.image (fun x ↦ h * x) = S :=
      Finset.eq_of_subset_of_card_le hsub hcard
    intro x hx
    rw [← himg] at hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    have hyx : h⁻¹ * x = y := by rw [← hxy, inv_mul_cancel_left]
    rw [hyx]
    exact hy

@[simp] theorem mem_leftStabilizer {S : Finset G} {h : G} :
    h ∈ leftStabilizer S ↔ ∀ x ∈ S, h * x ∈ S := Iff.rfl

/-- **The stabilizer of a nonempty finite set is finite.**  It injects into
that set: an element is determined by where it sends one fixed point. -/
theorem finite_leftStabilizer {S : Finset G} (hS : S.Nonempty) :
    Finite (leftStabilizer S) := by
  obtain ⟨x₀, hx₀⟩ := hS
  refine Finite.of_injective
    (fun h : leftStabilizer S ↦
      (⟨(h : G) * x₀, (mem_leftStabilizer.mp h.2) x₀ hx₀⟩ : {x : G // x ∈ S}))
    ?_
  intro h h' hEq
  have hval : (h : G) * x₀ = (h' : G) * x₀ := congrArg Subtype.val hEq
  exact Subtype.ext (mul_right_cancel hval)

/-! ## The group-level consequence -/

/-- **A group whose canonical trace has asymptotically multiplicative
compression models is locally finite.**

Given a finite subset `S`, each `g ∈ S` eventually has defect below `1` (the
multiplicativity hypothesis), hence defect exactly `0`
(`norm_inverseDefect_eq_zero_or_one_le`), hence preserves the window
(`mem_range_of_norm_inverseDefect_lt_one`).  Finitely many eventual conditions
share a stage; at such a stage the window is a nonempty finite set preserved
by every element of `S`, and its stabilizer is a finite subgroup containing
`S`.

The hypothesis `hpos` is not a restriction: a stage with an empty window
compresses everything to the `0 × 0` matrix, whose normalized trace is `0`
rather than `τ(1) = 1`, so such stages cannot be cofinal in a model of the
canonical trace.  It is stated as an eventual condition so that the theorem
applies to any family whose trace clause holds. -/
theorem isLocallyFiniteGroup_of_isAsymptoticallyMultiplicative
    (F : CompressionFamily G) (hpos : ∀ᶠ n in atTop, 0 < F.size n)
    (hmul : F.IsAsymptoticallyMultiplicative) :
    IsLocallyFiniteGroup G := by
  classical
  intro S
  have hev : ∀ g : G, ∀ᶠ n in atTop,
      ∀ q : Fin (F.size n), g * F.enum n q ∈ Set.range (F.enum n) := by
    intro g
    have hlt : ∀ᶠ n in atTop,
        ‖F.map n (reducedLeftRegular G g⁻¹ * reducedLeftRegular G g)
          - F.map n (reducedLeftRegular G g⁻¹)
            * F.map n (reducedLeftRegular G g)‖ < 1 :=
      (hmul (reducedLeftRegular G g⁻¹)
        (reducedLeftRegular G g)).eventually_lt_const zero_lt_one
    filter_upwards [hlt] with n hn q
    exact mem_range_of_norm_inverseDefect_lt_one (F.injective n) hn q
  have hallS : ∀ᶠ n in atTop, ∀ g ∈ S,
      ∀ q : Fin (F.size n), g * F.enum n q ∈ Set.range (F.enum n) :=
    (Filter.eventually_all_finset S).mpr fun g _ ↦ hev g
  obtain ⟨n, hn0, hnS⟩ := (hpos.and hallS).exists
  have hmemW : ∀ x : G,
      x ∈ Finset.image (F.enum n) Finset.univ ↔ x ∈ Set.range (F.enum n) := by
    intro x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨q, -, rfl⟩
      exact ⟨q, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, Finset.mem_univ q, rfl⟩
  have hWne : (Finset.image (F.enum n) Finset.univ).Nonempty := by
    obtain ⟨q⟩ := Fin.pos_iff_nonempty.mp hn0
    exact ⟨F.enum n q, (hmemW _).mpr ⟨q, rfl⟩⟩
  refine ⟨leftStabilizer (Finset.image (F.enum n) Finset.univ),
    finite_leftStabilizer hWne, fun g hg ↦ ?_⟩
  rw [mem_leftStabilizer]
  intro x hx
  obtain ⟨q, rfl⟩ := (hmemW x).mp hx
  exact (hmemW _).mpr (hnS g hg q)

end

end Quasidiagonal
end GroupApproximation

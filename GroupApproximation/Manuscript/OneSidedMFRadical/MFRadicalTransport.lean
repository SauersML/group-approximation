import GroupApproximation.Manuscript.OneSidedMFRadical.MFHomKernel
import GroupApproximation.Sofic.LEF
import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Pestov91.LEF
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Data.Matrix.Mul
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.NoncommRing

/-!
# The MF radical along embeddings, conjugation and restriction images

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`, tex lines 1696–1767).  The printed proof ends
with four group-theoretic moves and one ring-theoretic move, none of which uses the
dynamics.  They are proved here once, for arbitrary groups and rings, and the
printed assembly consumes them.

* tex 1752–1755: "Over $\F_2$, Theorem~\ref{thm:core-mf-radical} kills the whole
  return kernel in the embedded group in the stated rank ranges.  That kernel
  contains the phase-zero placement of every $g\in K_n(J)$, which $\Phi$ sends to
  $(1-p_C)I_n+g$."  A homomorphism carries the MF radical of its source into the MF
  radical of its target: `map_mfHomKernel_le`.
* tex 1756–1757: "Lemma~\ref{lem:involution-localization} conjugates every element
  of $K_n(I)$ into this corner, so all of $K_n(I)$ is killed."
  `mem_mfHomKernel_of_conj_mem`, `le_mfHomKernel_of_conj_mem_map`.
* tex 1757–1758: "Core restriction has LEF image, giving equality of radicals."
  `mfHomKernel_le_ker`, `mfHomKernel_eq_ker_of_le`,
  `mfHomKernel_eq_ker_of_conj_into_embedded`; the maximal MF quotient of tex
  1703–1704 is `quotientMFRadicalEquivRange`, with `isLEF_range` and
  `isOperatorMF_range_of_isLEF`.
* tex 1763–1765: "Transfer one nonzero invisible defect root ..."
  `not_isOperatorMF_of_injective_of_mem`.
* tex 1760–1763: "if $R_X$ is not directly finite then neither is $P_C$: otherwise
  Theorem~\ref{thm:core-ring-reflection} would make $P_C$ stably finite, and the full
  tower corner would make $R_X$ directly finite."
  `isDedekindFiniteMonoid_of_injective_nonUnitalRingHom`,
  `not_isDedekindFiniteMonoid_of_tower_corner`.
* tex 1697–1699 and 1766, "MF if and only if they are LEF, if and only if $R_X$ is
  directly finite", from its three printed ingredients:
  `isOperatorMF_iff_isLEF_and_isLEF_iff_of_pieces`.

`Rad_MF(G)` is `MFQuotientUnits.mfHomKernel G`, the printed intersection of the
kernels of all homomorphisms from `G` to MF groups.
-/

namespace GroupApproximation
namespace MFRadicalTransport

open MFQuotientUnits

section Groups

variable {G H : Type} [Group G] [Group H]

/-- **A homomorphism carries the MF radical into the MF radical.**

`non_mf_groups_exist.tex`, proof of `cor:dynamic-rank-budget`, tex 1752–1755: a kill
in the embedded group is a kill in the ambient group.  Every homomorphism from `G` to
an MF group restricts along `φ` to one from `H`. -/
theorem map_mfHomKernel_le (φ : H →* G) : (mfHomKernel H).map φ ≤ mfHomKernel G := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_mfHomKernel_iff _).mpr fun M _ hM f ↦ (mem_mfHomKernel_iff x).mp hx M hM (f.comp φ)

/-- **An element with a conjugate in the MF radical lies in the MF radical**, since the
radical is normal. -/
theorem mem_mfHomKernel_of_conj_mem {x g : G} (h : g * x * g⁻¹ ∈ mfHomKernel G) :
    x ∈ mfHomKernel G := by
  have h' := (mfHomKernel_normal G).conj_mem _ h g⁻¹
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h'

/-- **Conjugation into an embedded radical kills.**

tex 1756–1757: if every element of `K` has a conjugate in the image of a subgroup `L`
of the MF radical of an embedded group, then `K` lies in the MF radical. -/
theorem le_mfHomKernel_of_conj_mem_map (φ : H →* G) {L : Subgroup H}
    (hL : L ≤ mfHomKernel H) {K : Subgroup G}
    (hK : ∀ x ∈ K, ∃ g : G, g * x * g⁻¹ ∈ L.map φ) : K ≤ mfHomKernel G := by
  intro x hx
  obtain ⟨g, hg⟩ := hK x hx
  exact mem_mfHomKernel_of_conj_mem (map_mfHomKernel_le φ (Subgroup.map_mono hL hg))

/-- **A homomorphism to an MF group kills the MF radical.** -/
theorem mfHomKernel_le_ker {M : Type} [Group M] (hM : IsOperatorMF M) (ψ : G →* M) :
    mfHomKernel G ≤ ψ.ker := fun x hx ↦
  MonoidHom.mem_ker.mpr ((mem_mfHomKernel_iff x).mp hx M hM ψ)

/-- **An MF group has trivial MF radical**: apply the identity homomorphism. -/
theorem mfHomKernel_eq_bot_of_isOperatorMF (hG : IsOperatorMF G) : mfHomKernel G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact Subgroup.mem_bot.mpr ((mem_mfHomKernel_iff x).mp hx G hG (MonoidHom.id G))

/-- **The radical sandwich.**  tex 1757–1758: a kernel of a homomorphism to an MF group
that lies in the MF radical is the MF radical. -/
theorem mfHomKernel_eq_ker_of_le {M : Type} [Group M] (hM : IsOperatorMF M) (ψ : G →* M)
    (hK : ψ.ker ≤ mfHomKernel G) : mfHomKernel G = ψ.ker :=
  le_antisymm (mfHomKernel_le_ker hM ψ) hK

/-- **The printed radical equality, abstractly.**  tex 1752–1758: a restriction `ψ` to
an MF group whose kernel is conjugated, element by element, into the image of a
subgroup of an embedded MF radical has kernel equal to the MF radical. -/
theorem mfHomKernel_eq_ker_of_conj_into_embedded {M : Type} [Group M] (hM : IsOperatorMF M)
    (ψ : G →* M) (φ : H →* G) {L : Subgroup H} (hL : L ≤ mfHomKernel H)
    (hconj : ∀ x ∈ ψ.ker, ∃ g : G, g * x * g⁻¹ ∈ L.map φ) : mfHomKernel G = ψ.ker :=
  mfHomKernel_eq_ker_of_le hM ψ (le_mfHomKernel_of_conj_mem_map φ hL hconj)

/-- **The maximal MF quotient is the restriction image.**  tex 1703–1704: once the
kernel of `ψ` lies in the MF radical, `G ⧸ Rad_MF(G)` is isomorphic to the image of `ψ`. -/
noncomputable def quotientMFRadicalEquivRange {M : Type} [Group M] (hM : IsOperatorMF M)
    (ψ : G →* M) (hK : ψ.ker ≤ mfHomKernel G) : G ⧸ mfHomKernel G ≃* ψ.range :=
  (QuotientGroup.quotientMulEquivOfEq (mfHomKernel_eq_ker_of_le hM ψ hK)).trans
    (QuotientGroup.quotientKerEquivRange ψ)

/-- The image of a homomorphism into an LEF group is LEF. -/
theorem isLEF_range {M : Type} [Group M] (hM : IsLEF M) (ψ : G →* M) : IsLEF ψ.range :=
  isLEF_of_injective ψ.range.subtype Subtype.val_injective hM

/-- The image of a countable group in an LEF group is MF. -/
theorem isOperatorMF_range_of_isLEF [Countable G] {M : Type} [Group M] (hM : IsLEF M)
    (ψ : G →* M) : IsOperatorMF ψ.range := by
  haveI : Countable ψ.range := ψ.rangeRestrict_surjective.countable
  exact isOperatorMF_of_isLEF (isLEF_range hM ψ)

/-- **A nonzero invisible element, transferred along an embedding.**  tex 1763–1765: a
nontrivial element of the MF radical of `H`, pushed along an injective homomorphism,
shows that `G` is not MF. -/
theorem not_isOperatorMF_of_injective_of_mem (φ : H →* G) (hφ : Function.Injective φ)
    {x : H} (hx : x ∈ mfHomKernel H) (hx1 : x ≠ 1) : ¬ IsOperatorMF G := by
  intro hG
  have hmem : φ x ∈ mfHomKernel G := map_mfHomKernel_le φ (Subgroup.mem_map_of_mem φ hx)
  rw [mfHomKernel_eq_bot_of_isOperatorMF hG, Subgroup.mem_bot] at hmem
  exact hx1 (hφ (hmem.trans (map_one φ).symm))

/-- **MF if and only if LEF, if and only if directly finite, from the printed ingredients.**

tex 1697–1699 and 1766.  The three ingredients are: directly finite rings are LEF
(Theorem `thm:core-ring-reflection`); LEF rings give LEF groups (the LEF ring models); and
a ring that is not directly finite gives a nontrivial element of the MF radical (the
transferred defect root).  A countable LEF group is MF. -/
theorem isOperatorMF_iff_isLEF_and_isLEF_iff_of_pieces [Countable G] {R : Type*} [Ring R]
    (hlef : Pestov91.IsLEFRing R → IsLEF G)
    (hrefl : IsDedekindFiniteMonoid R → Pestov91.IsLEFRing R)
    (htransfer : ¬ IsDedekindFiniteMonoid R → ∃ x ∈ mfHomKernel G, x ≠ 1) :
    (IsOperatorMF G ↔ IsLEF G) ∧ (IsLEF G ↔ IsDedekindFiniteMonoid R) := by
  have hmf : IsOperatorMF G → IsDedekindFiniteMonoid R := by
    intro hG
    by_contra hnot
    obtain ⟨x, hx, hx1⟩ := htransfer hnot
    rw [mfHomKernel_eq_bot_of_isOperatorMF hG, Subgroup.mem_bot] at hx
    exact hx1 hx
  have hdf : IsDedekindFiniteMonoid R → IsLEF G := fun h ↦ hlef (hrefl h)
  have hlefmf : IsLEF G → IsOperatorMF G := fun h ↦ isOperatorMF_of_isLEF h
  exact ⟨⟨fun h ↦ hdf (hmf h), hlefmf⟩, ⟨fun h ↦ hmf (hlefmf h), hdf⟩⟩

end Groups

section Rings

/-- **A ring with an injective non-unital embedding into a directly finite ring is directly
finite.**

tex 1761–1763: "the full tower corner would make $R_X$ directly finite".  The printed map
`x ↦ (b_i x a_j)_{ij}` into `M_{2r-1}(P_C)` is additive, multiplicative and injective, but
sends `1` to an idempotent `e`, not to `1`.  If `ts = 1`, then
`(1 - e + ψ t) (1 - e + ψ s) = 1 - e + ψ (t s) = 1`, because `ψ t` and `ψ s` lie in the corner
`e A e`; direct finiteness of `A` reverses the product, so `ψ (s t) = e = ψ 1`. -/
theorem isDedekindFiniteMonoid_of_injective_nonUnitalRingHom {R A : Type*} [Ring R] [Ring A]
    [IsDedekindFiniteMonoid A] (ψ : R →ₙ+* A) (hψ : Function.Injective ψ) :
    IsDedekindFiniteMonoid R := by
  constructor
  intro t s hts
  have hl : ∀ a : R, ψ 1 * ψ a = ψ a := fun a ↦ by rw [← map_mul, one_mul]
  have hr : ∀ a : R, ψ a * ψ 1 = ψ a := fun a ↦ by rw [← map_mul, mul_one]
  have key : ∀ a b : R, (1 - ψ 1 + ψ a) * (1 - ψ 1 + ψ b) = 1 - ψ 1 + ψ (a * b) := by
    intro a b
    have h11 : ψ 1 * ψ 1 = ψ 1 := hl 1
    calc (1 - ψ 1 + ψ a) * (1 - ψ 1 + ψ b)
        = 1 - ψ 1 - ψ 1 + ψ 1 * ψ 1 + (ψ b - ψ 1 * ψ b) + (ψ a - ψ a * ψ 1) + ψ a * ψ b := by
          noncomm_ring
      _ = 1 - ψ 1 + ψ (a * b) := by
          rw [h11, hl b, hr a, map_mul]
          abel
  have h1 : (1 - ψ 1 + ψ t) * (1 - ψ 1 + ψ s) = 1 := by
    rw [key, hts]
    abel
  have h2 := mul_eq_one_symm h1
  rw [key] at h2
  have h3 : ψ (s * t) = ψ 1 := by
    calc ψ (s * t) = (1 - ψ 1 + ψ (s * t)) - (1 - ψ 1) := by abel
      _ = 1 - (1 - ψ 1) := by rw [h2]
      _ = ψ 1 := by abel
  exact hψ h3

/-- tex 1761–1763 in the printed shape: an injective non-unital embedding into a matrix ring
over a stably finite ring makes the source directly finite. -/
theorem isDedekindFiniteMonoid_of_injective_nonUnitalRingHom_matrix {R P : Type*} [Ring R]
    [Ring P] [IsStablyFiniteRing P] (m : ℕ) (ψ : R →ₙ+* Matrix (Fin m) (Fin m) P)
    (hψ : Function.Injective ψ) : IsDedekindFiniteMonoid R :=
  isDedekindFiniteMonoid_of_injective_nonUnitalRingHom ψ hψ

/-- **If `R` is not directly finite, then neither is the return ring.**  tex 1760–1763: if
directly finite return rings are stably finite (Theorem `thm:core-ring-reflection` for the
return system), then a tower corner embedding `R → M_m(P)` transfers direct finiteness from
`P` to `R`. -/
theorem not_isDedekindFiniteMonoid_of_tower_corner {R P : Type*} [Ring R] [Ring P]
    (hrefl : IsDedekindFiniteMonoid P → IsStablyFiniteRing P) (m : ℕ)
    (ψ : R →ₙ+* Matrix (Fin m) (Fin m) P) (hψ : Function.Injective ψ)
    (hR : ¬ IsDedekindFiniteMonoid R) : ¬ IsDedekindFiniteMonoid P := fun hP ↦
  hR (haveI := hrefl hP; isDedekindFiniteMonoid_of_injective_nonUnitalRingHom_matrix m ψ hψ)

end Rings

end MFRadicalTransport
end GroupApproximation

/-! ### Audit -/

#audit_axioms GroupApproximation.MFRadicalTransport.map_mfHomKernel_le
#audit_axioms GroupApproximation.MFRadicalTransport.mem_mfHomKernel_of_conj_mem
#audit_axioms GroupApproximation.MFRadicalTransport.le_mfHomKernel_of_conj_mem_map
#audit_axioms GroupApproximation.MFRadicalTransport.mfHomKernel_le_ker
#audit_axioms GroupApproximation.MFRadicalTransport.mfHomKernel_eq_bot_of_isOperatorMF
#audit_axioms GroupApproximation.MFRadicalTransport.mfHomKernel_eq_ker_of_le
#audit_axioms GroupApproximation.MFRadicalTransport.mfHomKernel_eq_ker_of_conj_into_embedded
#audit_axioms GroupApproximation.MFRadicalTransport.quotientMFRadicalEquivRange
#audit_axioms GroupApproximation.MFRadicalTransport.isLEF_range
#audit_axioms GroupApproximation.MFRadicalTransport.isOperatorMF_range_of_isLEF
#audit_axioms GroupApproximation.MFRadicalTransport.not_isOperatorMF_of_injective_of_mem
#audit_axioms GroupApproximation.MFRadicalTransport.isOperatorMF_iff_isLEF_and_isLEF_iff_of_pieces
#audit_axioms GroupApproximation.MFRadicalTransport.isDedekindFiniteMonoid_of_injective_nonUnitalRingHom
#audit_axioms GroupApproximation.MFRadicalTransport.isDedekindFiniteMonoid_of_injective_nonUnitalRingHom_matrix
#audit_axioms GroupApproximation.MFRadicalTransport.not_isDedekindFiniteMonoid_of_tower_corner

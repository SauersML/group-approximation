import GroupApproximation.Algebra.ZariskiClosedSubgroup
import GroupApproximation.Criterion.ClosedEnvelopeCompressionCore
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.WellFounded
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The descending chain condition for Zariski closed subgroups of `GL(V)`

`non_mf_groups_exist.tex` carried, in a `\begin{remark}[chain conditions
suffice]` of `\section{The finite-dimensional obstruction}`
(`\ref{sec:findim}`), this sentence about the algebraic envelope:

> the Zariski closures of `σ(Γ)` and `σ(tΓt⁻¹)` coincide, the descending chain
> condition for Zariski-closed subgroups of `GL(V)` coming from the Hilbert
> basis theorem.

That was the whole of what the manuscript said about the chain condition:
it named the Hilbert basis theorem as its ground and asserted the conclusion
without hypothesis.  **The remark was deleted in commit `3a45fa60` ("Editorial
pass: rewrite orbit collapse, cut what nothing uses"), so the quotation above
is a record and not a live citation; `rem:chaincondition` is not a `\label` any
more.**  (An earlier version of this docstring quoted the
manuscript as adding that the chain condition "is the input the badge
quantifies over rather than proves".  No such sentence occurs in
`non_mf_groups_exist.tex`; it appears to have come from an early draft, and it
had also been copied into the gate's own roster in
`scripts/check_non_mf_unconditional.py`, where it is likewise now removed.)

This file supplies the ground the manuscript names.  The chain condition is
*proved*, and
the abstract deduction of `Criterion/ClosedEnvelopeCompressionCore` is
instantiated at the Zariski notion of closedness, so that

  `zariskiEnvelope (t Γ t⁻¹) = zariskiEnvelope Γ`

for a one-sided compression becomes an unconditional theorem about `GL(V)`.

## The proof, step by step

1. **Hilbert basis theorem.**  `k` is a field, hence a Noetherian ring, hence
   `k[X_{ij}]` in the finitely many variables `n × n` is Noetherian
   (`MvPolynomial.isNoetherianRing`), so its ideals satisfy the *ascending*
   chain condition (`IsNoetherian.wellFoundedGT`).
2. **The ideal–variety pair reverses and reflects order.**  On Zariski closed
   sets, `zIdeal` is antitone (`zIdeal_antitone`) and reflects inclusion
   (`subset_of_zIdeal_le`), because a closed set is recovered from its ideal
   (`preimage_zeroLocus_zIdeal`).  So `zIdeal` is *strictly* antitone on the
   poset of closed sets, and likewise on the poset of closed subgroups.
3. **Descending chains terminate.**  A strictly antitone map into a poset with
   the ascending chain condition forces the ascending chain condition on the
   source read backwards: `StrictAnti.wellFoundedLT`.  This is
   `wellFoundedLT_isZClosedSubgroup`, and `zariski_dcc_closedSubgroups` is its
   chain-shaped restatement — the manuscript's classical input.
4. **The Zariski closure of a subgroup is a subgroup.**  Closedness under
   multiplication uses only that translations are homeomorphisms.  Closure
   under inversion uses the chain condition just proved: for `x` in the closure
   `C`, the descending chain `xᵐ·C` of closed sets stabilises, and `xᵐ⁺¹C = xᵐC`
   forces `x⁻¹ ∈ C`.  Hence `zEnvelope` — defined as the least closed subgroup
   containing a subgroup — *is* the Zariski closure (`zEnvelope_eq_zClosure`),
   which is what the manuscript's phrase names.
5. **The envelope conclusion.**  `manuscriptZariskiEnvelopeCompressionBlind`
   feeds the chain condition, the conjugation stability, the monotonicity and
   the equivariance into `ClosedEnvelopeCompression.envelope_conj_eq`.

A final section transports the chain condition along a group isomorphism, and
in particular to `GL(V)` for an arbitrary finite-dimensional `V` presented by a
basis.

Every step is proved from Mathlib; no hypothesis stands in for mathematics.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace ZariskiClosedSubgroup

open Matrix

/-! ### A chain-condition helper -/

/-- A descending sequence whose terms all satisfy a predicate `P` whose
subtype is well founded downwards must repeat at some step. -/
theorem exists_succ_eq_of_antitone {α : Type*} [PartialOrder α] (P : α → Prop)
    [WellFoundedLT {a : α // P a}] (F : ℕ → α) (hF : ∀ m, P (F m))
    (hanti : ∀ m, F (m + 1) ≤ F m) : ∃ m, F (m + 1) = F m := by
  have hwf : WellFounded ((· < ·) : {a : α // P a} → {a : α // P a} → Prop) := wellFounded_lt
  obtain ⟨_, ⟨m, rfl⟩, hmin⟩ :=
    hwf.has_min (Set.range fun m => (⟨F m, hF m⟩ : {a : α // P a}))
      ⟨⟨F 0, hF 0⟩, 0, rfl⟩
  refine ⟨m, ?_⟩
  by_contra hne
  refine hmin ⟨F (m + 1), hF (m + 1)⟩ ⟨m + 1, rfl⟩ ?_
  refine lt_of_le_of_ne (hanti m) ?_
  intro hEq
  exact hne (congrArg Subtype.val hEq)

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]

/-! ### The chain condition

`k` is a field, hence Noetherian; `k[X_{ij}]` has finitely many variables,
hence is Noetherian by the Hilbert basis theorem; hence its ideals satisfy the
ascending chain condition.  `zIdeal` embeds the closed sets into the ideals
order-reversingly, so the closed sets satisfy the descending chain condition.
-/

/-- `zIdeal` is strictly antitone on the Zariski closed subsets. -/
theorem zIdeal_strictAnti_sets :
    StrictAnti (fun T : {T : Set (GeneralLinearGroup n k) // IsZClosed T} => zIdeal T.1) := by
  intro T T' h
  have hle : T.1 ⊆ T'.1 := h.le
  have hne : T.1 ≠ T'.1 := fun hEq => h.ne (Subtype.ext hEq)
  refine lt_of_le_of_ne (zIdeal_antitone hle) ?_
  intro hEq
  exact hne (Set.Subset.antisymm hle (subset_of_zIdeal_le T.2 (le_of_eq hEq.symm)))

/-- **The descending chain condition for Zariski closed subsets of `GL(V)`.** -/
instance wellFoundedLT_isZClosed :
    WellFoundedLT {T : Set (GeneralLinearGroup n k) // IsZClosed T} :=
  StrictAnti.wellFoundedLT zIdeal_strictAnti_sets

/-- `zIdeal` is strictly antitone on the Zariski closed subgroups. -/
theorem zIdeal_strictAnti_subgroups :
    StrictAnti (fun H : {H : Subgroup (GeneralLinearGroup n k) // IsZClosedSubgroup H} =>
      zIdeal (H.1 : Set (GeneralLinearGroup n k))) := by
  intro H H' h
  have hle0 : H.1 ≤ H'.1 := h.le
  have hle : (H.1 : Set (GeneralLinearGroup n k)) ⊆ (H'.1 : Set (GeneralLinearGroup n k)) :=
    SetLike.coe_subset_coe.mpr hle0
  have hne : H.1 ≠ H'.1 := fun hEq => h.ne (Subtype.ext hEq)
  refine lt_of_le_of_ne (zIdeal_antitone hle) ?_
  intro hEq
  refine hne (SetLike.coe_injective (Set.Subset.antisymm hle ?_))
  exact subset_of_zIdeal_le H.2 (le_of_eq hEq.symm)

/-- **The descending chain condition for Zariski closed subgroups of `GL(V)`.**
This is the classical input the manuscript's envelope badge quantifies over. -/
instance wellFoundedLT_isZClosedSubgroup :
    WellFoundedLT {H : Subgroup (GeneralLinearGroup n k) // IsZClosedSubgroup H} :=
  StrictAnti.wellFoundedLT zIdeal_strictAnti_subgroups

/-- **The chain condition, in chain form.**  A descending chain of Zariski
closed subgroups of `GL(V)` stabilises. -/
theorem zariski_dcc_closedSubgroups (C : ℕ → Subgroup (GeneralLinearGroup n k))
    (hC : ∀ m, IsZClosedSubgroup (C m)) (hanti : ∀ m, C (m + 1) ≤ C m) :
    ∃ m, C (m + 1) = C m :=
  exists_succ_eq_of_antitone IsZClosedSubgroup C hC hanti

/-- **The chain condition, in negative form.**  There is no infinite strictly
descending chain of Zariski closed subgroups of `GL(V)`. -/
theorem zariski_no_strict_descending_chain (C : ℕ → Subgroup (GeneralLinearGroup n k))
    (hC : ∀ m, IsZClosedSubgroup (C m)) : ¬ ∀ m, C (m + 1) < C m := by
  intro hstrict
  obtain ⟨m, hm⟩ := zariski_dcc_closedSubgroups C hC fun m => (hstrict m).le
  exact (hstrict m).ne hm

/-! ### The Zariski closure of a subgroup is a subgroup

Only two inputs are used: two-sided translations preserve closedness
(`isZClosed_translate`), and closed subsets satisfy the descending chain
condition (`wellFoundedLT_isZClosed`).  In particular no localisation at the
determinant, and no separate proof that inversion is a morphism, is needed.
-/

section ClosureSubgroup

variable {H : Subgroup (GeneralLinearGroup n k)}

/-- Left translation by an element of `H` preserves the closure of `H`. -/
theorem mem_zClosure_mul_left {h y : GeneralLinearGroup n k} (hh : h ∈ H)
    (hy : y ∈ zClosure (H : Set (GeneralLinearGroup n k))) :
    h * y ∈ zClosure (H : Set (GeneralLinearGroup n k)) := by
  have hclosed : IsZClosed (translate h 1 (zClosure (H : Set (GeneralLinearGroup n k)))) :=
    isZClosed_translate (isZClosed_zClosure _) h 1
  have hsub : (H : Set (GeneralLinearGroup n k)) ⊆
      translate h 1 (zClosure (H : Set (GeneralLinearGroup n k))) := by
    intro z hz
    show h * z * 1 ∈ zClosure (H : Set (GeneralLinearGroup n k))
    rw [mul_one]
    exact subset_zClosure _
      (SetLike.mem_coe.mpr (H.mul_mem hh (SetLike.mem_coe.mp hz)))
  have hmem : h * y * 1 ∈ zClosure (H : Set (GeneralLinearGroup n k)) :=
    zClosure_subset_of_isZClosed hclosed hsub hy
  rwa [mul_one] at hmem

/-- The closure of a subgroup is closed under multiplication. -/
theorem mem_zClosure_mul {x y : GeneralLinearGroup n k}
    (hx : x ∈ zClosure (H : Set (GeneralLinearGroup n k)))
    (hy : y ∈ zClosure (H : Set (GeneralLinearGroup n k))) :
    x * y ∈ zClosure (H : Set (GeneralLinearGroup n k)) := by
  have hclosed : IsZClosed (translate 1 y (zClosure (H : Set (GeneralLinearGroup n k)))) :=
    isZClosed_translate (isZClosed_zClosure _) 1 y
  have hsub : (H : Set (GeneralLinearGroup n k)) ⊆
      translate 1 y (zClosure (H : Set (GeneralLinearGroup n k))) := by
    intro z hz
    show (1 : GeneralLinearGroup n k) * z * y ∈ zClosure (H : Set (GeneralLinearGroup n k))
    rw [one_mul]
    exact mem_zClosure_mul_left (SetLike.mem_coe.mp hz) hy
  have hmem : (1 : GeneralLinearGroup n k) * x * y ∈
      zClosure (H : Set (GeneralLinearGroup n k)) :=
    zClosure_subset_of_isZClosed hclosed hsub hx
  rwa [one_mul] at hmem

/-- The closure of a subgroup contains the identity. -/
theorem one_mem_zClosure :
    (1 : GeneralLinearGroup n k) ∈ zClosure (H : Set (GeneralLinearGroup n k)) :=
  subset_zClosure _ (SetLike.mem_coe.mpr H.one_mem)

/-- **The closure of a subgroup is closed under inversion.**  This is where the
chain condition is used: the descending chain of closed sets `xᵐ · C`
stabilises, and one step of stabilisation produces the inverse. -/
theorem inv_mem_zClosure {x : GeneralLinearGroup n k}
    (hx : x ∈ zClosure (H : Set (GeneralLinearGroup n k))) :
    x⁻¹ ∈ zClosure (H : Set (GeneralLinearGroup n k)) := by
  have hkey : ∀ j : ℕ, x * (x ^ (j + 1))⁻¹ = (x ^ j)⁻¹ := by
    intro j
    rw [pow_succ, _root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  have hFclosed : ∀ m : ℕ,
      IsZClosed (translate (x ^ m)⁻¹ 1 (zClosure (H : Set (GeneralLinearGroup n k)))) :=
    fun m => isZClosed_translate (isZClosed_zClosure _) (x ^ m)⁻¹ 1
  have hFanti : ∀ m : ℕ,
      translate (x ^ (m + 1))⁻¹ 1 (zClosure (H : Set (GeneralLinearGroup n k)))
        ≤ translate (x ^ m)⁻¹ 1 (zClosure (H : Set (GeneralLinearGroup n k))) := by
    intro m y hy
    have hy' : (x ^ (m + 1))⁻¹ * y * 1 ∈ zClosure (H : Set (GeneralLinearGroup n k)) := hy
    have hprod : x * ((x ^ (m + 1))⁻¹ * y * 1) = (x ^ m)⁻¹ * y * 1 := by
      rw [mul_one, mul_one, ← mul_assoc, hkey m]
    show (x ^ m)⁻¹ * y * 1 ∈ zClosure (H : Set (GeneralLinearGroup n k))
    rw [← hprod]
    exact mem_zClosure_mul hx hy'
  obtain ⟨m, hm⟩ :=
    exists_succ_eq_of_antitone IsZClosed
      (fun m => translate (x ^ m)⁻¹ 1 (zClosure (H : Set (GeneralLinearGroup n k))))
      hFclosed hFanti
  have hm' : translate (x ^ (m + 1))⁻¹ 1 (zClosure (H : Set (GeneralLinearGroup n k)))
      = translate (x ^ m)⁻¹ 1 (zClosure (H : Set (GeneralLinearGroup n k))) := hm
  have hxm : x ^ m ∈ translate (x ^ m)⁻¹ 1
      (zClosure (H : Set (GeneralLinearGroup n k))) := by
    show (x ^ m)⁻¹ * x ^ m * 1 ∈ zClosure (H : Set (GeneralLinearGroup n k))
    have hone : (x ^ m)⁻¹ * x ^ m * 1 = 1 := by
      rw [inv_mul_cancel, one_mul]
    rw [hone]
    exact one_mem_zClosure
  rw [← hm'] at hxm
  have hxm' : (x ^ (m + 1))⁻¹ * x ^ m * 1 ∈
      zClosure (H : Set (GeneralLinearGroup n k)) := hxm
  have hfin : (x ^ (m + 1))⁻¹ * x ^ m * 1 = x⁻¹ := by
    rw [mul_one, pow_succ, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  rwa [hfin] at hxm'

end ClosureSubgroup

/-- **The Zariski closure of a subgroup of `GL(V)`, as a subgroup.** -/
def zClosureSubgroup (H : Subgroup (GeneralLinearGroup n k)) :
    Subgroup (GeneralLinearGroup n k) where
  carrier := zClosure (H : Set (GeneralLinearGroup n k))
  mul_mem' := by
    intro a b ha hb
    exact mem_zClosure_mul ha hb
  one_mem' := one_mem_zClosure
  inv_mem' := by
    intro a ha
    exact inv_mem_zClosure ha

/-- **The algebraic envelope is the Zariski closure.**  This identifies the
lattice-theoretic definition of `zEnvelope` with the topological object the
manuscript names, `closure of σ(Γ) in the Zariski topology`. -/
theorem zEnvelope_eq_zClosure (H : Subgroup (GeneralLinearGroup n k)) :
    (zEnvelope H : Set (GeneralLinearGroup n k))
      = zClosure (H : Set (GeneralLinearGroup n k)) := by
  refine Set.Subset.antisymm ?_ ?_
  · have h1 : IsZClosedSubgroup (zClosureSubgroup H) := isZClosed_zClosure _
    have h2 : H ≤ zClosureSubgroup H := SetLike.coe_subset_coe.mp (subset_zClosure _)
    have h3 : zEnvelope H ≤ zClosureSubgroup H := zEnvelope_le h1 h2
    exact SetLike.coe_subset_coe.mpr h3
  · exact zClosure_subset_of_isZClosed (isZClosedSubgroup_zEnvelope H)
      (SetLike.coe_subset_coe.mpr (le_zEnvelope H))

/-! ### The manuscript's envelope conclusion, unconditionally -/

/-- **Compression does not move the algebraic envelope.**  This is
`Criterion/ClosedEnvelopeCompressionCore.envelope_conj_eq` with its one hypothesis
— the descending chain condition for closed subgroups — discharged by
`wellFoundedLT_isZClosedSubgroup`, and its abstract notion of closedness
instantiated at Zariski closedness.  By `zEnvelope_eq_zClosure` the envelope is
the Zariski closure, so this is the manuscript's

  `closure of σ(tΓt⁻¹) = closure of σ(Γ)`. -/
theorem manuscriptZariskiEnvelopeCompressionBlind
    {Γ : Subgroup (GeneralLinearGroup n k)} {t : GeneralLinearGroup n k}
    (ht : Γ.map (MulAut.conj t).toMonoidHom ≤ Γ) :
    zEnvelope (Γ.map (MulAut.conj t).toMonoidHom) = zEnvelope Γ :=
  ClosedEnvelopeCompression.envelope_conj_eq
    (G := GeneralLinearGroup n k) IsZClosedSubgroup
    (fun g _ hH => isZClosedSubgroup_map_conj hH g)
    zEnvelope isZClosedSubgroup_zEnvelope (fun _ _ h => zEnvelope_mono h)
    zEnvelope_map_conj ht

/-- The same statement written on the closures themselves. -/
theorem manuscriptZariskiClosureCompressionBlind
    {Γ : Subgroup (GeneralLinearGroup n k)} {t : GeneralLinearGroup n k}
    (ht : Γ.map (MulAut.conj t).toMonoidHom ≤ Γ) :
    zClosure ((Γ.map (MulAut.conj t).toMonoidHom : Subgroup (GeneralLinearGroup n k)) :
        Set (GeneralLinearGroup n k))
      = zClosure (Γ : Set (GeneralLinearGroup n k)) := by
  rw [← zEnvelope_eq_zClosure, ← zEnvelope_eq_zClosure,
    manuscriptZariskiEnvelopeCompressionBlind ht]

/-- **The manuscript's displayed identity**, at the level at which it is
printed: for a homomorphism `σ : H → GL(V)`, a subgroup `Γ ≤ H` and a
compressor `t` with `tΓt⁻¹ ≤ Γ`, the Zariski closures of `σ(tΓt⁻¹)` and of
`σ(Γ)` coincide.  This is
the displayed `\overline{\sigma(t\Gamma t^{-1})}^{\,Z}=\overline{\sigma(\Gamma)}^{\,Z}`
of `rem:chaincondition` in `non_mf_groups_exist.tex` (navigate by the label). -/
theorem manuscriptZariskiClosureOfRepresentation {H : Type*} [Group H]
    (σ : H →* GeneralLinearGroup n k) (Γ : Subgroup H) (t : H)
    (ht : Γ.map (MulAut.conj t).toMonoidHom ≤ Γ) :
    zClosure ((((Γ.map (MulAut.conj t).toMonoidHom).map σ) :
        Subgroup (GeneralLinearGroup n k)) : Set (GeneralLinearGroup n k))
      = zClosure ((Γ.map σ : Subgroup (GeneralLinearGroup n k)) :
        Set (GeneralLinearGroup n k)) := by
  have hhom : σ.comp (MulAut.conj t).toMonoidHom
      = (MulAut.conj (σ t)).toMonoidHom.comp σ := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
  have hmap : (Γ.map (MulAut.conj t).toMonoidHom).map σ
      = (Γ.map σ).map (MulAut.conj (σ t)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, hhom]
  rw [hmap]
  refine manuscriptZariskiClosureCompressionBlind ?_
  rw [← hmap]
  exact Subgroup.map_mono ht

/-- **Closed-header form.**  The coordinate data, the group, the
representation, the subgroup and the compressing element are all quantified
inside the proposition, so the printed header states on its own face what a
caller must supply.  The manuscript cites this form; the version above keeps
its section variables and is the one the proof is written against. -/
theorem manuscriptZariskiRepresentationEnvelopeClosed :
    ∀ {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]
      {H : Type*} [Group H] (σ : H →* GeneralLinearGroup n k)
      (Γ : Subgroup H) (t : H),
      Γ.map (MulAut.conj t).toMonoidHom ≤ Γ →
      zClosure ((((Γ.map (MulAut.conj t).toMonoidHom).map σ) :
          Subgroup (GeneralLinearGroup n k)) : Set (GeneralLinearGroup n k))
        = zClosure ((Γ.map σ : Subgroup (GeneralLinearGroup n k)) :
          Set (GeneralLinearGroup n k)) := by
  intro n _ _ k _ H _ σ Γ t ht
  exact manuscriptZariskiClosureOfRepresentation σ Γ t ht

end

/-! ### Transport to `GL(V)` for an arbitrary finite-dimensional `V`

`GL n k` is `GL(V)` for `V = n → k`.  For an arbitrary `V` with a basis indexed
by `n`, the closedness notion and the chain condition transport along the
resulting group isomorphism.
-/

section Transport

variable {G G' : Type*} [Group G] [Group G']

/-- A group isomorphism reflects equality of subgroups through `comap`. -/
theorem comap_mulEquiv_injective (e : G ≃* G') {H K : Subgroup G'}
    (h : H.comap e.toMonoidHom = K.comap e.toMonoidHom) : H = K := by
  ext y
  have hy : e (e.symm y) = y := e.apply_symm_apply y
  constructor
  · intro hmem
    have h1 : e.symm y ∈ H.comap e.toMonoidHom := by
      rw [Subgroup.mem_comap]
      show e (e.symm y) ∈ H
      rw [hy]
      exact hmem
    rw [h, Subgroup.mem_comap] at h1
    have h2 : e (e.symm y) ∈ K := h1
    rwa [hy] at h2
  · intro hmem
    have h1 : e.symm y ∈ K.comap e.toMonoidHom := by
      rw [Subgroup.mem_comap]
      show e (e.symm y) ∈ K
      rw [hy]
      exact hmem
    rw [← h, Subgroup.mem_comap] at h1
    have h2 : e (e.symm y) ∈ H := h1
    rwa [hy] at h2

/-- **The chain condition transports along a group isomorphism.** -/
theorem wellFoundedLT_comap (e : G ≃* G') (Closed : Subgroup G → Prop)
    [WellFoundedLT {H : Subgroup G // Closed H}] :
    WellFoundedLT {H : Subgroup G' // Closed (H.comap e.toMonoidHom)} := by
  refine StrictMono.wellFoundedLT
    (f := fun H : {H : Subgroup G' // Closed (H.comap e.toMonoidHom)} =>
      (⟨H.1.comap e.toMonoidHom, H.2⟩ : {H : Subgroup G // Closed H})) ?_
  intro H K h
  have hle : H.1 ≤ K.1 := h.le
  have hne : H.1 ≠ K.1 := fun hEq => h.ne (Subtype.ext hEq)
  refine lt_of_le_of_ne (Subgroup.comap_mono hle) ?_
  intro hEq
  exact hne (comap_mulEquiv_injective e (Subtype.ext_iff.mp hEq))

end Transport

noncomputable section GLV

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- Zariski closedness for subgroups of `GL(V)`, read off in a basis. -/
def IsZClosedSubgroupOfBasis (b : Module.Basis n k V)
    (H : Subgroup (LinearMap.GeneralLinearGroup k V)) : Prop :=
  IsZClosedSubgroup (H.comap (Matrix.GeneralLinearGroup.toLin' b).toMonoidHom)

/-- **The descending chain condition for Zariski closed subgroups of `GL(V)`,
for an arbitrary finite-dimensional `V`.**  This is the manuscript's classical
input in the generality in which the manuscript states it. -/
theorem wellFoundedLT_isZClosedSubgroupOfBasis (b : Module.Basis n k V) :
    WellFoundedLT {H : Subgroup (LinearMap.GeneralLinearGroup k V) //
      IsZClosedSubgroupOfBasis b H} := by
  exact wellFoundedLT_comap (Matrix.GeneralLinearGroup.toLin' b) IsZClosedSubgroup

end GLV

end ZariskiClosedSubgroup
end GroupApproximation

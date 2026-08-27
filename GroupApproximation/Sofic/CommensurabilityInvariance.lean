import GroupApproximation.Sofic.InducedCoronaMF
import GroupApproximation.Sofic.InducedFiniteDimensional
import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# Abstract commensurability and the approximation properties

Two groups are abstractly commensurable when one can pass to a finite-index subgroup in each and
land on the same abstract group.  Sections 46.5-46.7 and 49.2A-49.6 of the dossier observe that the
approximation properties studied here cannot tell such a pair apart: being MF, being residually
finite, and having no finite-dimensional unitary residual are all invariant under abstract
commensurability.

Only one direction of each invariance carries content.  Passing *down* to a subgroup is a
restriction: a faithful corona representation, a separating family of finite quotients, or a
separating family of finite-dimensional unitary representations restricts to any subgroup and stays
faithful, respectively separating.  Passing *up* from a finite-index subgroup is the induced
representation, and that is where the work lies; it is already done, in
`InducedCorona.isOperatorMF_of_finiteIndex_subgroup` for the corona, in
`InducedFdRep.fdUnitaryResidual_subgroupOf` for finite-dimensional unitaries, and in
`isResiduallyFinite_of_finiteIndex_subgroup` for finite quotients.  What remains here is the
bookkeeping that turns those three finite-index statements into commensurability statements: a
transport lemma along a group isomorphism for each property, and the composition of the descent,
the transport, and the rise.

The last consequence is Corollary 49.6 read backwards.  A group whose approximation failure is
hereditary — whose MF radical survives every passage to a finite-index subgroup — is commensurable
with no MF group at all, since a commensurable MF group would hand back an MF finite-index subgroup
on the other side.  Because the finite-index statement is an equivalence rather than an implication,
the same conclusion in fact needs only the failure of the ambient group, and both forms are
recorded.
-/

namespace GroupApproximation

namespace CommensurabilityInvariance

open InducedCorona InducedFdRep MatricialStabilityRadical

universe u v w

variable {G : Type u} [Group G] {H : Type v} [Group H] {K : Type w} [Group K]

/-! ## Abstract commensurability -/

/-- Abstract commensurability: each group has a finite-index subgroup, and those two subgroups are
isomorphic as abstract groups.  No compatibility between the two inclusions is required, which is
what distinguishes this from commensurability of two subgroups of one ambient group. -/
def AbstractlyCommensurable (G : Type u) [Group G] (H : Type v) [Group H] : Prop :=
  ∃ (A : Subgroup G) (B : Subgroup H), A.FiniteIndex ∧ B.FiniteIndex ∧ Nonempty (A ≃* B)

/-- Every group is abstractly commensurable with itself, witnessed by the whole group on both
sides. -/
theorem AbstractlyCommensurable.refl (G : Type u) [Group G] :
    AbstractlyCommensurable G G :=
  ⟨⊤, ⊤, inferInstance, inferInstance, ⟨MulEquiv.refl _⟩⟩

/-- Abstract commensurability is symmetric: invert the isomorphism and exchange the two
finite-index subgroups. -/
theorem AbstractlyCommensurable.symm (h : AbstractlyCommensurable G H) :
    AbstractlyCommensurable H G := by
  obtain ⟨A, B, hA, hB, ⟨e⟩⟩ := h
  exact ⟨B, A, hB, hA, ⟨e.symm⟩⟩

/-- Abstract commensurability is transitive.  Given `A ≃* B` with `B ≤ H` and `C ≃* D` with
`C ≤ H`, the intersection `B ⊓ C` is again finite index in `H`, and transporting it back through
the first isomorphism and forward through the second produces the required finite-index subgroups
of the two outer groups.  The index bookkeeping is `Subgroup.index_map_equiv` for the transport
along an isomorphism and `Subgroup.index_map_subtype` for the passage from a subgroup of a subgroup
to a subgroup of the ambient group. -/
theorem AbstractlyCommensurable.trans (hGH : AbstractlyCommensurable G H)
    (hHK : AbstractlyCommensurable H K) : AbstractlyCommensurable G K := by
  obtain ⟨A, B, hA, hB, ⟨e⟩⟩ := hGH
  obtain ⟨C, D, hC, hD, ⟨f⟩⟩ := hHK
  haveI := hA
  haveI := hB
  haveI := hC
  haveI := hD
  haveI : (((B ⊓ C).subgroupOf B).map (e.symm : B →* A)).FiniteIndex := by
    refine ⟨?_⟩
    rw [Subgroup.index_map_equiv]
    exact Subgroup.FiniteIndex.index_ne_zero
  haveI : (((B ⊓ C).subgroupOf C).map (f : C →* D)).FiniteIndex := by
    refine ⟨?_⟩
    rw [Subgroup.index_map_equiv]
    exact Subgroup.FiniteIndex.index_ne_zero
  refine ⟨(((B ⊓ C).subgroupOf B).map (e.symm : B →* A)).map A.subtype,
    (((B ⊓ C).subgroupOf C).map (f : C →* D)).map D.subtype, ⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · rw [Subgroup.index_map_subtype]
    exact Nat.mul_ne_zero Subgroup.FiniteIndex.index_ne_zero
      Subgroup.FiniteIndex.index_ne_zero
  · rw [Subgroup.index_map_subtype]
    exact Nat.mul_ne_zero Subgroup.FiniteIndex.index_ne_zero
      Subgroup.FiniteIndex.index_ne_zero
  · exact
      (Subgroup.equivMapOfInjective (((B ⊓ C).subgroupOf B).map (e.symm : B →* A))
            A.subtype A.subtype_injective).symm.trans
        ((e.symm.subgroupMap ((B ⊓ C).subgroupOf B)).symm.trans
          ((Subgroup.subgroupOfEquivOfLe (inf_le_left : B ⊓ C ≤ B)).trans
            ((Subgroup.subgroupOfEquivOfLe (inf_le_right : B ⊓ C ≤ C)).symm.trans
              ((f.subgroupMap ((B ⊓ C).subgroupOf C)).trans
                (Subgroup.equivMapOfInjective (((B ⊓ C).subgroupOf C).map (f : C →* D))
                  D.subtype D.subtype_injective)))))

/-! ## Transport along an isomorphism -/

/-- Operator-MF transports along a group isomorphism: compose a faithful corona representation of
the source with the inverse isomorphism. -/
theorem isOperatorMF_of_mulEquiv (e : G ≃* H) (hG : IsOperatorMF G) : IsOperatorMF H := by
  obtain ⟨X, hX, rho, hrho⟩ := hG
  exact ⟨X, hX, rho.comp e.symm.toMonoidHom, hrho.comp e.symm.injective⟩

/-- Residual finiteness transports along a group isomorphism, by functoriality of the finite
residual applied to the inverse isomorphism. -/
theorem isResiduallyFinite_of_mulEquiv (e : G ≃* H) (hG : IsResiduallyFinite G) :
    IsResiduallyFinite H := by
  refine le_antisymm ?_ bot_le
  rw [SetLike.le_def]
  intro x hx
  rw [Subgroup.mem_bot]
  have hmem : e.symm x ∈ (finiteResidual H).map (e.symm : H →* G) := ⟨x, hx, rfl⟩
  have hbot := map_finiteResidual_le (e.symm : H →* G) hmem
  rw [hG, Subgroup.mem_bot] at hbot
  have hval := congrArg e hbot
  simpa using hval

/-- The finite-dimensional unitary residual is carried across an isomorphism: an element of the
source is invisible to all finite-dimensional unitary representations exactly when its image
is. -/
theorem mem_fdUnitaryResidual_mulEquiv (e : G ≃* H) {x : G} :
    e x ∈ fdUnitaryResidual H ↔ x ∈ fdUnitaryResidual G := by
  constructor
  · intro hx
    rw [mem_fdUnitaryResidual_iff]
    intro Y phi
    have hphi := mem_fdUnitaryResidual_iff.mp hx Y (phi.comp e.symm.toMonoidHom)
    simpa using hphi
  · intro hx
    rw [mem_fdUnitaryResidual_iff]
    intro Y psi
    have hpsi := mem_fdUnitaryResidual_iff.mp hx Y (psi.comp e.toMonoidHom)
    simpa using hpsi

/-- Triviality of the finite-dimensional unitary residual transports along an isomorphism. -/
theorem fdUnitaryResidual_eq_bot_of_mulEquiv (e : G ≃* H) (hG : fdUnitaryResidual G = ⊥) :
    fdUnitaryResidual H = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [SetLike.le_def]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx' : e.symm x ∈ fdUnitaryResidual G := (mem_fdUnitaryResidual_mulEquiv e.symm).mpr hx
  rw [hG, Subgroup.mem_bot] at hx'
  have hval := congrArg e hx'
  simpa using hval

/-! ## Rising from a finite-index subgroup -/

/-- A group whose finite-index subgroup has no finite-dimensional unitary residual has none itself.
The residual lies in every finite-index subgroup, so it is already visible inside `B`, where
Theorem 49.2 identifies it with the trace of the ambient one. -/
theorem fdUnitaryResidual_eq_bot_of_finiteIndex_subgroup (B : Subgroup G) [B.FiniteIndex]
    (hB : fdUnitaryResidual B = ⊥) : fdUnitaryResidual G = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [SetLike.le_def]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxB : x ∈ B :=
    mem_finiteResidual_iff.mp (fdUnitaryResidual_le_finiteResidual hx) B inferInstance
  have hmem : (⟨x, hxB⟩ : B) ∈ fdUnitaryResidual B := by
    rw [fdUnitaryResidual_subgroupOf B]
    exact Subgroup.mem_subgroupOf.mpr hx
  rw [hB, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

/-! ## The three invariance theorems -/

/-- **Corollary 49.2A.**  Being operator-MF is an abstract-commensurability invariant: restrict a
faithful corona representation to the finite-index subgroup `A`, transport it across the
isomorphism to `B`, and induce it from `B` up to the whole of `H`. -/
theorem isOperatorMF_of_abstractlyCommensurable (hcomm : AbstractlyCommensurable G H)
    (hG : IsOperatorMF G) : IsOperatorMF H := by
  obtain ⟨A, B, -, hB, ⟨e⟩⟩ := hcomm
  haveI := hB
  exact isOperatorMF_of_finiteIndex_subgroup B (isOperatorMF_of_mulEquiv e (hG.subgroup A))

/-- **Corollary 49.2B(1).**  Residual finiteness is an abstract-commensurability invariant. -/
theorem isResiduallyFinite_of_abstractlyCommensurable (hcomm : AbstractlyCommensurable G H)
    (hG : IsResiduallyFinite G) : IsResiduallyFinite H := by
  obtain ⟨A, B, -, hB, ⟨e⟩⟩ := hcomm
  haveI := hB
  exact isResiduallyFinite_of_finiteIndex_subgroup
    (isResiduallyFinite_of_mulEquiv e (hG.subgroup A))

/-- **Corollary 49.3.**  Triviality of the finite-dimensional unitary residual is an
abstract-commensurability invariant.  Unlike the previous two, the descent step here also uses
finiteness of the index, since it is read off the exact heredity statement rather than from a bare
restriction. -/
theorem fdUnitaryResidual_eq_bot_of_abstractlyCommensurable
    (hcomm : AbstractlyCommensurable G H) (hG : fdUnitaryResidual G = ⊥) :
    fdUnitaryResidual H = ⊥ := by
  obtain ⟨A, B, hA, hB, ⟨e⟩⟩ := hcomm
  haveI := hA
  haveI := hB
  exact fdUnitaryResidual_eq_bot_of_finiteIndex_subgroup B
    (fdUnitaryResidual_eq_bot_of_mulEquiv e (fdUnitaryResidual_eq_bot_of_finiteIndex A hG))

/-! ## Corollary 49.6: hereditary failure blocks every commensurable MF group -/

/-- **Corollary 49.6.**  If no finite-index subgroup of `G` is operator-MF, then no group abstractly
commensurable with `G` is operator-MF: such a group would have a finite-index subgroup that is MF
by restriction, and the commensurating isomorphism would carry that back to a finite-index subgroup
of `G`. -/
theorem not_isOperatorMF_of_hereditary_failure
    (hfail : ∀ A : Subgroup G, A.FiniteIndex → ¬ IsOperatorMF A)
    (hcomm : AbstractlyCommensurable G H) : ¬ IsOperatorMF H := by
  intro hH
  obtain ⟨A, B, hA, -, ⟨e⟩⟩ := hcomm
  exact hfail A hA (isOperatorMF_of_mulEquiv e.symm (hH.subgroup B))

/-- **Corollary 49.6 in its radical form.**  If the MF radical of every finite-index subgroup of a
countable group `G` is nontrivial — the hereditary approximation failure of Theorem 49.5, which
belongs to the concrete family and is not discharged here — then `G` is abstractly commensurable
with no MF group. -/
theorem not_isOperatorMF_of_mfRadical_survives_finiteIndex [Countable G]
    (hsurv : ∀ A : Subgroup G, A.FiniteIndex → actualCoronaMFResidual A ≠ ⊥)
    (hcomm : AbstractlyCommensurable G H) : ¬ IsOperatorMF H := by
  refine not_isOperatorMF_of_hereditary_failure (fun A hA hMF => hsurv A hA ?_) hcomm
  rw [actualCoronaMFResidual_eq_coronaMFResidual]
  exact isOperatorMF_iff_coronaMFResidual_eq_bot.mp hMF

/-- Because the finite-index statement is an equivalence, failure of the MF property in `G` alone
already blocks every commensurable MF group; the hereditary hypothesis of Corollary 49.6 buys the
stronger conclusion that no finite-index subgroup is MF either. -/
theorem not_isOperatorMF_of_abstractlyCommensurable (hcomm : AbstractlyCommensurable G H)
    (hG : ¬ IsOperatorMF G) : ¬ IsOperatorMF H :=
  fun hH => hG (isOperatorMF_of_abstractlyCommensurable hcomm.symm hH)

end CommensurabilityInvariance

end GroupApproximation

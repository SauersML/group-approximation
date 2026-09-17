import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2Endpoints
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Sofic.CentralCoverInheritance
import GroupApproximation.Leavitt.UniversalLeavittOver
import GroupApproximation.Meta.AxiomGuard

/-!
# Interfaces for the rank-four criterion over `L = L_{𝔽₂}(1,2)` (lane sk-leavitt-15)

Census row `768ac9454e9b` (tex l.733–735): "Infinite finitely presented simple Kazhdan groups
exist~\cite{CapraceRemy}, and whether one of them is sofic, or at least hyperlinear, remains open."

The existence clause is closed in `LeavittFP.K2RankFourEndpoints` from the live gap
`LeavittFP.BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement`
(`K₂(4, L)` is finitely normally generated).  Khanh's criterion (arXiv:2609.08428, Thm 5.1 at
`n = 4`) reduces `K₂(4, L) = ⊥` to superperfectness of `Lˣ`, in two steps that other lanes of
carto `sk-leavitt` author in parallel:

* lane sk-leavitt-04: superperfect `Lˣ` gives `stab (K₂(3, L)) = ⊥` in `St_4(L)`;
* lane sk-leavitt-14: `stab (K₂(3, L)) = ⊥` gives `K₂(4, L) = ⊥` (Brown presentation over the
  ordered frame complex `X_4(L)`).

Neither lane is on disk yet.  This module states their interfaces as `Prop`s in the
sub-namespace `EndpointInterfaces`.  The sub-namespace keeps the names apart from the
declarations the two lanes create in `LeavittK2`.  The bodies copy the texts fixed in the carto,
so after the lanes land each interface is discharged by the lane's theorem, up to `Iff.rfl`.

## Truth check

* `BinaryLeavittUnitsSuperperfectStatement` is true.  `Lˣ` is acyclic (Khanh Thm 2.2), so
  `H₂(Lˣ) = 0`, and `Lˣ` is perfect (`BinaryLeavitt.binaryLeavittUnits_perfect`).  A perfect
  central extension of a superperfect group is an isomorphism.
* `BinaryLeavittStabKernelThreeTrivialStatement` is true: `K₂(3, L) = ⊥` by Khanh Thm 5.4.
* The two implications are true, because their conclusions are true.  The carto also gives
  elementary proofs of both (lanes 02–05 and 06–14).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces

/-- **The gap (lane sk-leavitt-04 text).**  The unit group of `L = L_{𝔽₂}(1,2)` is
superperfect: every central extension `E ↠ Lˣ` with `E` perfect is injective, i.e.
`H₂(Lˣ) = 0` (given `Lˣ` perfect).

*Why it is true.*  Khanh (arXiv:2609.08428), Theorem 2.2: `Lˣ` is acyclic.  Not proved in Lean. -/
def BinaryLeavittUnitsSuperperfectStatement : Prop :=
  ∀ (E : Type) [Group E]
    (P : GroupApproximation.CentralExtension E
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ),
    commutator E = ⊤ → Function.Injective P.projection

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement

/-- **Lane sk-leavitt-04 intermediate.**  The padding `stab : St_3(L) → St_4(L)` (along
`Fin.castSucc`) kills `K₂(3, L)`. -/
def BinaryLeavittStabKernelThreeTrivialStatement : Prop :=
  (GroupApproximation.BooneHigman.SteinbergBasic.K2n 3
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).map
    (GroupApproximation.BooneHigman.SteinbergBasic.stab 3
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) = ⊥

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement

/-- **Interface of lane sk-leavitt-04** (`stabKernelThreeTrivial_of_superperfect`): superperfect
units kill the padded rank-three kernel.

*Route (lane 04).*  `E = St_3/⁅⊤, K₂(3)⁆` is a perfect central extension of
`E_3(L) = GL_3(L) ≅ Lˣ`, so superperfectness gives `K₂(3) ≤ ⁅⊤, K₂(3)⁆`.  Padded centrality
(lane 03) then kills `stab (K₂(3))`. -/
def StabKernelThreeTrivialOfSuperperfectStatement : Prop :=
  BinaryLeavittUnitsSuperperfectStatement → BinaryLeavittStabKernelThreeTrivialStatement

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces.StabKernelThreeTrivialOfSuperperfectStatement

/-- **Interface of lane sk-leavitt-14** (`rankFourInjective_of_stabKernelThreeTrivial`): Khanh's
criterion at `n = 4`.  If `stab` kills `K₂(3, L)`, then `K₂(4, L) = ⊥`.

*Route (lane 14).*  Brown's presentation of `GL_4(L)` over the simply connected ordered frame
complex `X_4(L)` lifts to `St_4(L)` through the vertex-stabilizer section and the Weyl element.
This gives a surjective section of `St_4(L) → E_4(L)`. -/
def RankFourInjectiveOfStabKernelThreeTrivialStatement : Prop :=
  BinaryLeavittStabKernelThreeTrivialStatement →
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces

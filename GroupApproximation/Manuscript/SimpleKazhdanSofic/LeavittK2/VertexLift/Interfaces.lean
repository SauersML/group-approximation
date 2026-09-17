import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.RowVec
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces
import GroupApproximation.KOne.AllRanksElementaryCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Upstream interface for the vertex-stabilizer section (lane sk-leavitt-05)

Carto `sk-leavitt`, lane 05 needs two inputs.

* `stab (K₂(3, L)) = ⊥` in `St_4(L)`.  This exists on disk as
  `EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement` (lane 15), and this lane takes
  it as a hypothesis, just as the lane signature `liftGL (h : …)` prescribes.
* The conjugation formula `stab_conj_rowVec` from lane sk-leavitt-02 (`LK2/RowColumn`), which is
  not on disk.  `RowVecStabConjStatement` below is its special case `n = 3`, `R = L`, stated for
  the local `VertexLift.rowVec`.

## Truth check

Let `g ∈ St_3(L)` with `M = projection g ∈ E_3(L)`.  In `E_4(L)` the element `stab g` is
`[[M, 0], [0, 1]]` and `rowVec b` is `[[1, 0], [b, 1]]`.  Their conjugate is
`[[1, 0], [b M⁻¹, 1]]`, so the formula holds after projection.  In `St_4(L)` it is checked on the
generators `x_{ik}(a)` of `St_3` (with `i, k ≠ last`):

* `x_{ik}(a)` commutes with `x_{last,j}(c)` for `j ≠ i` (`x_commute_of_ne`, since `k ≠ last`);
* `x_{ik}(a) x_{last,i}(c) x_{ik}(-a) = x_{last,i}(c) x_{last,k}(-c a)`, by the Steinberg
  commutator relation with the index `last`.

Both sides define a left action of `St_3` on `L^3`, so the formula extends from generators to
the whole group.  So the Statement is true.  It is strictly weaker than lane 02's
`stab_conj_rowVec`, which covers every ring and every rank.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic

local notation "𝓛" => GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)

/-- **Interface of lane sk-leavitt-02 at `n = 3`, `R = L`** (`stab_conj_rowVec`): conjugating the
bottom-row vector by a padded Steinberg element multiplies the row by the inverse projection,
`stab g · x_last(b) · (stab g)⁻¹ = x_last(b · (projection g)⁻¹)`.

*Why it is true.*  See the module docstring: the formula is checked on the generators `x_{ik}(a)`
by the Steinberg relations, and it extends because both sides are actions.  Not proved in
this lane. -/
def RowVecStabConjStatement : Prop :=
  ∀ (g : St 3 𝓛) (b : Fin 3 → 𝓛),
    stab 3 𝓛 g * rowVec b * (stab 3 𝓛 g)⁻¹ =
      rowVec (b ᵥ* ((((projection g)⁻¹ : elementaryGroup (Fin 3) 𝓛) :
        (Matrix (Fin 3) (Fin 3) 𝓛)ˣ) : Matrix (Fin 3) (Fin 3) 𝓛))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.RowVecStabConjStatement

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift

import GroupApproximation.GGT.HullSCRelatorSeparation2Extract

/-!
# The other-arc clause, discharged

`GGT.OsinComponents.exists_two_block_conj_of_rot` carries one configuration
clause: no component start past the `s`-component or before the `q`-component is
connected to the `s`-component.  In the configuration this chain builds it holds
**vacuously**, because neither range contains a component start at all, and the
two reasons are different.

*Before the `q`-component.*  The range is `o < |p| + i`, and `i = 0` because `q`
is a single block letter -- each block letter of the alternating relator is its
own maximal component (`HullSC.isComp_relatorWord₂`), so a component of the run
spans one letter and starts at its own position.  So the range is `o < |p|`,
where every letter is a letter of `p`, and `p` is base-spelled.  A base letter
carries no index, so there is no component start below `|p|` at all:
`not_isCompStart_of_baseSpelled`.

*Past the `s`-component.*  The range is
`|p| + |q| + |r| + (|s| - l) < o < |w|`, and with `q` and `s` single letters,
`l = |s| = 1`, so the lower bound is `|w| - 1` and the upper is `|w|`.  No
natural number lies strictly between them: the range is empty, and the clause
holds with nothing to check.

Both halves come from the same fact about the relator -- that its blocks are
single-letter components -- which is what `Λ = Bool` and the alternation buy and
what the `Λ = Unit` model could not give.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section OtherArc

variable {G : Type u} [Group G] {Λ : Type w}

omit [Group G] in
/-- **A base-spelled prefix carries no component start.** -/
theorem not_isCompStart_of_baseSpelled {lam : Λ}
    {pre rest : List (GGT.RelLetter G Λ)}
    (hp : ∀ a ∈ pre, ∃ y : G, a = GGT.RelLetter.base y) {o : ℕ}
    (ho : o < pre.length) :
    ¬ GGT.OsinComponents.IsCompStart lam (pre ++ rest) o := by
  rintro ⟨k, hcomp⟩
  have hlen : o < (pre ++ rest).length := by
    rw [List.length_append]
    omega
  have hidx : (pre ++ rest)[o]'hlen = pre[o]'ho := List.getElem_append_left ho
  obtain ⟨y, hy⟩ := hp (pre[o]'ho) (List.getElem_mem ho)
  have hcompof : ((pre ++ rest)[o]'hlen).IsCompOf lam :=
    hcomp.2.2.1 o le_rfl hcomp.1 hlen
  rw [hidx, hy] at hcompof
  exact not_isCompOf_base lam y hcompof

end OtherArc

end HullSC
end GroupApproximation

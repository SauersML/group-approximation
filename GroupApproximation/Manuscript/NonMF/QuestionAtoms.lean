import GroupApproximation.Sofic.LiteralSignFreeQuotient
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Elementary quotient and torsion-free atoms

Earlier manuscript revisions used the following elementary facts in two open
questions.  The questions have since been answered in the paper, but the facts
remain useful to delimit the formal reductions.

The first pair says that neither quotient operation alone constrains
`Res_MF((E/⟨w⟩)/D)`, "because the elements they detect have already been
killed: `w` is trivial in `E/⟨w⟩`, and the commutators generating `D` are
trivial in the quotient by `D`".  The first clause is
`signFreeQuotient_mark_eq_one`, at the manuscript's own quotient; the second is
`map_eq_one_of_mem_normalClosure` in the generality the sentence uses it.

The second pair says that the Clifford construction itself cannot produce a torsion-free
finitely presented non-MF group: "it imposes `c² = 1`, so `d² = 1`, and a
torsion-free quotient `q` then has `q(d) = 1` and `q(N_conj) = 1`".  The first
conclusion is `map_eq_one_of_sq_eq_one_of_isMulTorsionFree`, and the second
follows from it and the first file's normal-closure lemma, because `N_conj` is
by `def:pattern` the normal closure of the commutators `[d, ι(λ)]` and each of
those dies as soon as `q(d)` does.  `cliffordTorsionFreeObstruction` is that
composite, stated over an arbitrary normal-closure presentation of `N_conj` so
that it applies to the printed datum without naming it.

Nothing here is deep and nothing here is new; what it is, is *stated*.

Wired into the root import closure on 2026-08-17, which is the first time any of
it was elaborated.  It did not elaborate as written: `map_eq_one_of_mem_normalClosure`
passed `q` to `MonoidHom.mem_ker`, whose `f` is implicit in the pinned Mathlib
(`Algebra/Group/Subgroup/Ker.lean`), so the term applied an `Iff` to an argument.
Every other use of that lemma in this repository spells it bare, and it now does
too.  Nothing else changed, and the four statements are as they were.

These declarations no longer certify an open-status claim.  In particular,
they do not contradict the manuscript's present torsion-free construction,
which uses a different small-cancellation route at paper level.
-/

namespace GroupApproximation
namespace ManuscriptNonMF

open scoped commutatorElement

universe u v

/-! ## The two quotient operations -/

/-- **"`w` is trivial in `E/⟨w⟩`."**  The manuscript's sign-free quotient is by
`Subgroup.zpowers mark`, so the distinguished word is killed by construction.
This is the elementary quotient fact used by the former reduction. -/
theorem signFreeQuotient_mark_eq_one :
    LiteralSignFreeQuotient.proj LiteralNonMFPresentation.mark = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)

/-- **"The commutators generating `D` are trivial in the quotient by `D`."**  A
homomorphism killing a generating set of a normal closure kills the whole normal
closure, because its kernel is a normal subgroup containing the set.  The former
reduction used this at `D = D_coll(L,s)`; the statement is general, since nothing
in the sentence depends on which normal closure it is. -/
theorem map_eq_one_of_mem_normalClosure {H : Type u} [Group H] {Q : Type v}
    [Group Q] (q : H →* Q) {S : Set H} (hS : ∀ s ∈ S, q s = 1) {x : H}
    (hx : x ∈ Subgroup.normalClosure S) : q x = 1 :=
  Subgroup.normalClosure_le_normal (N := q.ker)
    (fun s hs => MonoidHom.mem_ker.2 (hS s hs)) hx

/-! ## Why the Clifford construction itself cannot be torsion-free -/

/-- **"`c² = 1`, so `d² = 1`, and a torsion-free quotient `q` then has
`q(d) = 1`."**  An involution has an image of order dividing two, and a
torsion-free group has no such element but the identity. -/
theorem map_eq_one_of_sq_eq_one_of_isMulTorsionFree {H : Type u} [Group H]
    {Q : Type v} [Group Q] [IsMulTorsionFree Q] (q : H →* Q) {d : H}
    (hd : d ^ 2 = 1) : q d = 1 := by
  refine IsOfFinOrder.eq_one' (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, ?_, ?_⟩)
  · exact Nat.succ_pos 1
  · rw [← map_pow, hd, map_one]

/-- **The torsion-free Clifford obstruction.**  Let `d` be an involution of `H`, let
`N` be the normal closure of a set every element of which is a commutator
`[d, a]`, and let `q` be a homomorphism to a torsion-free group.  Then `q` kills
`d` and kills all of `N`.

The manuscript's `N_conj` is exactly such a normal closure, of
`{[d, ι(λ)] : λ ∈ Λ}` by `def:pattern`, and the Clifford construction's `c² = 1`
gives `d² = (tct⁻¹)² = tc²t⁻¹ = 1`.  Stating the hypothesis as "every element of
the generating set is a commutator with `d`" rather than naming `ι` keeps this
free of the construction's own definitions while remaining the printed
inference. -/
theorem cliffordTorsionFreeObstruction {H : Type u} [Group H] {Q : Type v}
    [Group Q] [IsMulTorsionFree Q] (q : H →* Q) {d : H} (hd : d ^ 2 = 1)
    {S : Set H} (hS : ∀ s ∈ S, ∃ a : H, s = ⁅d, a⁆) :
    q d = 1 ∧ ∀ x ∈ Subgroup.normalClosure S, q x = 1 := by
  have hqd : q d = 1 := map_eq_one_of_sq_eq_one_of_isMulTorsionFree q hd
  refine ⟨hqd, fun x hx => map_eq_one_of_mem_normalClosure q ?_ hx⟩
  rintro s hs
  obtain ⟨a, rfl⟩ := hS s hs
  rw [map_commutatorElement, hqd, commutatorElement_one_left]

end ManuscriptNonMF
end GroupApproximation

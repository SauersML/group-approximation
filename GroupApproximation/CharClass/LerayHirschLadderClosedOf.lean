import GroupApproximation.CharClass.LerayHirschColSumOf
import GroupApproximation.CharClass.ProjectiveSpaceRingClosedOf
import GroupApproximation.Meta.AxiomGuard

/-!
# Leray–Hirsch at general rank over a field, unconditionally

The coefficient-generic form of `LerayHirschLadderClosed`.  Both clauses of `HasFreeTuple` are proved
over any field `K`, against any nonzero fibre class `hfib ∈ H^2(ℂP^{d+1}; K)`:

* spanning is `exists_freeTupleOf` (every class is a column, by peeling towers);
* uniqueness is `freeTuple_uniqueOf` (a column summing to zero is zero, by the freeness of towers).

Both take the ring input `KnCP.CPRingOf K`, and `CPn.cupPowE_ne_zeroOf` proves it outright, so the free
tuple of `U × ℂP^{d+1} → U` holds with no hypothesis.

## Main declarations

* `LH.hasFreeTuple_cpProdOf_of_ring` — the free-module statement over the ring input.
* `LH.ladderRingInputOf` — the ring input, from `CPn.cupPowE_ne_zeroOf`.
* `LH.hasFreeTuple_cpProd_generalOf` — **the free-module statement, unconditionally**, at the
  tower's projections.
* `LH.hasFreeTuple_cpProdOf` — the same at the chart step's projections `cpFst`/`cpSnd`.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

/-- **The free-module statement over `K`, over the ring input.**  Both clauses, at every degree and
every rank, over an arbitrary base and any nonzero fibre class. -/
theorem hasFreeTuple_cpProdOf_of_ring (K : Type) [Field K] (hring : KnCP.CPRingOf K)
    (U : Type) [TopologicalSpace U] (d : ℕ) (hfib : Hmod K (CPtop (d + 1)) 2)
    (hfib0 : hfib ≠ 0) :
    HasFreeTuple (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 hfib) (d + 2) :=
  fun n =>
    ⟨fun z => exists_freeTupleOf K U d hring hfib hfib0 n z,
      fun a hside hzero => freeTuple_uniqueOf K U d hring hfib hfib0 n a hside hzero⟩

/-- **The ring input over `K` holds outright**: the powers of a nonzero degree-two class of `ℂP^d`
are nonzero up to the dimension. -/
theorem ladderRingInputOf (K : Type) [Field K] : KnCP.CPRingOf K :=
  fun d hd h h0 _ hm => CPn.cupPowE_ne_zeroOf K d hd h h0 hm

/-- **The free-module statement over `K`, unconditionally.** -/
theorem hasFreeTuple_cpProd_generalOf (K : Type) [Field K] (U : Type) [TopologicalSpace U]
    (d : ℕ) (hfib : Hmod K (CPtop (d + 1)) 2) (hfib0 : hfib ≠ 0) :
    HasFreeTuple (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 hfib) (d + 2) :=
  hasFreeTuple_cpProdOf_of_ring K (ladderRingInputOf K) U d hfib hfib0

/-- **The free-module statement over `K`, unconditionally**, at the projections `cpFst`/`cpSnd` the
chart step of compact Leray–Hirsch takes for its `hfree`.  `cpFst U (d + 1)` and `cpPrU U d` are the
same map, both abbreviations of the first projection of `U × ℂP^{d+1}`. -/
theorem hasFreeTuple_cpProdOf (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)
    (_hd : 1 ≤ d + 1) (hfib : Hmod K (CPtop (d + 1)) 2) (hfib0 : hfib ≠ 0) :
    HasFreeTuple (KnCP.cpFst U (d + 1)) (pull (KnCP.cpSnd U (d + 1)) 2 hfib) (d + 2) :=
  hasFreeTuple_cpProd_generalOf K U d hfib hfib0

end

#audit_axioms hasFreeTuple_cpProdOf_of_ring
#audit_axioms ladderRingInputOf
#audit_axioms hasFreeTuple_cpProd_generalOf
#audit_axioms hasFreeTuple_cpProdOf

end LH
end CharClass
end GroupApproximation

import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngRank3BldLoop
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngRank3FillCore
import Mathlib.Order.Lattice.Nat
import GroupApproximation.Meta.AxiomGuard

/-!
# Coset-graph filling for `czK2FngRank3Bld_LoopStatement` (lane `bh-met-93z`, part 2)

Put `S = ℤ[1/(mp)]`, `X = E_3(S)/φ(E_3(ℤ[1/m]))` (`czK2FngRank3Bld_X`), `y₀ = [1]`, and let the
free group `F` on the letters `a₀₁, a₁₂, a₂₀, u₀₁` act on `X` through `evE`.

**Concrete combing.**
* `czK2FngRank3Fill_ht y` is the Schreier-graph distance from `y₀` to `y`: the least length of
  a list `l` of signed letters with `evE (mk l) • y₀ = y` (`sInf`, so `0` if `y` is not
  reached).  With this height the *descent* half of the route is automatic: every vertex of
  positive height has a letter-neighbour of smaller height (the last step of a geodesic).
* `czK2FngRank3Fill_sigma y` is `1` at `y₀`, and otherwise a geodesic word to `y`
  (`Classical.epsilon`).

**The new residual `czK2FngRank3Fill_LocalStatement` (local filling).**  There is a finite
set `L` of relator words (`evE ℓ = 1`) such that, for every letter `a` and vertex `y`, the
Schreier generator `σ(a • y)⁻¹ · a · σ(y)` of the edge `y —a→ a • y` lies in
`(⟪L⟫ ⊔ ⟨base loops⟩) ⊔ ⟨Schreier generators of edges of strictly smaller height⟩`.
That is: each edge-loop is filled by `L`-cells and base loops *modulo loops lower down*.

**Proved outright.**
* `czK2FngRank3Fill_loop_of_local : LocalStatement → czK2FngRank3Bld_LoopStatement`, by the
  height induction `czK2FngRank3Fill_schGen_mem_of_local` and Schreier rewriting
  `czK2FngRank3Fill_mem_of_schGen` (file `...FillCore`).
* `czK2FngRank3Fill_residual_of_local`, `czK2FngRank3Fill_rankThree_of_local`: through
  `czK2FngRank3Bld_residual_of_loop` and `czK2FngRank3Bld_rankThree_of_loop`.

**Strength and truth (LOUD).**
* It is *not* logically weaker than the loop statement: granting that every vertex is
  reached by a word (true, since the four matrices generate `E_3(S)`), the loop statement
  with the same `L` gives it at once (each Schreier generator fixes `y₀`).  What it removes
  is proof content: the Schreier rewriting of arbitrary closed paths and the induction over
  the height are now proved.  Only the loop at one edge must be filled, and the loops of
  strictly lower edges may be used freely.
* True by that argument, given the truth of the loop statement (via Behr; truth argument
  only, never a hypothesis).
* The naive *lattice-height* descent is FALSE, which is why the height is the graph distance.
  For `h = e₃ − e₁` (elementary-divisor spread of the `p`-local lattice), `a₀₁, a₁₂, a₂₀`
  lie in `SL_3(ℤ_(p))`, so they preserve `h`.  The script `$SP/bh-met-93z/fill_check.py`
  finds many vertices with no `h`-descending letter.  It also checks the telescoping
  identity behind `czK2FngRank3Fill_telescope` on every closed word of length `≤ 6` at `y₀`
  (`p = 2, 3`, `m = 1, 5`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- The Schreier-graph distance from `y₀ = [1]` (the least length of a signed-letter list
reaching `y`; `0` if there is none). -/
noncomputable def czK2FngRank3Fill_ht (m p : ℕ) (y : czK2FngRank3Bld_X m p) : ℕ :=
  sInf {n | ∃ l : List (czK2FngRank3Bld_Letter × Bool), l.length = n ∧
    czK2FngRank3Bld_evE m p (FreeGroup.mk l) • (QuotientGroup.mk 1 : czK2FngRank3Bld_X m p) =
      y}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Fill_ht

open scoped Classical in
/-- The combing: `1` at `y₀`, otherwise a geodesic word from `y₀` to `y`. -/
noncomputable def czK2FngRank3Fill_sigma (m p : ℕ) (y : czK2FngRank3Bld_X m p) :
    FreeGroup czK2FngRank3Bld_Letter :=
  if y = QuotientGroup.mk 1 then 1 else
    FreeGroup.mk (Classical.epsilon fun l : List (czK2FngRank3Bld_Letter × Bool) ↦
      l.length = czK2FngRank3Fill_ht m p y ∧
        czK2FngRank3Bld_evE m p (FreeGroup.mk l) •
          (QuotientGroup.mk 1 : czK2FngRank3Bld_X m p) = y)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Fill_sigma

theorem czK2FngRank3Fill_sigma_base (m p : ℕ) :
    czK2FngRank3Fill_sigma m p (QuotientGroup.mk 1 : czK2FngRank3Bld_X m p) = 1 := by
  rw [czK2FngRank3Fill_sigma]
  exact if_pos rfl

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Fill_sigma_base

/-- **The local-filling residual (lane `bh-met-93z`).**  Finitely many relator words `L` fill
every edge-loop `σ(a • y)⁻¹ · a · σ(y)` by `L`-cells and base loops, modulo the edge-loops of
strictly smaller height. -/
def czK2FngRank3Fill_LocalStatement : Prop :=
  ∀ m p : ℕ, 0 < m → p.Prime → ¬ p ∣ m →
    ∃ L : Set (FreeGroup czK2FngRank3Bld_Letter), L.Finite ∧
      (∀ ℓ ∈ L, czK2FngRank3Bld_evE m p ℓ = 1) ∧
      ∀ (a : czK2FngRank3Bld_Letter) (y : czK2FngRank3Bld_X m p),
        czK2FngRank3Fill_schGen (czK2FngRank3Bld_evE m p) (czK2FngRank3Fill_sigma m p) a y ∈
          (Subgroup.normalClosure L ⊔ Subgroup.closure (czK2FngRank3Bld_baseLoops p)) ⊔
            Subgroup.closure (czK2FngRank3Fill_lower (czK2FngRank3Bld_evE m p)
              (czK2FngRank3Fill_sigma m p) (czK2FngRank3Fill_ht m p)
              (czK2FngRank3Fill_level (czK2FngRank3Bld_evE m p) (czK2FngRank3Fill_ht m p) a y))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Fill_LocalStatement

/-- **Local filling gives the loop statement.** -/
theorem czK2FngRank3Fill_loop_of_local (h : czK2FngRank3Fill_LocalStatement) :
    czK2FngRank3Bld_LoopStatement := by
  intro m p hm hp hpm
  obtain ⟨L, hLf, hL1, hloc⟩ := h m p hm hp hpm
  refine ⟨L, hLf, hL1, fun w hw ↦ ?_⟩
  exact czK2FngRank3Fill_mem_of_schGen (czK2FngRank3Bld_evE m p) _
    (czK2FngRank3Fill_sigma m p) (czK2FngRank3Fill_sigma_base m p) _
    (czK2FngRank3Fill_schGen_mem_of_local _ _ (czK2FngRank3Fill_ht m p) _ hloc) hw

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Fill_loop_of_local

/-- **Local filling gives the residual** `czK2FngRank3Sec_ResidualStatement`. -/
theorem czK2FngRank3Fill_residual_of_local (h : czK2FngRank3Fill_LocalStatement) :
    czK2FngRank3Sec_ResidualStatement :=
  czK2FngRank3Bld_residual_of_loop (czK2FngRank3Fill_loop_of_local h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Fill_residual_of_local

/-- **Local filling gives the target** `czK2FngGtOne_RankThreeStatement`. -/
theorem czK2FngRank3Fill_rankThree_of_local (h : czK2FngRank3Fill_LocalStatement) :
    czK2FngGtOne_RankThreeStatement :=
  czK2FngRank3Bld_rankThree_of_loop (czK2FngRank3Fill_loop_of_local h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Fill_rankThree_of_local

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

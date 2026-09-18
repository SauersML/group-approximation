import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.HopfFiveTerm.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# The Hopf five-term step: trivial multiplier and a perfect cover give `N = [S, N]`

Lane `sk-rows-15`.  Let `p : S ↠ G` be surjective with `S` perfect and `G` of trivial multiplier
(`HopfMultiplierTrivial`).  Then `ker p ≤ ⁅S, ker p⁆`.  This is the group-theory half of Khanh
(arXiv:2609.08428v1), Theorem 5.4: `N₃ = [S₃, N₃]`.

## Truth check

It is the five-term exact sequence `H₂(S) → H₂(G) → N/[S, N] → H₁(S) → H₁(G)` with `H₂(G) = 0` and
`H₁(S) = 0`, so it is true.  The proof below is elementary and does not need the sequence.

## Route

Let `q : F = FreeGroup S ↠ S` be `FreeGroup.prod` (surjective) and `f = p ∘ q`, a free
presentation of `G` with kernel `R'`.  Take `n ∈ ker p`.
1. `q` maps `[F, F]` onto `[S, S] = S` (`Subgroup.map_commutator`, `map_top_of_surjective`), so
   `n = q x` for some `x ∈ [F, F]`.
2. `f x = p n = 1`, so `x ∈ R' ∩ [F, F] ≤ [F, R']` by the trivial multiplier.
3. `n = q x ∈ q [F, R'] = [q F, q R'] = [S, q R'] ≤ [S, ker p]`, since `q R' ≤ ker p`.
-/

universe u

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.HopfFiveTerm

/-- **Hopf five-term step.**  If `p : S ↠ G` is surjective, `S` is perfect and `G` has trivial
multiplier, then `ker p ≤ ⁅S, ker p⁆` (so `ker p = ⁅S, ker p⁆`). -/
theorem le_commutator_of_hopfMultiplierTrivial {S G : Type u} [Group S] [Group G]
    (p : S →* G) (hp : Function.Surjective p) (hS : commutator S = ⊤)
    (hG : HopfMultiplierTrivial G) : p.ker ≤ ⁅(⊤ : Subgroup S), p.ker⁆ := by
  intro n hn
  obtain ⟨q, hq⟩ : ∃ q : FreeGroup S →* S, Function.Surjective q :=
    ⟨FreeGroup.prod, FreeGroup.prod_surjective⟩
  have hf : Function.Surjective (p.comp q) := by
    intro g
    obtain ⟨s, rfl⟩ := hp g
    obtain ⟨x, rfl⟩ := hq s
    exact ⟨x, rfl⟩
  have hmapTop : (⊤ : Subgroup (FreeGroup S)).map q = ⊤ := Subgroup.map_top_of_surjective q hq
  -- Step 1: `q` maps `[F, F]` onto `S`.
  have hcomm : (commutator (FreeGroup S)).map q = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, hmapTop, ← _root_.commutator_def S, hS]
  have hn' : n ∈ (commutator (FreeGroup S)).map q := by
    rw [hcomm]
    exact Subgroup.mem_top n
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hn'
  -- Step 2: the trivial multiplier puts `x` in `[F, R']`.
  have hxker : x ∈ (p.comp q).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact MonoidHom.mem_ker.mp hn
  have hxc : x ∈ ⁅(⊤ : Subgroup (FreeGroup S)), (p.comp q).ker⁆ :=
    hG S (p.comp q) hf (Subgroup.mem_inf.mpr ⟨hxker, hx⟩)
  -- Step 3: push forward along `q`.
  have himage : q x ∈ ⁅(⊤ : Subgroup S), (p.comp q).ker.map q⁆ := by
    rw [← hmapTop, ← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem q hxc
  refine Subgroup.commutator_mono le_rfl ?_ himage
  rintro _ ⟨y, hy, rfl⟩
  rw [MonoidHom.mem_ker]
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
  exact hy

#audit_axioms
  GroupApproximation.SimpleKazhdanSofic.SkRows.HopfFiveTerm.le_commutator_of_hopfMultiplierTrivial

/-- The equality form: `ker p = ⁅S, ker p⁆` (the reverse inclusion holds since `ker p` is normal). -/
theorem ker_eq_commutator_of_hopfMultiplierTrivial {S G : Type u} [Group S] [Group G]
    (p : S →* G) (hp : Function.Surjective p) (hS : commutator S = ⊤)
    (hG : HopfMultiplierTrivial G) : p.ker = ⁅(⊤ : Subgroup S), p.ker⁆ :=
  le_antisymm (le_commutator_of_hopfMultiplierTrivial p hp hS hG)
    (Subgroup.commutator_le_right ⊤ p.ker)

#audit_axioms
  GroupApproximation.SimpleKazhdanSofic.SkRows.HopfFiveTerm.ker_eq_commutator_of_hopfMultiplierTrivial

end GroupApproximation.SimpleKazhdanSofic.SkRows.HopfFiveTerm

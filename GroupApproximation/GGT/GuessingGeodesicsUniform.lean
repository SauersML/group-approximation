import GroupApproximation.GGT.GuessingGeodesicsBootstrap

/-!
# The bound is uniform: one instantiation closes the recursion

`GGT/GuessingGeodesicsBootstrap.lean` relates the bound at a scale to the bound
at a scale its own value determines, and `GGT/GuessingGeodesicsGrowth.lean` says
that beyond some radius the dyadic bound is smaller than the scale.  Put
together, they force the bound to be constant.

## Why one instantiation is enough

Write `F n = 2 · pathBound n + 4K + 2`.  The bootstrap gives `F n ≤ F (F n) + 6K`,
and the dyadic bound gives `F m + 6K < m` for every `m` past the radius `r`.
Suppose `F n` exceeded `r` for some `n`.  Then the second fact may be read **at
`m = F n`**, giving `F (F n) + 6K < F n`, against the first.  So `F n ≤ r` for
every `n`, and `pathBound` is bounded by `r`.

No induction, no minimal counterexample, no monotonicity of `pathBound` in the
scale --- which is fortunate, since `pathBound` is a `sInf` over a set that grows
with the scale and monotonicity is not obvious.  The self-application does all
the work, and the argument is first-order.

## Keeping the closing step linear

The comparison mixes `K` with `Nat.log 2 m`, and their product is not something
`omega` should be asked to reason about.  Naming it once --- `P = K · log₂ m` ---
and rewriting the two hypotheses that mention it leaves a closing step that is
linear in `pathBound n`, `pathBound m`, `P`, `K`, `m` and `r`, which `omega`
settles.  The products are then cleared, so the final call is provably linear
rather than relying on how `omega` atomises.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric

universe u

variable {G : Type u} [Group G]

/-- **The bound function is bounded.**

The radius the growth comparison returns bounds `pathBound` at every scale. -/
theorem exists_uniform_pathBound {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {K : ℕ} (D : GuessingData S K) :
    ∃ s : ℕ, ∀ n : ℕ, pathBound D n ≤ s := by
  obtain ⟨r, hr⟩ := exists_radius_log_lt (2 * K) (12 * K + 2)
  refine ⟨r, ?_⟩
  intro n
  by_contra hcon
  push Not at hcon
  -- the scale the bootstrap sends `n` to
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 2 * pathBound D n + 4 * K + 2 := ⟨_, rfl⟩
  have hrm : r < m := by omega
  -- the growth comparison, read at that scale
  have hgrow := hr m hrm
  -- the dyadic bound, read at that scale
  have hmpow : m ≤ 2 ^ (Nat.log 2 m + 1) :=
    le_of_lt (Nat.lt_pow_succ_log_self (b := 2) (by omega) m)
  have hdy := pathBound_le_of_pow hS D hmpow
  -- the recursion at `n`
  have hrec := pathBound_le_bootstrap hS D n
  rw [← hm] at hrec
  -- name the one product, so that the closing step is linear
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = K * Nat.log 2 m := ⟨_, rfl⟩
  have e1 : (Nat.log 2 m + 1 + 1) * K = P + 2 * K := by
    rw [hP]
    ring
  have e2 : 2 * K * (Nat.log 2 m + 1) + (12 * K + 2) = 2 * P + 14 * K + 2 := by
    rw [hP]
    ring
  rw [e1] at hdy
  rw [e2] at hgrow
  clear e1 e2 hP
  omega

/-- **The criterion's hypothesis holds at one constant, at every scale.**

This is the shape the slimness argument consumes: a single `s` with every path
vertex within `s` of every geodesic, whatever the distance between the
endpoints. -/
theorem exists_uniform_bnd {S : Set G} (hS : IsSymmetricGeneratingSet S)
    {K : ℕ} (D : GuessingData S K) :
    ∃ s : ℕ, ∀ n : ℕ, Bnd D n s := by
  obtain ⟨s, hs⟩ := exists_uniform_pathBound hS D
  exact ⟨s, fun n => (bnd_pathBound hS D n).mono (hs n)⟩

end OsinEnlargement
end GGT
end GroupApproximation

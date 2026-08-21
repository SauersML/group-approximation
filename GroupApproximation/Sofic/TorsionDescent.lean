import GroupApproximation.Sofic.GreendlingerCombinatorics
import GroupApproximation.Sofic.PeriodicOverlap

/-!
# The torsion descent: arithmetic core

The free-group small-cancellation torsion theorem descends on the length of a
cyclically reduced conjugate representative.  This file carries the part of that
descent that is pure arithmetic — the case analysis' length bookkeeping — and in
particular settles which metric constant the descent needs.

## The four branches

Write `n = |W|` for the cyclically reduced word, `u` for the Greendlinger arc of
the relator `r` inside `W ^ k`, and `m = |u| - n` for the overhang.  The arc has
period `n`, so when `|u| > n` the overhang is a common prefix of `r` and
`r.rotate n`, and the branches are

* `|u| ≤ n` — the arc is a cyclic subword of `W`, and a Dehn replacement
  shortens `W`;
* `|u| > n`, `r.rotate n = r` — `r` is a proper power, excluded by hypothesis;
* `|u| > n`, `r.rotate n ≠ r`, `|r| < 2n` — the relator contains a full cyclic
  conjugate of `W`, and replacing it shortens `W`;
* `|u| > n`, `r.rotate n ≠ r`, `2n ≤ |r|` — **the residual**.

## Why the constant moved to `1/8`

At `C'(1/6)`, consumed through the half-form `|r| < 2|u|`, the residual branch
does **not** close.  The overhang is what the piece bound controls, so the
branch yields `6m < |r|` and `|r| < 2(n + m)`, hence only `|u| < 3n/2` and
`|r| < 3n` — two upper bounds and no contradiction.
`half_form_residual_satisfiable` exhibits a solution of the whole constraint
set, so this is a fact about the constants rather than a gap in the search for
an argument.

At `C'(lam)` with `lam ≤ 1/8`, consumed through the **sharp** form
`(1 - 3·lam)·|r| < |u|` that the classical count actually produces, the residual
is empty: the piece bound gives `m < lam·|r|`, so

    (1 - 4·lam)·|r| < |u| - m = n,

and `lam ≤ 1/8` makes `1 - 4·lam ≥ 1/2`, so `|r| < 2n`, contradicting the
branch's own `2n ≤ |r|`.  That is `residual_empty_of_lam_le_eighth`, and it is
why the avatar family is designed at `C'(1/8)`: the stronger constant costs a
longer relator and removes a van-Kampen-class obligation from the program.

Note that the sharp form is genuinely stronger input, not a restatement:
`greendlingerConclusion_of_sharp` derives the half-form from it, and nothing
derives it back.
-/

namespace GroupApproximation
namespace TorsionDescent

open SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The sharp Greendlinger conclusion

`SmallCancellationRouter.GreendlingerConclusionSharp` is the statement, owned
upstream beside the half-form it generalizes, so that the lane that proves it
and the lane that spends it name the same constant rather than two matching
copies. -/

/-- The sharp form implies the half-form, for any constant at most `1/6`. -/
theorem greendlingerConclusion_of_sharp {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1 / 6) (h : GreendlingerConclusionSharp R lam) :
    GreendlingerConclusion R := by
  intro w hred hne hmem
  obtain ⟨r, hr, u, hinf, hpre, hlen⟩ := h w hred hne hmem
  refine ⟨r, hr, u, hinf, hpre, ?_⟩
  have hr0 : (0 : ℚ) ≤ (r.length : ℚ) := Nat.cast_nonneg _
  have hhalf : (1 : ℚ) / 2 * (r.length : ℚ) ≤ (1 - 3 * lam) * (r.length : ℚ) := by
    apply mul_le_mul_of_nonneg_right _ hr0
    linarith
  have : (r.length : ℚ) < 2 * (u.length : ℚ) := by linarith
  exact_mod_cast this

/-! ## 2.  The residual branch, and the constant that empties it -/

/-- **The residual branch is empty at `lam ≤ 1/8`.**

The four quantities are the lengths in play: `N = |W|`, `M = |u| - n` the
overhang, `Rl = |r|`, with the arc `|u| = N + M`.  The three hypotheses are
exactly what the branch supplies — the piece bound on the overhang, the sharp
Greendlinger bound on the arc, and the branch's own band `2N ≤ Rl` — and
together they are contradictory.

Stated over `ℚ` with the lengths abstracted, so that the arithmetic is separated
from the word combinatorics and can be read on its own. -/
theorem residual_empty_of_lam_le_eighth {lam N M Rl : ℚ}
    (hRl : 0 ≤ Rl) (hlam : lam ≤ 1 / 8)
    (hpiece : M < lam * Rl)
    (hsharp : (1 - 3 * lam) * Rl < N + M)
    (hband : 2 * N ≤ Rl) : False := by
  have hkey : Rl * (1 - 8 * lam) < 0 := by nlinarith
  have hnn : 0 ≤ Rl * (1 - 8 * lam) := mul_nonneg hRl (by linarith)
  linarith

/-- **At `1/6` through the half-form, the residual branch is consistent.**

Every constraint the branch supplies, with the arc `|u| = n + m`: the arc is a
prefix of the relator, the relator is less than twice the arc (the half-form),
the overhang is a piece and so less than a sixth of the relator, and the branch
band `2n ≤ |r|` holds.  A solution exists, so no rearrangement of these
hypotheses closes the branch — the constant has to move.

This is the machine-checked half of the claim that `C'(1/6)` is insufficient
here; `residual_empty_of_lam_le_eighth` is the other half. -/
theorem half_form_residual_satisfiable :
    ∃ n m Rl : ℕ, 0 < n ∧ 0 < m ∧ n + m ≤ Rl ∧ Rl < 2 * (n + m) ∧
      ((m : ℚ) < 1 / 6 * (Rl : ℚ)) ∧ 2 * n ≤ Rl :=
  ⟨10, 3, 25, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

/-- The same configuration, refuted the moment the constant is `1/8` and the
sharp form is used: the witness of `half_form_residual_satisfiable` does not
survive `residual_empty_of_lam_le_eighth`.  Recorded so the two theorems are
visibly about the same configuration rather than about different ones.  It is
the *sharp* conjunct that fails — the arc would have to be longer than `15.625`
where the witness offers `13`. -/
theorem half_form_witness_dies_at_eighth :
    ¬ ((3 : ℚ) < 1 / 8 * 25 ∧ (1 - 3 * (1 / 8 : ℚ)) * 25 < 10 + 3) := by
  norm_num

/-! ## 3.  From the quotient to cyclically reduced words -/

/-- **Every free-group element is conjugate to one spelled by a cyclically
reduced word.**  Mathlib's `reduceCyclically` and its partner `conjugator`
supply the decomposition as a list identity, which `FreeGroup.mk` turns into the
conjugation.  Decidability is obtained classically: it is used only to run the
reduction, and the conclusion is a proposition. -/
theorem exists_cyclicallyReduced_conj (g : FreeGroup α) :
    ∃ (W : List (α × Bool)) (c : FreeGroup α),
      FreeGroup.IsCyclicallyReduced W ∧ g = c * FreeGroup.mk W * c⁻¹ := by
  classical
  refine ⟨FreeGroup.reduceCyclically g.toWord,
    FreeGroup.mk (FreeGroup.reduceCyclically.conjugator g.toWord),
    FreeGroup.reduceCyclically.isCyclicallyReduced FreeGroup.isReduced_toWord, ?_⟩
  have h := FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically g.toWord
  conv_lhs => rw [← FreeGroup.mk_toWord (x := g), ← h]
  rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, FreeGroup.inv_mk]

/-- **The word-level torsion statement.**  Torsion-freeness of the quotient is
equivalent to this, and the equivalence is `isPowerTorsionFree_of_wordTorsion`
in one direction — the only direction any consumer needs. -/
def WordTorsion (R : Set (List (α × Bool))) : Prop :=
  ∀ W : List (α × Bool), FreeGroup.IsCyclicallyReduced W → ∀ k : ℕ, 0 < k →
    (FreeGroup.mk W) ^ k ∈ Subgroup.normalClosure (FreeGroup.mk '' R) →
      FreeGroup.mk W ∈ Subgroup.normalClosure (FreeGroup.mk '' R)

/-- **The quotient is torsion-free as soon as the word-level statement holds.**
Cyclic reduction moves an arbitrary element to a cyclically reduced word up to
conjugacy, and both membership in the relator subgroup and the order of an
element are conjugacy-invariant. -/
theorem isPowerTorsionFree_of_wordTorsion {R : Set (List (α × Bool))}
    (h : WordTorsion R) :
    IsPowerTorsionFree
      (FreeGroup α ⧸ Subgroup.normalClosure (FreeGroup.mk '' R)) := by
  intro q k hk hqk
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (N := Subgroup.normalClosure (FreeGroup.mk '' R)) q
  obtain ⟨W, c, hWcyc, hgc⟩ := exists_cyclicallyReduced_conj g
  have hgk : g ^ k ∈ Subgroup.normalClosure (FreeGroup.mk '' R) := by
    have h2 : QuotientGroup.mk'
        (Subgroup.normalClosure (FreeGroup.mk '' R)) (g ^ k) = 1 := by
      rw [map_pow]; exact hqk
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h2
    exact h2
  have hWk : (FreeGroup.mk W) ^ k ∈ Subgroup.normalClosure (FreeGroup.mk '' R) := by
    have hconj : c⁻¹ * (g ^ k) * c⁻¹⁻¹ ∈
        Subgroup.normalClosure (FreeGroup.mk '' R) :=
      Subgroup.normalClosure_normal.conj_mem _ hgk c⁻¹
    have hrw : c⁻¹ * (g ^ k) * c⁻¹⁻¹ = (FreeGroup.mk W) ^ k := by
      rw [hgc, ← conj_pow]; group
    rwa [hrw] at hconj
  have hmem := h W hWcyc k hk hWk
  have : g ∈ Subgroup.normalClosure (FreeGroup.mk '' R) := by
    rw [hgc]
    exact Subgroup.normalClosure_normal.conj_mem _ hmem c
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  exact this

/-! ## 4.  The descent principle -/

/-- **One shortening step discharges the whole word-level statement.**  If every
cyclically reduced nonempty word that is a counterexample yields a strictly
shorter cyclically reduced counterexample, there are none: the length is a
natural number, and the empty word is not a counterexample because it spells the
identity.

This is the only place the recursion lives, so the arc analysis has to produce
just one step. -/
theorem wordTorsion_of_step {R : Set (List (α × Bool))}
    (step : ∀ W : List (α × Bool), FreeGroup.IsCyclicallyReduced W → W ≠ [] →
      ∀ k : ℕ, 0 < k →
        (FreeGroup.mk W) ^ k ∈ Subgroup.normalClosure (FreeGroup.mk '' R) →
        FreeGroup.mk W ∉ Subgroup.normalClosure (FreeGroup.mk '' R) →
        ∃ W' : List (α × Bool), FreeGroup.IsCyclicallyReduced W' ∧
          W'.length < W.length ∧
          (FreeGroup.mk W') ^ k ∈ Subgroup.normalClosure (FreeGroup.mk '' R) ∧
          FreeGroup.mk W' ∉ Subgroup.normalClosure (FreeGroup.mk '' R)) :
    WordTorsion R := by
  suffices H : ∀ B : ℕ, ∀ W : List (α × Bool), W.length ≤ B →
      FreeGroup.IsCyclicallyReduced W → ∀ k : ℕ, 0 < k →
      (FreeGroup.mk W) ^ k ∈ Subgroup.normalClosure (FreeGroup.mk '' R) →
        FreeGroup.mk W ∈ Subgroup.normalClosure (FreeGroup.mk '' R) by
    exact fun W hcyc k hk hpow => H W.length W le_rfl hcyc k hk hpow
  intro B
  induction B with
  | zero =>
      intro W hlen _ _ _ _
      have : W = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      rw [← FreeGroup.one_eq_mk]
      exact Subgroup.one_mem _
  | succ B ih =>
      intro W hlen hcyc k hk hpow
      by_contra hnot
      rcases eq_or_ne W [] with rfl | hne
      · refine hnot ?_
        rw [← FreeGroup.one_eq_mk]
        exact Subgroup.one_mem _
      obtain ⟨W', hcyc', hlt, hpow', hnot'⟩ := step W hcyc hne k hk hpow hnot
      exact hnot' (ih W' (by omega) hcyc' k hk hpow')

/-! ## 5.  The period of a power, and the arc that inherits it -/

/-- **A positive power is periodic with the period of its base.**  Reading the
block off the front and off the back gives the two decompositions that make the
tail a prefix. -/
theorem hasPeriod_flatten_replicate {β : Type*} (W : List β) {k : ℕ} (hk : 0 < k) :
    List.HasPeriod ((List.replicate k W).flatten) W.length := by
  refine PeriodicOverlap.hasPeriod_iff_drop_prefix.mpr ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : (List.replicate (j + 1) W).flatten
      = W ++ (List.replicate j W).flatten := by
    rw [List.replicate_succ, List.flatten_cons]
  have h2 : (List.replicate (j + 1) W).flatten
      = (List.replicate j W).flatten ++ W := by
    rw [List.replicate_succ', List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil]
  rw [h1, List.drop_left, ← h1, h2]
  exact List.prefix_append _ _

/-! ## 5b.  An arc no longer than one period is a cyclic subword -/

/-- **A short factor of a periodic word is a factor of one period, read
cyclically.**  If `u` sits inside `z` at offset `a` and is no longer than the
period, then `u` prefixes the rotation of `z`'s first period by `a % n`: every
index computation on both sides collapses to `z` at the same residue.

This is what turns "the Greendlinger arc is short" into "the arc is a cyclic
subword of `W`", which is what the Dehn replacement needs. -/
theorem exists_prefix_rotate_of_infix {β : Type*} {z u : List β} {n : ℕ}
    (hn : 0 < n) (hper : List.HasPeriod z n) (hnz : n ≤ z.length)
    (hu : u <:+: z) (hlen : u.length ≤ n) :
    ∃ s, s < n ∧ u <+: (z.take n).rotate s := by
  obtain ⟨A, B, hAB⟩ := hu
  have htake : (z.take n).length = n := List.length_take_of_le hnz
  have hAu : A.length + u.length ≤ z.length := by
    have h := congrArg List.length hAB
    simp only [List.length_append] at h
    omega
  refine ⟨A.length % n, Nat.mod_lt _ hn, ?_⟩
  rw [List.prefix_iff_getElem?]
  intro i hi
  have hin : i < n := lt_of_lt_of_le hi hlen
  have hiz : A.length + i < z.length := by omega
  -- the left-hand side is `z` at index `A.length + i`
  have hleft : u[i]? = z[A.length + i]? := by
    rw [← hAB, List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by omega)]
    simp
  -- the right-hand side is `z` at the residue of that index
  have hmod : (i + A.length % n) % n = (A.length + i) % n := by
    rw [Nat.add_comm A.length i]
    conv_rhs => rw [Nat.add_mod]
    conv_lhs => rw [Nat.add_mod]
    simp
  have hright : ((z.take n).rotate (A.length % n))[i]? = z[(A.length + i) % n]? := by
    rw [List.getElem?_rotate (by omega), htake, hmod]
    exact List.getElem?_take_of_lt (Nat.mod_lt _ hn)
  rw [hright, ← List.hasPeriod_iff_forall_getElem?_mod.mp hper _ hiz, ← hleft]
  exact List.getElem?_eq_getElem hi

/-- The form the descent consumes: a Greendlinger arc no longer than the base
is a prefix of some rotation of the base. -/
theorem exists_prefix_rotate_of_infix_pow {β : Type*} {W u : List β} {k : ℕ}
    (hk : 0 < k) (hW : W ≠ []) (hu : u <:+: (List.replicate k W).flatten)
    (hlen : u.length ≤ W.length) :
    ∃ s, s < W.length ∧ u <+: W.rotate s := by
  have hn : 0 < W.length := List.length_pos_of_ne_nil hW
  have hflat : (List.replicate k W).flatten.length = k * W.length :=
    PeriodicOverlap.length_flatten_replicate k W
  have hnz : W.length ≤ (List.replicate k W).flatten.length := by
    rw [hflat]
    exact Nat.le_mul_of_pos_left _ hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have htake : (List.replicate (j + 1) W).flatten.take W.length = W := by
    rw [List.replicate_succ, List.flatten_cons, List.take_left]
  obtain ⟨s, hs, hpre⟩ :=
    exists_prefix_rotate_of_infix hn (hasPeriod_flatten_replicate W hk) hnz hu hlen
  exact ⟨s, hs, by rwa [htake] at hpre⟩

/-! ## 6.  The overhang dichotomy

This is the branch the periodicity lane was built for, and it is where
`NoProperPower` is spent. -/

/-- **An arc longer than one period is a proper power or has a piece for its
overhang.**  The arc `u` sits inside a word of period `n`, so it has period `n`
itself; its overhang `u.drop n` is then a common prefix of `r` and of
`r.rotate n`, both members of the symmetrization.  Either those two rotations
coincide — and then `r` is fixed by a nontrivial rotation, hence a proper
power — or they are distinct and the overhang is a piece.

No length hypothesis beyond `n < u.length` is needed, and none is available:
the piece bounds the *overhang*, never the arc. -/
theorem isProperPower_or_isPiece_drop {R : Set (List (α × Bool))}
    {r u : List (α × Bool)} {n : ℕ} (hn : 0 < n)
    (hr : r ∈ symmetrization R) (hpre : u <+: r) (hper : List.HasPeriod u n)
    (hlt : n < u.length) :
    PeriodicOverlap.IsProperPower r ∨ IsPiece (symmetrization R) (u.drop n) := by
  have hnr : n < r.length := lt_of_lt_of_le hlt hpre.length_le
  by_cases hfix : r.rotate n = r
  · exact Or.inl (PeriodicOverlap.isProperPower_of_rotate_eq_self hn hnr hfix)
  · refine Or.inr ⟨r, hr, r.rotate n, rotate_mem_symmetrization hr n, ?_, ?_, ?_⟩
    · exact fun h => hfix h.symm
    · exact (PeriodicOverlap.hasPeriod_iff_drop_prefix.mp hper).trans hpre
    · obtain ⟨t, ht⟩ := hpre
      have hdrop : r.drop n = u.drop n ++ t := by
        rw [← ht, List.drop_append_of_le_length (by omega)]
      refine ⟨t ++ r.take n, ?_⟩
      rw [List.rotate_eq_drop_append_take hnr.le, hdrop, List.append_assoc]

end TorsionDescent
end GroupApproximation

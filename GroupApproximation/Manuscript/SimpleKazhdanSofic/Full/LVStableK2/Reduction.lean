import Mathlib.Data.Fin.Embedding
import GroupApproximation.Steinberg.Functoriality
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVH2GL3.RankFive

/-!
# Formal reductions for stable `K₂ = 0` (lane LVStableK2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`): infinite finitely presented simple
Kazhdan groups exist.  The Lean route needs `hsp` (the units of `L = L_{𝔽₂}(1,2)` are superperfect),
and `LVH2GL3.binaryLeavittUnits_isSuperperfect_of_stable` reduces `hsp` to two stable inputs.  This
lane (work order W1) targets the first one, `LVH2GL3.StableK2Trivial L`.

The classical proof (Ara–Brustenga–Cortiñas, *K-theory of Leavitt path algebras*, Münster J. Math.
2 (2009)) runs through the Cohn algebra `C = C_2(𝔽₂)`, the surjection `π : C → L` and the ideal
`(p) = ker π ≅ M_∞(𝔽₂)`:

1. relative `K₁(C, (p)) = 0`;
2. the degree-two part of the `K`-equivalence `𝔽₂ → C`: stable `K₂(𝔽₂) → K₂(C)` is onto;
3. stable `K₂(𝔽₂) = 0`.

This file proves the two formal steps that glue these inputs, for arbitrary rings and at finite
stages:

* `indexMap_ringMap`: coefficient maps commute with index padding;
* `RelativeKOneLift f`: the finite-stage form of step 1 for a ring map `f : R → S`;
* `stableK2Trivial_of_surjective`: for a surjective `f`, `RelativeKOneLift f` and stable
  `K₂(R) = 0` give stable `K₂(S) = 0` (the foreign reduction
  `LeavittK2.binaryLeavittStableK2Trivial_of_cohn`, re-proved for any ring);
* `StableK2BaseSurjective f`: the finite-stage form of step 2;
* `stableK2Trivial_of_baseSurjective`: step 2 plus stable `K₂(R) = 0` give stable `K₂(S) = 0`;
* `baseSurjective_of_stableK2Trivial`: conversely stable `K₂(S) = 0` gives step 2 (so step 2 is not
  logically stronger than the target).

Only modules already reachable from `GroupApproximation.lean` are imported.
-/

namespace GroupApproximation.Full.LVStableK2

open SteinbergGroup

section Padding

variable {R S : Type*} [Ring R] [Ring S]

/-- Coefficient maps commute with index padding of Steinberg groups.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem indexMap_ringMap {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ↪ J) (f : R →+* S) (g : SteinbergGroup I R) :
    indexMap e (ringMap f g) = ringMap f (indexMap e g) := by
  have hh : (indexMap (R := S) e).comp (ringMap (I := I) f) =
      (ringMap (I := J) f).comp (indexMap (R := R) e) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change indexMap e (ringMap f (x i j hij a)) = ringMap f (indexMap e (x i j hij a))
    simp only [ringMap_x, indexMap_x]
  exact DFunLike.congr_fun hh g

end Padding

section Surjective

variable {R S : Type*} [Ring R] [Ring S]

/-- **Relative `K₁` lifting, finite-stage form.**  Every `g ∈ St_n(R)` whose image over `S` lies
in `K₂(n, S)` has, after padding to some rank `N`, the same projection to `E_N(R)` as some element
of `ker (St_N(R) → St_N(S))`.  For the Cohn surjection `C_2(𝔽₂) → L_{𝔽₂}(1,2)` this is relative
`K₁(C_2, (p)) = 0` (Ara–Brustenga–Cortiñas 2009, via excision `(p) ≅ M_∞(𝔽₂)` and `𝔽₂ˣ = 1`).
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
def RelativeKOneLift (f : R →+* S) : Prop :=
  ∀ (n : ℕ) (g : SteinbergGroup (Fin n) R), projection (ringMap f g) = 1 →
    ∃ (N : ℕ) (h : n ≤ N) (t : SteinbergGroup (Fin N) R),
      ringMap f t = 1 ∧ projection t = projection (indexMap (Fin.castLEEmb h) g)

/-- **Stable `K₂` descends along a surjection with relative `K₁` lifting.**  Lift
`k ∈ K₂(n, S)` to `g ∈ St_n(R)`; relative `K₁` gives `t ∈ ker (St_N(R) → St_N(S))` with the
projection of the padded `g`; then `g t⁻¹ ∈ K₂(N, R)` dies in some `St_M(R)`, and pushing the
relation to `S` kills the padded `k`.  (Finite-stage Milnor argument; re-proves the foreign
`LeavittK2.binaryLeavittStableK2Trivial_of_cohn` for arbitrary rings.
`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem stableK2Trivial_of_surjective (f : R →+* S) (hf : Function.Surjective f)
    (hK : RelativeKOneLift f) (hS : LVH2GL3.StableK2Trivial R) :
    LVH2GL3.StableK2Trivial S := by
  intro n k hk
  obtain ⟨g, rfl⟩ := ringMap_surjective_of_surjective (I := Fin n) f hf k
  obtain ⟨N, hnN, t, ht1, htg⟩ := hK n g hk
  have hy : projection (indexMap (Fin.castLEEmb hnN) g * t⁻¹) = 1 := by
    rw [map_mul, map_inv, ← htg, mul_inv_cancel]
  obtain ⟨M, hNM, hyM⟩ := hS N _ hy
  rw [map_mul, map_inv, mul_inv_eq_one] at hyM
  refine ⟨M, hnN.trans hNM, ?_⟩
  rw [← LVH2GL3.indexMap_castLEEmb_castLEEmb hnN hNM, indexMap_ringMap, indexMap_ringMap, hyM,
    ← indexMap_ringMap, ht1, map_one]

end Surjective

section BaseChange

variable {R S : Type*} [Ring R] [Ring S]

/-- **Stable surjectivity of `K₂(R) → K₂(S)`, finite-stage form.**  Every `k ∈ K₂(n, S)`
becomes, in some `St_N(S)` with `n ≤ N`, the coefficientwise image of some `y ∈ K₂(N, R)`.
For `𝔽₂ → C_2(𝔽₂)` this is the degree-two part of the Ara–Brustenga–Cortiñas `K`-equivalence.
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
def StableK2BaseSurjective (f : R →+* S) : Prop :=
  ∀ (n : ℕ) (k : SteinbergGroup (Fin n) S), projection k = 1 →
    ∃ (N : ℕ) (h : n ≤ N) (y : SteinbergGroup (Fin N) R),
      projection y = 1 ∧ ringMap f y = indexMap (Fin.castLEEmb h) k

/-- Stable surjectivity on `K₂` plus stable `K₂(R) = 0` give stable `K₂(S) = 0`.
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem stableK2Trivial_of_baseSurjective (f : R →+* S) (hB : StableK2BaseSurjective f)
    (hR : LVH2GL3.StableK2Trivial R) : LVH2GL3.StableK2Trivial S := by
  intro n k hk
  obtain ⟨N, hN, y, hy1, hy⟩ := hB n k hk
  obtain ⟨M, hM, hyM⟩ := hR N y hy1
  refine ⟨M, hN.trans hM, ?_⟩
  rw [← LVH2GL3.indexMap_castLEEmb_castLEEmb hN hM, ← hy, indexMap_ringMap, hyM, map_one]

/-- Conversely, stable `K₂(S) = 0` gives stable surjectivity (take `y = 1`).
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem baseSurjective_of_stableK2Trivial (f : R →+* S) (hS : LVH2GL3.StableK2Trivial S) :
    StableK2BaseSurjective f := by
  intro n k hk
  obtain ⟨N, hN, hNk⟩ := hS n k hk
  exact ⟨N, hN, 1, map_one _, by rw [map_one, hNk]⟩

end BaseChange

end GroupApproximation.Full.LVStableK2

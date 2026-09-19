import Mathlib

/-!
# Adamczewski–Bell, Lemma `lem: rational`, over `ℤ`: a local–global principle for recurrences

Adamczewski–Bell (arXiv:1303.2019, Lemma `lem: rational`, read at source). If an integer
sequence satisfies, modulo arbitrarily large primes `p`, a nontrivial linear recurrence whose
order is bounded independently of `p`, then it satisfies a nontrivial linear recurrence over `ℚ`.

The source argues with the vanishing of all maximal minors of a Hankel matrix. Here the argument
avoids minors:
- the windows `K_T = {c | ∑ⱼ cⱼ f(m + j) = 0 for m < T}` decrease, so some `K_{T₀}` has minimal
  dimension, and then `K_{T₀}` is contained in every `K_T`;
- if `K_{T₀} = 0`, the window map has a rational left inverse `G`;
- clearing its denominators gives integers `Z` and `N > 0` with
  `N · cⱼ = ∑ₘ Zⱼₘ ∑ᵢ cᵢ f(m + i)` for every integer vector `c`;
- modulo a prime `p > N`, this identity kills every mod-`p` recurrence, a contradiction.

**Role in Kourovka 17.57.** Here `f = Φ` is the normalizer sequence, and the mod-`p` recurrences
of order `≤ d` come from Lemma `lem: AB` (`Out/MahlerAB.lean`).
-/

set_option linter.unusedSimpArgs false

namespace GroupApproximation.ClassTransposition.Out

open Finset

/-- The recurrence map of window `T`: `c ↦ (∑ⱼ cⱼ f(m + j))_{m < T}`. -/
def recMap (f : ℕ → ℤ) (D T : ℕ) : (Fin D → ℚ) →ₗ[ℚ] (Fin T → ℚ) where
  toFun c m := ∑ j : Fin D, c j * (f ((m : ℕ) + (j : ℕ)) : ℚ)
  map_add' c c' := by
    funext m
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext m
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

/-- **Adamczewski–Bell, Lemma `lem: rational`, over `ℤ`.** If for arbitrarily large primes `p`
the sequence `f` satisfies a nonzero mod-`p` recurrence `∑_{j<D} cⱼ f(m + j) ≡ 0`, then it
satisfies a nonzero rational one. -/
theorem exists_rat_recurrence_of_mod_primes {f : ℕ → ℤ} {D : ℕ}
    (h : ∀ N : ℕ, ∃ p : ℕ, p.Prime ∧ N < p ∧ ∃ c : Fin D → ZMod p, c ≠ 0 ∧
      ∀ m : ℕ, ∑ j : Fin D, c j * ((f (m + j) : ℤ) : ZMod p) = 0) :
    ∃ c : Fin D → ℚ, c ≠ 0 ∧ ∀ m : ℕ, ∑ j : Fin D, c j * (f (m + j) : ℚ) = 0 := by
  classical
  let K : ℕ → Submodule ℚ (Fin D → ℚ) := fun T => LinearMap.ker (recMap f D T)
  have hanti : ∀ T T', T ≤ T' → K T' ≤ K T := by
    intro T T' hTT' c hc
    simp only [K, LinearMap.mem_ker] at hc ⊢
    funext m
    exact congrFun hc ⟨m, lt_of_lt_of_le m.2 hTT'⟩
  obtain ⟨T0, hT0⟩ : ∃ T0, ∀ T, Module.finrank ℚ (K T0) ≤ Module.finrank ℚ (K T) := by
    have hex : ∃ r, ∃ T, Module.finrank ℚ (K T) = r := ⟨_, 0, rfl⟩
    obtain ⟨T0, hT0⟩ := Nat.find_spec hex
    refine ⟨T0, fun T => ?_⟩
    rw [hT0]
    exact Nat.find_min' hex ⟨T, rfl⟩
  by_cases hK : K T0 = ⊥
  · exfalso
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (recMap f D T0) hK
    obtain ⟨Gq, hGq⟩ : ∃ Gq : Fin D → Fin T0 → ℚ,
        ∀ j m, Gq j m = g (fun m' => if m = m' then (1 : ℚ) else 0) j :=
      ⟨_, fun _ _ => rfl⟩
    have hinv : ∀ c, g (recMap f D T0 c) = c := by
      intro c
      have := LinearMap.congr_fun hg c
      rwa [LinearMap.comp_apply, LinearMap.id_apply] at this
    have key : ∀ (c : Fin D → ℚ) (j : Fin D),
        c j = ∑ m : Fin T0, recMap f D T0 c m * Gq j m := by
      intro c j
      calc c j = g (recMap f D T0 c) j := by rw [hinv]
        _ = g (∑ m : Fin T0, recMap f D T0 c m •
              (fun m' => if m = m' then (1 : ℚ) else 0)) j := by
            rw [← pi_eq_sum_univ]
        _ = ∑ m : Fin T0, recMap f D T0 c m * Gq j m := by
            rw [map_sum]
            simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hGq]
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ∏ j : Fin D, ∏ m : Fin T0, (Gq j m).den := ⟨_, rfl⟩
    have hNpos : 0 < N := by
      rw [hN]
      exact Finset.prod_pos fun j _ => Finset.prod_pos fun m _ => (Gq j m).pos
    have hden : ∀ j m, ∃ z : ℤ, (z : ℚ) = (N : ℚ) * Gq j m := by
      intro j m
      have hd : (Gq j m).den ∣ N := by
        rw [hN]
        exact dvd_trans
          (Finset.dvd_prod_of_mem (fun m => (Gq j m).den) (Finset.mem_univ m))
          (Finset.dvd_prod_of_mem (fun j => ∏ m : Fin T0, (Gq j m).den) (Finset.mem_univ j))
      obtain ⟨k, hk⟩ := hd
      refine ⟨(k : ℤ) * (Gq j m).num, ?_⟩
      rw [hk]
      push_cast
      rw [mul_comm ((Gq j m).den : ℚ) (k : ℚ), mul_assoc, Rat.den_mul_eq_num]
    choose Z hZ using hden
    have hint : ∀ (c : Fin D → ℤ) (j : Fin D),
        (N : ℤ) * c j = ∑ m : Fin T0, Z j m * ∑ i : Fin D, c i * f ((m : ℕ) + (i : ℕ)) := by
      intro c j
      have hk : (c j : ℚ) = ∑ m : Fin T0, recMap f D T0 (fun i => (c i : ℚ)) m * Gq j m :=
        key (fun i => (c i : ℚ)) j
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [hk, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hZ j m]
      show (N : ℚ) * ((∑ i : Fin D, (c i : ℚ) * (f ((m : ℕ) + (i : ℕ)) : ℚ)) * Gq j m) =
        (N : ℚ) * Gq j m * ∑ i : Fin D, (c i : ℚ) * (f ((m : ℕ) + (i : ℕ)) : ℚ)
      ring
    obtain ⟨p, hp, hNp, c', hc'0, hc'⟩ := h N
    haveI := Fact.mk hp
    haveI : NeZero p := ⟨hp.ne_zero⟩
    apply hc'0
    funext j
    have hmod := congrArg (Int.cast : ℤ → ZMod p) (hint (fun i => ((c' i).val : ℤ)) j)
    push_cast at hmod
    simp only [ZMod.natCast_zmod_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id', id_eq] at hmod
    have hzero : ∀ m : Fin T0,
        ∑ i : Fin D, c' i * ((f ((m : ℕ) + (i : ℕ)) : ℤ) : ZMod p) = 0 := fun m => hc' m
    simp only [hzero, mul_zero, Finset.sum_const_zero] at hmod
    have hN0 : (N : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact absurd (Nat.le_of_dvd hNpos hdvd) (by omega)
    exact (mul_eq_zero.mp hmod).resolve_left hN0
  · obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
    refine ⟨c, hc0, fun m => ?_⟩
    have hKT : K (max T0 (m + 1)) = K T0 :=
      Submodule.eq_of_le_of_finrank_le (hanti T0 _ (le_max_left _ _)) (hT0 _)
    have hcT : c ∈ K (max T0 (m + 1)) := by
      rw [hKT]
      exact hc
    have := congrFun (LinearMap.mem_ker.mp hcT) ⟨m, lt_of_lt_of_le (Nat.lt_succ_self m)
      (le_max_right _ _)⟩
    exact this

end GroupApproximation.ClassTransposition.Out

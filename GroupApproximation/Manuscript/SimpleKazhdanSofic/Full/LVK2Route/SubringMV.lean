import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Coefficients

/-!
# Mayer–Vietoris factorization for a square of subrings (lane LVK2Route)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`, "The finitely presented case"),
leaf T1b.iii: the Lean route needs stable `K₂(L_{𝔽₂}(1,2)) = 0` (input W1).  Every known proof of
that input goes through a Mayer–Vietoris or localization step for `K₂`, e.g.
Ara–Brustenga–Cortiñas 2009 `thm:skewyao` (`yaoseq6.tex` l.574-640), which is Yao 1995 Thm 2.1
for `S[t] ← S → S[t⁻¹] → S[t,t⁻¹]`, or the graded square `L₀ ⊂ L₊, L₋ ⊂ L` of the Leavitt
algebra itself.  This file states the Steinberg-level form of the `K₂` part of such a square for
arbitrary subrings `C ≤ A`, `C ≤ B` of a ring `R`, and proves that it is exactly what is needed:

* `SubringFactorization A B C hCA`: after padding, each `k ∈ K₂(n, R)` is a product
  `a · b` with `a ∈ St_N(A)`, `b ∈ St_N(B)`, and the image of `a` in `E_N(A)` comes from
  `St_N(C)`;
* `stableK2Trivial_of_subringFactorization`: with stable `K₂(A) = K₂(B) = 0` this gives stable
  `K₂(R) = 0`;
* `subringFactorization_of_stableK2Trivial`: conversely stable `K₂(R) = 0` gives the factorization,
  so the factorization is precisely the Mayer–Vietoris core.

This generalizes `LVSkewLaurentK2.stableK2Trivial_of_yaoFactorization` (`YaoReduction.lean`):
there `A, B` are the two half rings, `C` is the constants, and the `K₁(S)` hypothesis is used only
to lift the constant matrix to `St_N(C)`; here that lift is part of the factorization.
-/

namespace GroupApproximation.Full.LVK2Route

open SteinbergGroup

section SubringSquare

variable {R : Type*} [Ring R]

/-- **Mayer–Vietoris factorization** for subrings `C ≤ A` and `C ≤ B` of `R`, at the Steinberg
level: every `k ∈ K₂(n, R)`, padded to some `St_N(R)`, factors as `a · b` with `a ∈ St_N(A)`,
`b ∈ St_N(B)`, and `a` has the same image in `E_N(A)` as some `c ∈ St_N(C)`.
(Yao 1995 Thm 2.1; Ara–Brustenga–Cortiñas 2009 `thm:skewyao`, `yaoseq6.tex` l.574-640;
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def SubringFactorization (A B C : Subring R) (hCA : C ≤ A) : Prop :=
  ∀ (n : ℕ) (k : SteinbergGroup (Fin n) R), projection k = 1 →
    ∃ (N : ℕ) (h : n ≤ N) (a : SteinbergGroup (Fin N) A) (b : SteinbergGroup (Fin N) B)
      (c : SteinbergGroup (Fin N) C),
      indexMap (Fin.castLEEmb h) k = ringMap A.subtype a * ringMap B.subtype b ∧
        projection a = projection (ringMap (Subring.inclusion hCA) c)

/-- The inclusion `C ≤ A` followed by `A ⊆ R` is the inclusion `C ⊆ R`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem subtype_comp_inclusion {A C : Subring R} (hCA : C ≤ A) :
    A.subtype.comp (Subring.inclusion hCA) = C.subtype :=
  RingHom.ext fun _ => rfl

/-- Steinberg elements of a smaller subring pass through a larger one.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem ringMap_subtype_inclusion {A C : Subring R} (hCA : C ≤ A) {N : ℕ}
    (c : SteinbergGroup (Fin N) C) :
    ringMap A.subtype (ringMap (Subring.inclusion hCA) c) = ringMap C.subtype c := by
  rw [LVCohnK2.ringMap_ringMap, subtype_comp_inclusion]

/-- **Mayer–Vietoris step for `K₂`.**  If the square `C ≤ A, B ≤ R` has the Steinberg-level
factorization and both `A` and `B` have stable `K₂ = 0`, then `R` has stable `K₂ = 0`.
Proof: pad `k` to `a · b`; move the common element `c` from `a` to `b`: `a' = a · c⁻¹` lies in
`K₂(N, A)`, hence so does `b' = c · b`, and both die after padding.
(Yao 1995 Thm 2.1; `yaoseq6.tex` l.574-640; `simple_kazhdan_sofic_group.tex` l.733-735,
leaf T1b.iii.) -/
theorem stableK2Trivial_of_subringFactorization {A B C : Subring R} (hCA : C ≤ A)
    (hCB : C ≤ B) (hFac : SubringFactorization A B C hCA) (hA : LVH2GL3.StableK2Trivial A)
    (hB : LVH2GL3.StableK2Trivial B) : LVH2GL3.StableK2Trivial R := by
  intro n k hk
  obtain ⟨N, h, a, b, c, hkab, hac⟩ := hFac n k hk
  obtain ⟨a', ha'⟩ : ∃ a' : SteinbergGroup (Fin N) A,
      a' = a * (ringMap (Subring.inclusion hCA) c)⁻¹ := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : SteinbergGroup (Fin N) B,
      b' = ringMap (Subring.inclusion hCB) c * b := ⟨_, rfl⟩
  have hsplit : indexMap (Fin.castLEEmb h) k =
      ringMap A.subtype a' * ringMap B.subtype b' := by
    rw [hkab, ha', hb', map_mul, map_mul, map_inv, ringMap_subtype_inclusion,
      ringMap_subtype_inclusion, mul_assoc, inv_mul_cancel_left]
  have ha'1 : projection a' = 1 := by
    rw [ha', map_mul, map_inv, ← hac, mul_inv_eq_one]
  have hb'1 : projection b' = 1 := by
    apply LVCohnK2.projection_eq_one_of_ringMap B.subtype B.subtype_injective
    have hkN : projection (indexMap (Fin.castLEEmb h) k) = 1 :=
      LVH2GL3.projection_indexMap_eq_one (Fin.castLEEmb h) hk
    rw [hsplit, map_mul, LVCohnK2.projection_ringMap A.subtype a', ha'1, map_one,
      one_mul] at hkN
    exact hkN
  obtain ⟨N₁, h₁, hN₁⟩ := hA N a' ha'1
  obtain ⟨N₂, h₂, hN₂⟩ := hB N b' hb'1
  have hnM : n ≤ N₁ + N₂ := by omega
  have hNM : N ≤ N₁ + N₂ := by omega
  have h1M : N₁ ≤ N₁ + N₂ := by omega
  have h2M : N₂ ≤ N₁ + N₂ := by omega
  refine ⟨N₁ + N₂, hnM, ?_⟩
  have ha'M : indexMap (Fin.castLEEmb hNM) a' = 1 := by
    rw [← LVH2GL3.indexMap_castLEEmb_castLEEmb h₁ h1M a', hN₁, map_one]
  have hb'M : indexMap (Fin.castLEEmb hNM) b' = 1 := by
    rw [← LVH2GL3.indexMap_castLEEmb_castLEEmb h₂ h2M b', hN₂, map_one]
  rw [← LVH2GL3.indexMap_castLEEmb_castLEEmb h hNM k, hsplit, map_mul,
    LVStableK2.indexMap_ringMap, LVStableK2.indexMap_ringMap, ha'M, hb'M, map_one, map_one,
    one_mul]

/-- Conversely, stable `K₂(R) = 0` gives the factorization with `a = b = c = 1`: the
Mayer–Vietoris factorization is exactly as strong as the endpoint.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem subringFactorization_of_stableK2Trivial (A B C : Subring R) (hCA : C ≤ A)
    (hR : LVH2GL3.StableK2Trivial R) : SubringFactorization A B C hCA := by
  intro n k hk
  obtain ⟨N, h, hN⟩ := hR n k hk
  refine ⟨N, h, 1, 1, 1, ?_, ?_⟩
  · rw [hN, map_one, map_one, one_mul]
  · simp only [map_one]

end SubringSquare

end GroupApproximation.Full.LVK2Route

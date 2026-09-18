import GroupApproximation.Analysis.CStarCompactOperators

/-!
# Strong limits of adjointable operators

Lane `TWWSch3c2-C3c`, work order `WO-TWWSch-3c2-C3c`, first part. Sources: G. A. Elliott and
D. Kucerovsky, Pacific J. Math. 198 (2001), proof of Thm. 6 and Lemma 7; G. G. Kasparov,
J. Operator Theory 4 (1980), §7; J. Gabe, J. Funct. Anal. 271 (2016), Thm. 2.1. Manuscript label:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (the absorption step).

The Elliott–Kucerovsky diagonal argument builds its near isometry `w = Σ vₙ` as a *strong* limit
of partial sums, and shows that the errors `w⋆ ℓ(s) w − σ(s)` are compact because they are strong
limits of norm-Cauchy sequences of compact operators. This file isolates the soft analysis:

* `IsStrongLimit T L`: `Tₙ x → L x` for every vector `x`, in the module norm, in `ε`–`N` form;
* `IsStrongLimit.isBoundedBy`: a bound that eventually holds for `Tₙ` holds for `L`;
* `IsStrongLimit.isBoundedBy_sub`: a norm-Cauchy estimate passes to `L − Tₙ`;
* `IsStrongLimit.isCompactOp`: **a strong limit of a norm-Cauchy sequence of compact operators is
  compact** (no completeness of the module is needed: the limit is given);
* `IsStrongLimit.comp`, `IsStrongLimit.add`: strong limits of products (under a uniform bound on
  the left factors) and of sums;
* `IsStrongLimit.toFun_eq`: strong limits are unique.
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

universe v w w' w''

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {E : CStarModule.{v, w} B} {F : CStarModule.{v, w'} B} {G : CStarModule.{v, w''} B}

/-- `L` is the **strong limit** of the operators `T n`: `T n x → L x` in the module norm for every
vector `x` (Elliott–Kucerovsky 2001, proof of Thm. 6). -/
def IsStrongLimit (T : ℕ → Adjointable E F) (L : Adjointable E F) : Prop :=
  ∀ x : E.carrier, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    F.norm (L.toFun x - (T n).toFun x) ≤ ε

/-- A constant sequence converges strongly to its value. -/
theorem isStrongLimit_const (L : Adjointable E F) : IsStrongLimit (fun _ => L) L := by
  intro x ε hε
  refine ⟨0, fun n _ => ?_⟩
  show F.norm (L.toFun x - L.toFun x) ≤ ε
  rw [sub_self, F.norm_zero_vector]
  exact hε.le

/-- **A bound that eventually holds along the sequence holds for the strong limit.** -/
theorem IsStrongLimit.isBoundedBy {T : ℕ → Adjointable E F} {L : Adjointable E F}
    (hL : IsStrongLimit T L) {C : ℝ} {N : ℕ} (hb : ∀ n : ℕ, N ≤ n → (T n).IsBoundedBy C) :
    L.IsBoundedBy C := by
  intro x
  by_contra hne
  have hlt : C * E.norm x < F.norm (L.toFun x) := not_le.mp hne
  obtain ⟨N', hN'⟩ := hL x ((F.norm (L.toFun x) - C * E.norm x) / 2) (by linarith)
  have h1 := hN' (max N N') (le_max_right N N')
  have h2 := hb (max N N') (le_max_left N N') x
  have h3 : F.norm (L.toFun x) ≤ F.norm (L.toFun x - (T (max N N')).toFun x)
      + F.norm ((T (max N N')).toFun x) := by
    have hrw : L.toFun x = (L.toFun x - (T (max N N')).toFun x)
        + (T (max N N')).toFun x := by abel
    calc F.norm (L.toFun x)
        = F.norm ((L.toFun x - (T (max N N')).toFun x) + (T (max N N')).toFun x) := by
          rw [← hrw]
      _ ≤ F.norm (L.toFun x - (T (max N N')).toFun x) + F.norm ((T (max N N')).toFun x) :=
          F.norm_add_le _ _
  linarith

/-- Subtracting a fixed operator commutes with strong limits. -/
theorem IsStrongLimit.sub_const {T : ℕ → Adjointable E F} {L : Adjointable E F}
    (hL : IsStrongLimit T L) (U : Adjointable E F) :
    IsStrongLimit (fun n => (T n).sub U) (L.sub U) := by
  intro x ε hε
  obtain ⟨N, hN⟩ := hL x ε hε
  refine ⟨N, fun n hn => ?_⟩
  show F.norm (L.toFun x - U.toFun x - ((T n).toFun x - U.toFun x)) ≤ ε
  have hrw : L.toFun x - U.toFun x - ((T n).toFun x - U.toFun x)
      = L.toFun x - (T n).toFun x := by abel
  rw [hrw]
  exact hN n hn

/-- **A norm-Cauchy estimate passes to the strong limit**: if `T m − T n` is bounded by `ε` for
`m, n ≥ N`, then so is `L − T n`. -/
theorem IsStrongLimit.isBoundedBy_sub {T : ℕ → Adjointable E F} {L : Adjointable E F}
    (hL : IsStrongLimit T L) {ε : ℝ} {N : ℕ}
    (hc : ∀ m n : ℕ, N ≤ m → N ≤ n → ((T m).sub (T n)).IsBoundedBy ε) {n : ℕ} (hn : N ≤ n) :
    (L.sub (T n)).IsBoundedBy ε :=
  (hL.sub_const (T n)).isBoundedBy (N := N) (fun m hm => hc m n hm hn)

/-- The strong limit of an eventually norm-Cauchy sequence with one bounded term is bounded. -/
theorem IsStrongLimit.isBounded {T : ℕ → Adjointable E F} {L : Adjointable E F}
    (hL : IsStrongLimit T L) {N : ℕ}
    (hc : ∀ m n : ℕ, N ≤ m → N ≤ n → ((T m).sub (T n)).IsBoundedBy 1)
    (hT : (T N).IsBounded) : L.IsBounded := by
  have h1 : (L.sub (T N)).IsBoundedBy 1 := hL.isBoundedBy_sub hc le_rfl
  obtain ⟨C, hC, hCb⟩ := hT
  have h2 : ((L.sub (T N)).add (T N)).IsBoundedBy (1 + C) := h1.add hCb
  have hx : ∀ x : E.carrier, ((L.sub (T N)).add (T N)).toFun x = L.toFun x := by
    intro x
    show L.toFun x - (T N).toFun x + (T N).toFun x = L.toFun x
    abel
  exact Adjointable.IsBounded.congr hx
    (Adjointable.IsBoundedBy.isBounded (by linarith) h2)

/-- **A strong limit of a norm-Cauchy sequence of compact operators is compact**
(Elliott–Kucerovsky 2001, proof of Thm. 6: the error series). -/
theorem IsStrongLimit.isCompactOp {T : ℕ → Adjointable E F} {L : Adjointable E F}
    (hL : IsStrongLimit T L) (hK : ∀ n : ℕ, (T n).IsCompactOp)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      ((T m).sub (T n)).IsBoundedBy ε) :
    L.IsCompactOp := by
  obtain ⟨N₁, hN₁⟩ := hc 1 one_pos
  refine Adjointable.isCompactOp_of_approx (hL.isBounded hN₁ (hK N₁).isBounded) ?_
  intro ε hε
  obtain ⟨N, hN⟩ := hc ε hε
  exact ⟨T N, hK N, hL.isBoundedBy_sub hN le_rfl⟩

/-- **Strong limits of products**: if the left factors are uniformly bounded, the products of
strongly convergent sequences converge strongly to the product of the limits. -/
theorem IsStrongLimit.comp {A : ℕ → Adjointable F G} {A' : Adjointable F G}
    {T : ℕ → Adjointable E F} {T' : Adjointable E F}
    (hA : IsStrongLimit A A') (hT : IsStrongLimit T T') {C : ℝ} (hC : 0 ≤ C)
    (hAb : ∀ n : ℕ, (A n).IsBoundedBy C) :
    IsStrongLimit (fun n => (A n).comp (T n)) (A'.comp T') := by
  intro x ε hε
  have hCpos : (0 : ℝ) < C + 1 := by linarith
  obtain ⟨N₁, hN₁⟩ := hA (T'.toFun x) (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := hT x (ε / 2 / (C + 1)) (div_pos (half_pos hε) hCpos)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left N₁ N₂) hn)
  have h2 := hN₂ n (le_trans (le_max_right N₁ N₂) hn)
  have h3 := hAb n (T'.toFun x - (T n).toFun x)
  have h4 : C * F.norm (T'.toFun x - (T n).toFun x) ≤ C * (ε / 2 / (C + 1)) :=
    mul_le_mul_of_nonneg_left h2 hC
  have hCε : C * (ε / 2 / (C + 1)) ≤ ε / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hCpos]
    nlinarith [hε.le, hC]
  have hsplit : A'.toFun (T'.toFun x) - (A n).toFun ((T n).toFun x)
      = (A'.toFun (T'.toFun x) - (A n).toFun (T'.toFun x))
        + (A n).toFun (T'.toFun x - (T n).toFun x) := by
    rw [(A n).map_sub]
    abel
  show G.norm (A'.toFun (T'.toFun x) - (A n).toFun ((T n).toFun x)) ≤ ε
  rw [hsplit]
  have h5 := G.norm_add_le (A'.toFun (T'.toFun x) - (A n).toFun (T'.toFun x))
    ((A n).toFun (T'.toFun x - (T n).toFun x))
  linarith

/-- **Strong limits of sums.** -/
theorem IsStrongLimit.add {A : ℕ → Adjointable E F} {A' : Adjointable E F}
    {T : ℕ → Adjointable E F} {T' : Adjointable E F}
    (hA : IsStrongLimit A A') (hT : IsStrongLimit T T') :
    IsStrongLimit (fun n => (A n).add (T n)) (A'.add T') := by
  intro x ε hε
  obtain ⟨N₁, hN₁⟩ := hA x (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := hT x (ε / 2) (half_pos hε)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_trans (le_max_left N₁ N₂) hn)
  have h2 := hN₂ n (le_trans (le_max_right N₁ N₂) hn)
  show F.norm (A'.toFun x + T'.toFun x - ((A n).toFun x + (T n).toFun x)) ≤ ε
  have hsplit : A'.toFun x + T'.toFun x - ((A n).toFun x + (T n).toFun x)
      = (A'.toFun x - (A n).toFun x) + (T'.toFun x - (T n).toFun x) := by abel
  rw [hsplit]
  have h3 := F.norm_add_le (A'.toFun x - (A n).toFun x) (T'.toFun x - (T n).toFun x)
  linarith

/-- **Strong limits are unique** (pointwise). -/
theorem IsStrongLimit.toFun_eq {T : ℕ → Adjointable E F} {L L' : Adjointable E F}
    (h : IsStrongLimit T L) (h' : IsStrongLimit T L') (x : E.carrier) :
    L.toFun x = L'.toFun x := by
  have hle : ∀ ε : ℝ, 0 < ε → F.norm (L.toFun x - L'.toFun x) ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := h x (ε / 2) (half_pos hε)
    obtain ⟨N', hN'⟩ := h' x (ε / 2) (half_pos hε)
    have h1 := hN (max N N') (le_max_left N N')
    have h2 := hN' (max N N') (le_max_right N N')
    have hsplit : L.toFun x - L'.toFun x = (L.toFun x - (T (max N N')).toFun x)
        + -(L'.toFun x - (T (max N N')).toFun x) := by abel
    have h3 := F.norm_add_le (L.toFun x - (T (max N N')).toFun x)
      (-(L'.toFun x - (T (max N N')).toFun x))
    rw [F.norm_neg, ← hsplit] at h3
    linarith
  have h0 : F.norm (L.toFun x - L'.toFun x) = 0 := by
    refine le_antisymm ?_ (F.norm_nonneg _)
    by_contra hne
    have hpos : 0 < F.norm (L.toFun x - L'.toFun x) := not_le.mp hne
    have h4 := hle (F.norm (L.toFun x - L'.toFun x) / 2) (half_pos hpos)
    linarith
  exact sub_eq_zero.mp ((F.norm_eq_zero_iff _).mp h0)

end GroupApproximation.Full.TWWSchafhauser

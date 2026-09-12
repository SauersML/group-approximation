import GroupApproximation.CharClass.OddPTopPowerAW

/-!
# The iterated Alexander–Whitney diagonal is a natural chain map

The second half of the top-power groundwork.  `OddPTopPowerAW.lean` builds the left-nested
diagonal `awAll K X r` on the full tuple model; this file proves

* `tupDAll_awAll` — `d (AW^{(r)} τ) = AW^{(r)} (∂τ)`, at every arity and over every commutative
  ring;
* `tupAllMap_awAll` — naturality in the space.

## The binary law

The induction on the arity uses the concatenation law of `OddPTopPowerAW.lean` once and the
binary Alexander–Whitney law `binary_aw` once:

    Σ_i  ∂(σ[0..i]) ⊗ σ[i..k]  +  (−1)^i σ[0..i] ⊗ ∂(σ[i..k])   =   Σ_v (−1)^v AW(d_v σ),

proved for an arbitrary bilinear map `B`, so that the second factor may already be the
diagonal of the remaining arity.  The last face of a front face and the first face of the next
back face are the same pair with opposite signs (`aw_term_front`, `aw_term_back`); what remains
are the interior faces, and a face `d_v σ` contributes to exactly one of the two families,
according as the removed vertex `v` lies in the front (`v ≤ i`) or in the back (`v > i`).
-/

namespace GroupApproximation.CharClass

open CategoryTheory Simplicial
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace TopPow

/-! ## 1. Faces of sub-simplices, split at an end -/

section Faces

variable {X : TopCat.{0}}

theorem tagBd_vtx_last (K : Type) [CommRing K] {k : ℕ} (σ : singularSimplices X k) (a : ℕ)
    {v : ℕ → ℕ} (hv : Monotone v) :
    tagBd K X (vtx σ (a + 1) v hv)
      = ∑ l ∈ Finset.range (a + 1),
          ((-1 : K) ^ l) • Finsupp.single (vtx σ a (v ∘ succAb l) (hv.comp (succAb_mono l))) (1 : K)
        + ((-1 : K) ^ (a + 1)) •
            Finsupp.single (vtx σ a (v ∘ succAb (a + 1)) (hv.comp (succAb_mono (a + 1)))) (1 : K) :=
  (tagBd_vtx K σ a hv).trans (Finset.sum_range_succ _ (a + 1))

theorem tagBd_vtx_first (K : Type) [CommRing K] {k : ℕ} (σ : singularSimplices X k) (a : ℕ)
    {v : ℕ → ℕ} (hv : Monotone v) :
    tagBd K X (vtx σ (a + 1) v hv)
      = ∑ l ∈ Finset.range (a + 1),
          ((-1 : K) ^ (l + 1)) •
            Finsupp.single (vtx σ a (v ∘ succAb (l + 1)) (hv.comp (succAb_mono (l + 1)))) (1 : K)
        + ((-1 : K) ^ 0) • Finsupp.single (vtx σ a (v ∘ succAb 0) (hv.comp (succAb_mono 0))) (1 : K) :=
  (tagBd_vtx K σ a hv).trans (Finset.sum_range_succ' _ (a + 1))

/-! ## 2. Front and back faces of a face -/

theorem awFront_face {n : ℕ} (σ : singularSimplices X (n + 1)) (v i : ℕ) (hin : i ≤ n) :
    awFront (vtx σ n (succAb v) (succAb_mono v)) i = vtx σ i (succAb v) (succAb_mono v) :=
  vtx_vtx σ n (succAb_mono v) i monotone_id fun j hj => by
    show j ≤ n
    omega

theorem awBack_face {n : ℕ} (σ : singularSimplices X (n + 1)) (v i : ℕ) (hin : i ≤ n) :
    awBack (vtx σ n (succAb v) (succAb_mono v)) i
      = vtx σ (n - i) (succAb v ∘ fun j => j + i) ((succAb_mono v).comp (addRight_mono i)) :=
  vtx_vtx σ n (succAb_mono v) (n - i) (addRight_mono i) fun j hj => by
    show j + i ≤ n
    omega

end Faces

/-! ## 3. The binary law -/

section Binary

variable {X : TopCat.{0}} (K : Type) [CommRing K] {M : Type} [AddCommGroup M] [Module K M]
  (B : (TagSimp X →₀ K) →ₗ[K] (TagSimp X →₀ K) →ₗ[K] M)

/-- The front half at a cut `i + 1`: the interior faces of the front, and its last face. -/
theorem aw_term_front (n : ℕ) (σ : singularSimplices X (n + 1)) (i : ℕ) (hi : i ≤ n) :
    B (tagBd K X (awFront (⟨n + 1, σ⟩ : TagSimp X) (i + 1)))
        (Finsupp.single (awBack (⟨n + 1, σ⟩ : TagSimp X) (i + 1)) 1)
      = ∑ l ∈ Finset.range (i + 1), ((-1 : K) ^ l) •
          B (Finsupp.single (vtx σ i (succAb l) (succAb_mono l)) 1)
            (Finsupp.single (vtx σ (n - i) (fun j => j + (i + 1)) (addRight_mono (i + 1))) 1)
        + ((-1 : K) ^ (i + 1)) •
          B (Finsupp.single (vtx σ i id monotone_id) 1)
            (Finsupp.single (vtx σ (n - i) (fun j => j + (i + 1)) (addRight_mono (i + 1))) 1) := by
  have hback : awBack (⟨n + 1, σ⟩ : TagSimp X) (i + 1)
      = vtx σ (n - i) (fun j => j + (i + 1)) (addRight_mono (i + 1)) :=
    vtx_congr σ (addRight_mono (i + 1)) (addRight_mono (i + 1))
      (by show n + 1 - (i + 1) = n - i; omega) fun _ _ => rfl
  have hfront : awFront (⟨n + 1, σ⟩ : TagSimp X) (i + 1) = vtx σ (i + 1) id monotone_id := rfl
  have hlast : vtx σ i (id ∘ succAb (i + 1)) (monotone_id.comp (succAb_mono (i + 1)))
      = vtx σ i id monotone_id :=
    vtx_congr σ _ _ rfl fun j hj => by
      simp only [Function.comp_apply, id_eq, succAb]
      split_ifs <;> omega
  rw [hback, hfront, tagBd_vtx_last, hlast, map_add, map_sum, LinearMap.add_apply,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  refine congrArg (· + _) (Finset.sum_congr rfl fun l _ => ?_)
  have hid : vtx σ i (id ∘ succAb l) (monotone_id.comp (succAb_mono l))
      = vtx σ i (succAb l) (succAb_mono l) := rfl
  rw [hid, map_smul, LinearMap.smul_apply]

/-- The back half at a cut `i ≤ n`: the interior faces of the back, and its first face. -/
theorem aw_term_back (n : ℕ) (σ : singularSimplices X (n + 1)) (i : ℕ) (hi : i ≤ n) :
    ((-1 : K) ^ i) • B (Finsupp.single (awFront (⟨n + 1, σ⟩ : TagSimp X) i) 1)
        (tagBd K X (awBack (⟨n + 1, σ⟩ : TagSimp X) i))
      = ∑ l ∈ Finset.range (n - i + 1), ((-1 : K) ^ (i + (l + 1))) •
          B (Finsupp.single (vtx σ i id monotone_id) 1)
            (Finsupp.single (vtx σ (n - i) ((fun j => j + i) ∘ succAb (l + 1))
              ((addRight_mono i).comp (succAb_mono (l + 1)))) 1)
        + ((-1 : K) ^ i) •
          B (Finsupp.single (vtx σ i id monotone_id) 1)
            (Finsupp.single (vtx σ (n - i) (fun j => j + (i + 1)) (addRight_mono (i + 1))) 1) := by
  have hback : awBack (⟨n + 1, σ⟩ : TagSimp X) i
      = vtx σ (n - i + 1) (fun j => j + i) (addRight_mono i) :=
    vtx_congr σ (addRight_mono i) (addRight_mono i)
      (by show n + 1 - i = n - i + 1; omega) fun _ _ => rfl
  have hfront : awFront (⟨n + 1, σ⟩ : TagSimp X) i = vtx σ i id monotone_id := rfl
  have hzero : vtx σ (n - i) ((fun j => j + i) ∘ succAb 0) ((addRight_mono i).comp (succAb_mono 0))
      = vtx σ (n - i) (fun j => j + (i + 1)) (addRight_mono (i + 1)) :=
    vtx_congr σ _ _ rfl fun j _ => by
      simp only [Function.comp_apply, succAb]
      split_ifs <;> omega
  rw [hback, hfront, tagBd_vtx_first, hzero, map_add, map_sum, map_smul, pow_zero, one_smul,
    smul_add, Finset.smul_sum]
  refine congrArg (· + _) (Finset.sum_congr rfl fun l _ => ?_)
  rw [map_smul, smul_smul, ← pow_add]

theorem aw_term_front_zero (n : ℕ) (σ : singularSimplices X (n + 1)) :
    B (tagBd K X (awFront (⟨n + 1, σ⟩ : TagSimp X) 0))
        (Finsupp.single (awBack (⟨n + 1, σ⟩ : TagSimp X) 0) 1) = 0 := by
  have h : tagBd K X (awFront (⟨n + 1, σ⟩ : TagSimp X) 0) = 0 := rfl
  rw [h, map_zero, LinearMap.zero_apply]

theorem aw_term_back_last (n : ℕ) (σ : singularSimplices X (n + 1)) :
    ((-1 : K) ^ (n + 1)) • B (Finsupp.single (awFront (⟨n + 1, σ⟩ : TagSimp X) (n + 1)) 1)
        (tagBd K X (awBack (⟨n + 1, σ⟩ : TagSimp X) (n + 1))) = 0 := by
  have hback : awBack (⟨n + 1, σ⟩ : TagSimp X) (n + 1)
      = vtx σ 0 (fun j => j + (n + 1)) (addRight_mono (n + 1)) :=
    vtx_congr σ (addRight_mono (n + 1)) (addRight_mono (n + 1))
      (by show n + 1 - (n + 1) = 0; omega) fun _ _ => rfl
  rw [hback, tagBd_vtx_zero, map_zero, smul_zero]

/-- **The binary Alexander–Whitney law**, for an arbitrary bilinear map. -/
theorem binary_aw (n : ℕ) (σ : singularSimplices X (n + 1)) :
    ∑ i ∈ Finset.range (n + 1 + 1),
        (B (tagBd K X (awFront (⟨n + 1, σ⟩ : TagSimp X) i))
            (Finsupp.single (awBack (⟨n + 1, σ⟩ : TagSimp X) i) 1)
          + ((-1 : K) ^ i) • B (Finsupp.single (awFront (⟨n + 1, σ⟩ : TagSimp X) i) 1)
              (tagBd K X (awBack (⟨n + 1, σ⟩ : TagSimp X) i)))
      = ∑ v ∈ Finset.range (n + 1 + 1), ((-1 : K) ^ v) •
          ∑ i ∈ Finset.range (n + 1),
            B (Finsupp.single (awFront (vtx σ n (succAb v) (succAb_mono v)) i) 1)
              (Finsupp.single (awBack (vtx σ n (succAb v) (succAb_mono v)) i) 1) := by
  -- the left side: split off the two degenerate cuts, then the two endpoint families cancel
  have hL : ∑ i ∈ Finset.range (n + 1 + 1),
        (B (tagBd K X (awFront (⟨n + 1, σ⟩ : TagSimp X) i))
            (Finsupp.single (awBack (⟨n + 1, σ⟩ : TagSimp X) i) 1)
          + ((-1 : K) ^ i) • B (Finsupp.single (awFront (⟨n + 1, σ⟩ : TagSimp X) i) 1)
              (tagBd K X (awBack (⟨n + 1, σ⟩ : TagSimp X) i)))
      = ∑ i ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (i + 1), ((-1 : K) ^ l) •
            B (Finsupp.single (vtx σ i (succAb l) (succAb_mono l)) 1)
              (Finsupp.single (vtx σ (n - i) (fun j => j + (i + 1)) (addRight_mono (i + 1))) 1)
        + ∑ i ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n - i + 1), ((-1 : K) ^ (i + (l + 1))) •
            B (Finsupp.single (vtx σ i id monotone_id) 1)
              (Finsupp.single (vtx σ (n - i) ((fun j => j + i) ∘ succAb (l + 1))
                ((addRight_mono i).comp (succAb_mono (l + 1)))) 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_range_succ' _ (n + 1), aw_term_front_zero, add_zero,
      Finset.sum_range_succ _ (n + 1), aw_term_back_last, add_zero,
      Finset.sum_congr rfl fun i hi =>
        aw_term_front K B n σ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),
      Finset.sum_congr rfl fun i hi =>
        aw_term_back K B n σ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),
      Finset.sum_add_distrib, Finset.sum_add_distrib, add_add_add_comm]
    have hE : ∑ i ∈ Finset.range (n + 1), ((-1 : K) ^ (i + 1)) •
            B (Finsupp.single (vtx σ i id monotone_id) 1)
              (Finsupp.single (vtx σ (n - i) (fun j => j + (i + 1)) (addRight_mono (i + 1))) 1)
        + ∑ i ∈ Finset.range (n + 1), ((-1 : K) ^ i) •
            B (Finsupp.single (vtx σ i id monotone_id) 1)
              (Finsupp.single (vtx σ (n - i) (fun j => j + (i + 1)) (addRight_mono (i + 1))) 1)
        = 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => by rw [pow_succ, mul_neg_one, neg_smul, neg_add_cancel]
    rw [hE, add_zero]
  -- the right side: each face `d_v σ` lands in the front family (`v ≤ i`) or the back one
  have hR : ∑ v ∈ Finset.range (n + 1 + 1), ((-1 : K) ^ v) •
          ∑ i ∈ Finset.range (n + 1),
            B (Finsupp.single (awFront (vtx σ n (succAb v) (succAb_mono v)) i) 1)
              (Finsupp.single (awBack (vtx σ n (succAb v) (succAb_mono v)) i) 1)
      = ∑ i ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (i + 1), ((-1 : K) ^ l) •
            B (Finsupp.single (vtx σ i (succAb l) (succAb_mono l)) 1)
              (Finsupp.single (vtx σ (n - i) (fun j => j + (i + 1)) (addRight_mono (i + 1))) 1)
        + ∑ i ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n - i + 1), ((-1 : K) ^ (i + (l + 1))) •
            B (Finsupp.single (vtx σ i id monotone_id) 1)
              (Finsupp.single (vtx σ (n - i) ((fun j => j + i) ∘ succAb (l + 1))
                ((addRight_mono i).comp (succAb_mono (l + 1)))) 1) := by
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    rw [← Finset.sum_range_add_sum_Ico _ (show i + 1 ≤ n + 1 + 1 by omega),
      Finset.sum_Ico_eq_sum_range, show n + 1 + 1 - (i + 1) = n - i + 1 by omega]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun v hv => ?_)
      (Finset.sum_congr rfl fun l _ => ?_)
    · have hvi : v ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hv)
      have hlow : vtx σ (n - i) (succAb v ∘ fun j => j + i) ((succAb_mono v).comp (addRight_mono i))
          = vtx σ (n - i) (fun j => j + (i + 1)) (addRight_mono (i + 1)) :=
        vtx_congr σ _ _ rfl fun j _ => by
          simp only [Function.comp_apply, succAb]
          split_ifs <;> omega
      rw [awFront_face σ v i hin, awBack_face σ v i hin, hlow]
    · have hfr : vtx σ i (succAb (i + 1 + l)) (succAb_mono (i + 1 + l)) = vtx σ i id monotone_id :=
        vtx_congr σ _ _ rfl fun j hj => by
          simp only [id_eq, succAb]
          split_ifs <;> omega
      have hbk : vtx σ (n - i) (succAb (i + 1 + l) ∘ fun j => j + i)
            ((succAb_mono (i + 1 + l)).comp (addRight_mono i))
          = vtx σ (n - i) ((fun j => j + i) ∘ succAb (l + 1))
              ((addRight_mono i).comp (succAb_mono (l + 1))) :=
        vtx_congr σ _ _ rfl fun j _ => by
          simp only [Function.comp_apply, succAb]
          split_ifs <;> omega
      rw [awFront_face σ (i + 1 + l) i hin, awBack_face σ (i + 1 + l) i hin, hfr, hbk,
        show i + 1 + l = i + (l + 1) by omega]
  rw [hL, hR]

end Binary

/-! ## 4. The chain-map law -/

section Chain

variable (K : Type) [CommRing K] (X : TopCat.{0})

/-- **The iterated Alexander–Whitney diagonal is a chain map**: `d (AW^{(r)} τ) = AW^{(r)} (∂τ)`. -/
theorem tupDAll_awAll (r : ℕ) (τ : TagSimp X) :
    tupDAll K X r (awAll K X r τ) = awLin K X r (tagBd K X τ) := by
  induction r generalizing τ with
  | zero =>
    have h0 : tupDAll K X 0 = 0 := by
      rw [tupDAll, Fin.sum_univ_zero]
    rw [h0, LinearMap.zero_apply]
    obtain ⟨_ | n, σ⟩ := τ
    · rw [tagBd_zero, map_zero]
    · rw [tagBd_eq_sum, map_sum]
      rcases n with _ | n
      · have hpt : ∀ l : ℕ, awLin K X 0
            (((-1 : K) ^ l) • Finsupp.single (vtx σ 0 (succAb l) (succAb_mono l)) 1)
              = ((-1 : K) ^ l) • Finsupp.single (Fin.elim0 : TupAll X 0) 1 := fun l => by
          rw [map_smul, awLin_single, awAll_zero, if_pos (vtx_fst σ 0 (succAb l) (succAb_mono l))]
        rw [Finset.sum_congr rfl fun l _ => hpt l, ← Finset.sum_smul,
          show (∑ l ∈ Finset.range (0 + 1 + 1), (-1 : K) ^ l) = 0 by simp [Finset.sum_range_succ],
          zero_smul]
      · refine (Finset.sum_eq_zero fun l _ => ?_).symm
        rw [map_smul, awLin_single, awAll_zero,
          if_neg (show (vtx σ (n + 1) (succAb l) (succAb_mono l)).1 ≠ 0 from Nat.succ_ne_zero n),
          smul_zero]
  | succ r ih =>
    obtain ⟨k, σ⟩ := τ
    have hterm : ∀ i ∈ Finset.range (k + 1),
        tupDAll K X (r + 1) (catLin K X r (awAll K X r (awFront (⟨k, σ⟩ : TagSimp X) i))
            (Finsupp.single (awBack (⟨k, σ⟩ : TagSimp X) i) 1))
          = (catLin K X r).comp (awLin K X r) (tagBd K X (awFront (⟨k, σ⟩ : TagSimp X) i))
              (Finsupp.single (awBack (⟨k, σ⟩ : TagSimp X) i) 1)
            + ((-1 : K) ^ i) • (catLin K X r).comp (awLin K X r)
                (Finsupp.single (awFront (⟨k, σ⟩ : TagSimp X) i) 1)
                (tagBd K X (awBack (⟨k, σ⟩ : TagSimp X) i)) := by
      intro i _
      have hx : awAll K X r (awFront (⟨k, σ⟩ : TagSimp X) i)
          ∈ Finsupp.supported K K (degSetT X r i) :=
        awAll_mem K X r (awFront (⟨k, σ⟩ : TagSimp X) i)
      rw [tupDAll_catLin_of_mem K X hx, ih, LinearMap.comp_apply, LinearMap.comp_apply,
        awLin_single]
    rw [awAll_succ, map_sum, Finset.sum_congr rfl hterm]
    rcases k with _ | n
    · have h1 : tagBd K X (awFront (⟨0, σ⟩ : TagSimp X) 0) = 0 := rfl
      have h2 : tagBd K X (awBack (⟨0, σ⟩ : TagSimp X) 0) = 0 := rfl
      rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h1, h2, tagBd_zero]
      simp
    · rw [tagBd_eq_sum, map_sum]
      refine (binary_aw K ((catLin K X r).comp (awLin K X r)) n σ).trans ?_
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [map_smul, awLin_single, awAll_succ]
      refine congrArg (fun z => ((-1 : K) ^ v) • z) (Finset.sum_congr rfl fun i _ => ?_)
      rw [LinearMap.comp_apply, awLin_single]

end Chain

/-! ## 5. Naturality -/

section Natural

variable (K : Type) [CommRing K] {X Y : TopCat.{0}} (f : X ⟶ Y)

theorem tagPush_vtx {k : ℕ} (σ : singularSimplices X k) (a : ℕ) (v : ℕ → ℕ) (hv : Monotone v) :
    tagPush f (vtx σ a v hv) = vtx (pushSimplex f k σ) a v hv := by
  have h : pushSimplex f a ((TopCat.toSSet.obj X).map (clampHom a k v hv).op σ)
      = (TopCat.toSSet.obj Y).map (clampHom a k v hv).op (pushSimplex f k σ) := by
    simpa only [pushSimplex, ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom ((TopCat.toSSet.map f).naturality (clampHom a k v hv).op) σ
  exact congrArg (Sigma.mk a) h

theorem tagPush_awFront (τ : TagSimp X) (i : ℕ) : tagPush f (awFront τ i) = awFront (tagPush f τ) i :=
  tagPush_vtx f τ.2 i id monotone_id

theorem tagPush_awBack (τ : TagSimp X) (i : ℕ) : tagPush f (awBack τ i) = awBack (tagPush f τ) i :=
  tagPush_vtx f τ.2 (τ.1 - i) (fun j => j + i) (addRight_mono i)

theorem tupPush_snocT {r : ℕ} (t : TupAll X r) (τ : TagSimp X) :
    tupPush f (snocT X t τ) = snocT Y (tupPush f t) (tagPush f τ) := by
  funext j
  induction j using Fin.lastCases with
  | last =>
    show tagPush f (Fin.snoc t τ (Fin.last r)) = Fin.snoc (fun l => tagPush f (t l)) (tagPush f τ) (Fin.last r)
    rw [Fin.snoc_last, Fin.snoc_last]
  | cast j =>
    show tagPush f (Fin.snoc t τ j.castSucc) = Fin.snoc (fun l => tagPush f (t l)) (tagPush f τ) j.castSucc
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc]

theorem tupAllMap_catLin {r : ℕ} (x : tupAllMod K X r) (τ : TagSimp X) :
    tupAllMap K f (r + 1) (catLin K X r x (Finsupp.single τ 1))
      = catLin K Y r (tupAllMap K f r x) (Finsupp.single (tagPush f τ) 1) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y hx hy =>
    rw [map_add, LinearMap.add_apply, map_add, hx, hy, map_add, LinearMap.add_apply]
  | single t c =>
    rw [show Finsupp.single t c = c • Finsupp.single t (1 : K) by rw [Finsupp.smul_single_one],
      map_smul, LinearMap.smul_apply, map_smul, catLin_single, tupAllMap_single, map_smul,
      LinearMap.smul_apply, tupAllMap_single, catLin_single, tupPush_snocT]

/-- **The iterated Alexander–Whitney diagonal is natural in the space.** -/
theorem tupAllMap_awAll (r : ℕ) (τ : TagSimp X) :
    tupAllMap K f r (awAll K X r τ) = awAll K Y r (tagPush f τ) := by
  induction r generalizing τ with
  | zero =>
    rw [awAll_zero, awAll_zero]
    show _ = if τ.1 = 0 then _ else _
    split_ifs
    · rw [tupAllMap_single]
      exact congrArg (fun t => Finsupp.single t (1 : K)) (Subsingleton.elim _ _)
    · exact map_zero _
  | succ r ih =>
    rw [awAll_succ, awAll_succ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tupAllMap_catLin, ih, tagPush_awFront, tagPush_awBack]

end Natural

#audit_axioms binary_aw
#audit_axioms tupDAll_awAll
#audit_axioms tupAllMap_awAll

end TopPow

end

end GroupApproximation.CharClass

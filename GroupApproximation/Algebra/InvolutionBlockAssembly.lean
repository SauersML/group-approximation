import GroupApproximation.Algebra.InvolutionBlockSplit
import GroupApproximation.Algebra.PermutationTwoInvolutions

/-!
# The consumption count: every even permutation, in `4·fuel + 4` conjugates

This assembles the consumption half of the premise `hBNG` of proof-ledger row
`SO.17`, in purely arithmetic form — no `δ` yet, only a block capacity `c` and
a fuel.

The route is the one recorded in
`Algebra/AlternatingBoundedNormalGeneration.lean`:

1. factor the target as a product of two involutions
   (`PermutationTwoInvolutions.exists_two_involutions`);
2. their transposition counts have equal parity, because the target is even
   (`sign_involution` below with
   `PermutationTwoInvolutions.sign_eq_of_sign_mul_eq_one`);
3. if both counts are even, cut each involution into blocks of at most `c`
   pairs of transpositions (`InvolutionBlocks.exists_blocks`), each of which is
   reachable in two conjugates
   (`InvolutionBlocks.isBoundedConjProduct_two_of_involution`);
4. if both are odd, peel one transposition off each and pair them through a
   spare transposition `ρ` disjoint from both: `τ τ' = (τ ρ)(ρ τ')`, and each of
   `τ ρ` and `ρ τ'` is a product of two disjoint transpositions, hence of cycle
   type `2 + 2` and reachable.  The spare needs two points outside four, which
   is why `6 ≤ |Ω|` appears; it does **not** need points outside the support of
   the target, which may be everything.

The count is `4·fuel + 4`: two involutions, at most `fuel` blocks each, two
conjugates per block, plus the two repair factors.

What remains for `SO.17` is only the arithmetic that turns `|supp s| ≥ δ|Ω|`
into a fuel depending on `δ` alone — take `c = |supp s| / 6` and
`fuel = ⌈12/δ⌉` — and then the assembly of the manuscript's premise from this
theorem.
-/

namespace GroupApproximation
namespace InvolutionBlocks

open AlternatingBoundedNormalGeneration BoundedConjProductAlgebra
open SoficEnvelopeSimplicity

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ## Products of reachable elements -/

omit [Fintype Y] [DecidableEq Y] in
/-- A product of a list of elements each reachable in `K` conjugates is
reachable in `length · K`. -/
theorem isBoundedConjProduct_list {s : Equiv.Perm Y} :
    ∀ (L : List (Equiv.Perm Y)) (K : ℕ),
      (∀ z ∈ L, IsBoundedConjProduct s K z) →
        IsBoundedConjProduct s (L.length * K) L.prod := by
  intro L
  induction L with
  | nil =>
      intro K _
      simp
  | cons z L ih =>
      intro K h
      have h1 : IsBoundedConjProduct s K z := h z (List.mem_cons_self ..)
      have h2 : IsBoundedConjProduct s (L.length * K) L.prod :=
        ih K fun w hw => h w (List.mem_cons_of_mem z hw)
      have h3 := isBoundedConjProduct_mul K (L.length * K) z L.prod h1 h2
      have harith : (z :: L).length * K = K + L.length * K := by
        rw [List.length_cons]
        ring
      rw [List.prod_cons, harith]
      exact h3

/-! ## The sign of an involution -/

/-- An involution's sign is `(-1)` to the number of its transpositions. -/
theorem sign_involution {w : Equiv.Perm Y} (hw : w * w = 1) :
    Equiv.Perm.sign w = (-1 : ℤˣ) ^ Multiset.card w.cycleType := by
  have hsum : w.cycleType.sum = 2 * Multiset.card w.cycleType := by
    conv_lhs => rw [cycleType_involution hw]
    rw [Multiset.sum_replicate, smul_eq_mul, mul_comm]
  rw [Equiv.Perm.sign_of_cycleType, hsum, pow_add, pow_mul]
  simp
  rfl

/-- The two involutions of an even permutation have transposition counts of
equal parity. -/
theorem card_cycleType_parity {u v : Equiv.Perm Y} (hu : u * u = 1)
    (hv : v * v = 1) (h : Equiv.Perm.sign (u * v) = 1) :
    Multiset.card u.cycleType % 2 = Multiset.card v.cycleType % 2 := by
  have hsign : Equiv.Perm.sign u = Equiv.Perm.sign v :=
    PermutationTwoInvolutions.sign_eq_of_sign_mul_eq_one h
  rw [sign_involution hu, sign_involution hv] at hsign
  rcases Nat.even_or_odd (Multiset.card u.cycleType) with hue | huo
  · rcases Nat.even_or_odd (Multiset.card v.cycleType) with hve | hvo
    · rw [Nat.even_iff] at hue hve
      omega
    · -- `Even.neg_one_pow` leaves its carrier a metavariable, which does not
      -- resolve to `ℤˣ` from the rewrite target alone; ascribe both first.
      have h1 : ((-1 : ℤˣ)) ^ Multiset.card u.cycleType = 1 := hue.neg_one_pow
      have h2 : ((-1 : ℤˣ)) ^ Multiset.card v.cycleType = -1 := hvo.neg_one_pow
      rw [h1, h2] at hsign
      have hcast : ((1 : ℤˣ) : ℤ) = ((-1 : ℤˣ) : ℤ) := congrArg _ hsign
      norm_num at hcast
  · rcases Nat.even_or_odd (Multiset.card v.cycleType) with hve | hvo
    · have h1 : ((-1 : ℤˣ)) ^ Multiset.card u.cycleType = -1 := huo.neg_one_pow
      have h2 : ((-1 : ℤˣ)) ^ Multiset.card v.cycleType = 1 := hve.neg_one_pow
      rw [h1, h2] at hsign
      have hcast : ((-1 : ℤˣ) : ℤ) = ((1 : ℤˣ) : ℤ) := congrArg _ hsign
      norm_num at hcast
    · rw [Nat.odd_iff] at huo hvo
      omega

/-! ## Transpositions -/

/-- An involution with a single transposition has a two-point support. -/
theorem card_support_of_card_cycleType_one {w : Equiv.Perm Y} (hw : w * w = 1)
    (hcard : Multiset.card w.cycleType = 1) : w.support.card = 2 := by
  have hsum := Equiv.Perm.sum_cycleType w
  rw [cycleType_involution hw, hcard, Multiset.sum_replicate, smul_eq_mul] at hsum
  omega

/-- Two points outside a given finset, when there is room. -/
theorem exists_pair_not_mem {S : Finset Y} (hS : S.card + 2 ≤ Fintype.card Y) :
    ∃ x y : Y, x ∉ S ∧ y ∉ S ∧ x ≠ y := by
  have hcompl : (Sᶜ : Finset Y).card = Fintype.card Y - S.card :=
    Finset.card_compl _
  have hlt : 1 < (Sᶜ : Finset Y).card := by omega
  obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.mp hlt
  exact ⟨x, y, Finset.mem_compl.mp hx, Finset.mem_compl.mp hy, hxy⟩

/-! ## The consumption count -/

/-- **Every even permutation is a product of at most `4·fuel + 4` conjugates of
`s` and `s⁻¹`**, given a block capacity `c` with `6c ≤ |supp s|` and enough fuel
to cover the whole model.

The hypotheses are exactly the arithmetic the blocks need: `hfit` makes a block
of `c` pairs reachable, `hfuel` makes `fuel` blocks enough for an involution of
any support, and `hbig` provides the two spare points of the parity repair. -/
theorem isBoundedConjProduct_of_sign_eq_one {s a : Equiv.Perm Y} {c fuel : ℕ}
    (hc : 0 < c) (hfit : 6 * c ≤ s.support.card)
    (hfuel : Fintype.card Y ≤ 2 * (fuel * c)) (hbig : 6 ≤ Fintype.card Y)
    (ha : Equiv.Perm.sign a = 1) :
    IsBoundedConjProduct s (4 * fuel + 4) a := by
  classical
  have hmle : s.support.card ≤ Fintype.card Y := Finset.card_le_univ _
  have hroom : 2 * c ≤ Fintype.card Y := by omega
  obtain ⟨u, v, hu, hv, hauv, -, -⟩ :=
    PermutationTwoInvolutions.exists_two_involutions a
  have hpar : Multiset.card u.cycleType % 2 = Multiset.card v.cycleType % 2 := by
    refine card_cycleType_parity hu hv ?_
    rw [← hauv]
    exact ha
  -- an involution's support is twice its transposition count
  have hsupp_eq : ∀ w : Equiv.Perm Y, w * w = 1 →
      w.support.card = 2 * Multiset.card w.cycleType := by
    intro w hw
    have hsum := Equiv.Perm.sum_cycleType w
    rw [cycleType_involution hw, Multiset.sum_replicate, smul_eq_mul] at hsum
    omega
  -- each block is reachable in two conjugates
  have hblock : ∀ z : Equiv.Perm Y, z * z = 1 →
      (∃ k, Multiset.card z.cycleType = 2 * k ∧ k ≤ c) →
        IsBoundedConjProduct s 2 z := by
    rintro z hz ⟨k, hk, hkc⟩
    exact isBoundedConjProduct_two_of_involution hz hk (by omega) (by omega)
  -- an involution with `2q` transpositions is reachable in `2 * fuel`
  have hhalf : ∀ (w : Equiv.Perm Y) (q : ℕ), w * w = 1 →
      Multiset.card w.cycleType = 2 * q → 4 * q ≤ Fintype.card Y →
        IsBoundedConjProduct s (2 * fuel) w := by
    intro w q hw hq hqn
    obtain ⟨L, hLprod, hLmem, hLlen⟩ :=
      exists_blocks c hc fuel q (by omega) w hw hq
    have hL : IsBoundedConjProduct s (L.length * 2) L.prod :=
      isBoundedConjProduct_list L 2 fun z hz =>
        hblock z (hLmem z hz).1 (hLmem z hz).2
    rw [hLprod] at hL
    exact isBoundedConjProduct_mono (by omega) hL
  rcases Nat.even_or_odd (Multiset.card u.cycleType) with hue | huo
  · -- both counts even: two families of blocks
    obtain ⟨qu, hqu⟩ := hue
    obtain ⟨qv, hqv⟩ : ∃ q, Multiset.card v.cycleType = 2 * q := by
      have : Multiset.card v.cycleType % 2 = 0 := by omega
      exact ⟨Multiset.card v.cycleType / 2, by omega⟩
    have hu2 : Multiset.card u.cycleType = 2 * qu := by omega
    have hun : 4 * qu ≤ Fintype.card Y := by
      have := hsupp_eq u hu
      have hle : u.support.card ≤ Fintype.card Y := Finset.card_le_univ _
      omega
    have hvn : 4 * qv ≤ Fintype.card Y := by
      have := hsupp_eq v hv
      have hle : v.support.card ≤ Fintype.card Y := Finset.card_le_univ _
      omega
    have hU := hhalf u qu hu hu2 hun
    have hV := hhalf v qv hv hqv hvn
    have hprod := isBoundedConjProduct_mul _ _ _ _ hU hV
    rw [← hauv] at hprod
    exact isBoundedConjProduct_mono (by omega) hprod
  · -- both counts odd: peel one transposition off each and pair them
    obtain ⟨qu, hqu⟩ := huo
    obtain ⟨qv, hqv⟩ : ∃ q, Multiset.card v.cycleType = 2 * q + 1 := by
      have : Multiset.card v.cycleType % 2 = 1 := by omega
      exact ⟨Multiset.card v.cycleType / 2, by omega⟩
    -- peel
    obtain ⟨u₀, u₁, hu01, hu0, hu1, hcu0, hcu1⟩ :=
      exists_split hu (2 * qu)
    obtain ⟨v₁, v₀, hv01, hv1, hv0, hcv1, hcv0⟩ := exists_split hv 1
    have hcu0' : Multiset.card u₀.cycleType = 2 * qu := by omega
    have hcu1' : Multiset.card u₁.cycleType = 1 := by omega
    have hcv1' : Multiset.card v₁.cycleType = 1 := by omega
    have hcv0' : Multiset.card v₀.cycleType = 2 * qv := by omega
    -- the two peeled transpositions
    have hsu1 : u₁.support.card = 2 := card_support_of_card_cycleType_one hu1 hcu1'
    have hsv1 : v₁.support.card = 2 := card_support_of_card_cycleType_one hv1 hcv1'
    have hunion : (u₁.support ∪ v₁.support).card + 2 ≤ Fintype.card Y := by
      have := Finset.card_union_le u₁.support v₁.support
      omega
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_pair_not_mem hunion
    -- the spare transposition, disjoint from both
    have hdx : ∀ w : Equiv.Perm Y, w.support ⊆ u₁.support ∪ v₁.support →
        Equiv.Perm.Disjoint w (Equiv.swap x y) := by
      intro w hw
      rw [Equiv.Perm.disjoint_iff_disjoint_support, Finset.disjoint_left]
      intro z hz hz'
      rw [Equiv.Perm.support_swap hxy, Finset.mem_insert,
        Finset.mem_singleton] at hz'
      rcases hz' with rfl | rfl
      · exact hx (hw hz)
      · exact hy (hw hz)
    have hdu : Equiv.Perm.Disjoint u₁ (Equiv.swap x y) :=
      hdx u₁ Finset.subset_union_left
    have hdv : Equiv.Perm.Disjoint v₁ (Equiv.swap x y) :=
      hdx v₁ Finset.subset_union_right
    have hswapsq : Equiv.swap x y * Equiv.swap x y = 1 := Equiv.swap_mul_self x y
    -- the two repair factors are involutions of cycle type `2 + 2`
    have hrepair : ∀ w : Equiv.Perm Y, w * w = 1 →
        Multiset.card w.cycleType = 1 → Equiv.Perm.Disjoint w (Equiv.swap x y) →
          IsBoundedConjProduct s 2 (w * Equiv.swap x y) ∧
            IsBoundedConjProduct s 2 (Equiv.swap x y * w) := by
      intro w hw hcw hdw
      have hcomm : w * Equiv.swap x y = Equiv.swap x y * w := hdw.commute.eq
      have hsq : (w * Equiv.swap x y) * (w * Equiv.swap x y) = 1 := by
        calc (w * Equiv.swap x y) * (w * Equiv.swap x y)
            = w * (Equiv.swap x y * w) * Equiv.swap x y := by group
          _ = w * (w * Equiv.swap x y) * Equiv.swap x y := by rw [← hcomm]
          _ = (w * w) * (Equiv.swap x y * Equiv.swap x y) := by group
          _ = 1 := by rw [hw, hswapsq, mul_one]
      have hct : Multiset.card (w * Equiv.swap x y).cycleType = 2 := by
        rw [hdw.cycleType_mul, Multiset.card_add, hcw,
          (Equiv.Perm.isCycle_swap hxy).cycleType]
        simp
      have hreach : IsBoundedConjProduct s 2 (w * Equiv.swap x y) :=
        isBoundedConjProduct_two_of_involution hsq
          (k := 1) (by omega) (by omega) (by omega)
      exact ⟨hreach, hcomm ▸ hreach⟩
    obtain ⟨hB, -⟩ := hrepair u₁ hu1 hcu1' hdu
    obtain ⟨-, hC⟩ := hrepair v₁ hv1 hcv1' hdv
    -- the two block families
    have hun : 4 * qu ≤ Fintype.card Y := by
      have := hsupp_eq u₀ hu0
      have hle : u₀.support.card ≤ Fintype.card Y := Finset.card_le_univ _
      omega
    have hvn : 4 * qv ≤ Fintype.card Y := by
      have := hsupp_eq v₀ hv0
      have hle : v₀.support.card ≤ Fintype.card Y := Finset.card_le_univ _
      omega
    have hA := hhalf u₀ qu hu0 hcu0' hun
    have hD := hhalf v₀ qv hv0 hcv0' hvn
    -- combine
    have h1 := isBoundedConjProduct_mul _ _ _ _ hA hB
    have h2 := isBoundedConjProduct_mul _ _ _ _ h1 hC
    have h3 := isBoundedConjProduct_mul _ _ _ _ h2 hD
    have hchain : u₀ * (u₁ * Equiv.swap x y) * (Equiv.swap x y * v₁) * v₀ = a := by
      calc u₀ * (u₁ * Equiv.swap x y) * (Equiv.swap x y * v₁) * v₀
          = u₀ * u₁ * (Equiv.swap x y * Equiv.swap x y) * (v₁ * v₀) := by group
        _ = u₀ * u₁ * 1 * (v₁ * v₀) := by rw [hswapsq]
        _ = (u₀ * u₁) * (v₁ * v₀) := by rw [mul_one]
        _ = u * v := by rw [hu01, hv01]
        _ = a := hauv.symm
    rw [hchain] at h3
    exact isBoundedConjProduct_mono (by omega) h3

end InvolutionBlocks
end GroupApproximation

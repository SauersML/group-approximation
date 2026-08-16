import GroupApproximation.Sofic.CyclicStack

/-!
# Cyclic extension permanence for sofic actions

**Theorem 12.1** of the ascending-HNN dossier.  If the normal part of a
semidirect product `N ⋊[φ] ℤ` acts soficly on a set and the whole product acts
compatibly, then the whole product acts soficly.

The model stacks `L` twisted copies of an `N`-model around a cycle of length
`L`.  The permutation layer is `Sofic.CyclicStack`; what this file adds is the
chart layer.  The chart at the stack point `(j, a)` is
`π_{(j,a)}(x) = ρ_a (t^{-j} · x)`, and the covariance identity comes from the
group identity

`(inl (φ^{-k} n))⁻¹ * t^{-k} = t^{-j} * (inl n * t^q)⁻¹`  for `k = j + q`,

which says exactly that undoing the twisted label at height `k` is the same as
descending `j` levels and then undoing `g`.

This lemma is useful beyond the ascending-HNN problem: soficity of an action is
stable under adjoining a compatible cyclic normalizer.
-/

namespace GroupApproximation
namespace CyclicStack

open SemidirectProduct SoficIntegerExtension

universe u v

variable {N : Type u} [Group N] {X : Type v} [MulAction N X]
variable (φ : Multiplicative ℤ →* MulAut N)

/-- The stable letter, as an element of the semidirect product. -/
def tpow (m : ℤ) : N ⋊[φ] Multiplicative ℤ := inr (Multiplicative.ofAdd m)

theorem tpow_add (m m' : ℤ) : tpow φ (m + m') = tpow φ m * tpow φ m' := by
  simp [tpow, ← map_mul, ← ofAdd_add]

theorem tpow_neg (m : ℤ) : tpow φ (-m) = (tpow φ m)⁻¹ := by
  simp [tpow, ← map_inv, ← ofAdd_neg]

/-- The decomposition of an element into its normal part and its height. -/
theorem eq_inl_mul_tpow (g : N ⋊[φ] Multiplicative ℤ) :
    g = inl g.left * tpow φ (Multiplicative.toAdd g.right) := by
  rw [tpow]
  simp

/-- **The transport identity.**  Undoing the label twisted to height `k` after
descending `k` levels is the same as descending `j` levels and undoing `g`,
whenever `k = j + q` with `q` the height of `g`. -/
theorem inv_tw_mul_tpow (g : N ⋊[φ] Multiplicative ℤ) (j k : ℤ)
    (hk : k = j + Multiplicative.toAdd g.right) :
    (inl (tw φ (-k) g.left))⁻¹ * tpow φ (-k) = tpow φ (-j) * g⁻¹ := by
  have haut : (inl (tw φ (-k) g.left) : N ⋊[φ] Multiplicative ℤ)
      = tpow φ (-k) * inl g.left * (tpow φ (-k))⁻¹ := by
    rw [tw, tpow, inl_aut, map_inv]
  have hlhs : (inl (tw φ (-k) g.left))⁻¹ * tpow φ (-k)
      = tpow φ (-k) * (inl g.left)⁻¹ := by
    rw [haut]
    group
  have hsum : -j + -Multiplicative.toAdd g.right = -k := by omega
  have hrhs : tpow φ (-j) * g⁻¹ = tpow φ (-k) * (inl g.left)⁻¹ := by
    conv_lhs => rw [eq_inl_mul_tpow φ g]
    rw [mul_inv_rev, ← mul_assoc, ← tpow_neg, ← tpow_add, hsum]
  rw [hlhs, hrhs]

/-! ## The cyclic extension theorem -/

variable [MulAction (N ⋊[φ] Multiplicative ℤ) X]

/-- Compatibility of the two actions: the normal part acts through `inl`. -/
def ActionCompatible : Prop :=
  ∀ (n : N) (x : X), (inl n : N ⋊[φ] Multiplicative ℤ) • x = n • x

variable {φ}

/-- **Theorem 12.1.**  Soficity of an action is stable under adjoining a
compatible cyclic normalizer. -/
theorem isSoficAction_semidirect [DecidableEq X]
    (hcompat : ActionCompatible φ (X := X))
    (hN : IsSoficAction N X) :
    IsSoficAction (N ⋊[φ] Multiplicative ℤ) X := by
  classical
  intro F E ε hε
  -- height bound over the tested set
  set Q : ℕ := F.sup (fun g => (Multiplicative.toAdd g.right).natAbs) with hQdef
  have hQ : ∀ g ∈ F, (Multiplicative.toAdd g.right).natAbs ≤ Q := by
    intro g hg
    rw [hQdef]
    exact Finset.le_sup (f := fun g => (Multiplicative.toAdd g.right).natAbs) hg
  -- choose the stack length
  obtain ⟨L₀, hL₀⟩ :=
    exists_nat_gt ((8 * ((Q : ℝ) + 1) * ((F.card : ℝ) + 1)) / ε)
  set L : ℕ := L₀ + 1 with hLdef
  haveI : NeZero L := ⟨by omega⟩
  have hLpos : 0 < L := Nat.succ_pos _
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hLbig : (8 * ((Q : ℝ) + 1) * ((F.card : ℝ) + 1)) / ε < (L : ℝ) := by
    refine lt_of_lt_of_le hL₀ ?_
    exact_mod_cast Nat.le_succ L₀
  have hkey : 8 * ((Q : ℝ) + 1) * ((F.card : ℝ) + 1) < ε * L := by
    rw [div_lt_iff₀ hε] at hLbig
    linarith [hLbig]
  have hδ : (0 : ℝ) < ε / 4 := by positivity
  -- the finite windows for the normal part
  set M : Finset N := (Finset.range L).biUnion
    (fun m => F.image (fun g => tw φ (-(m : ℤ)) g.left)) with hMdef
  have hMmem : ∀ (m : ℕ), m < L → ∀ g ∈ F, tw φ (-(m : ℤ)) g.left ∈ M := by
    intro m hm g hg
    rw [hMdef, Finset.mem_biUnion]
    exact ⟨m, Finset.mem_range.mpr hm, Finset.mem_image_of_mem _ hg⟩
  set E' : Finset X := (Finset.range L).biUnion
    (fun j => E.image (fun x => (tpow φ (-(j : ℤ))) • x)) with hE'def
  have hE'mem : ∀ (j : ℕ), j < L → ∀ x ∈ E, (tpow φ (-(j : ℤ))) • x ∈ E' := by
    intro j hj x hx
    rw [hE'def, Finset.mem_biUnion]
    exact ⟨j, Finset.mem_range.mpr hj, Finset.mem_image_of_mem _ hx⟩
  obtain ⟨M₀⟩ := hN M E' (ε / 4) hδ
  -- the good levels
  set badAll : Finset (ZMod L) :=
    F.biUnion (fun g => badLevels L (Multiplicative.toAdd g.right)) with hbadDef
  set J : Finset (ZMod L) := Finset.univ \ badAll with hJdef
  have hbadCard : (badAll.card : ℝ) ≤ 2 * (Q : ℝ) * (F.card : ℝ) := by
    have h1 : badAll.card ≤ ∑ g ∈ F, (badLevels L (Multiplicative.toAdd g.right)).card :=
      Finset.card_biUnion_le
    have h2 : ∀ g ∈ F, (badLevels L (Multiplicative.toAdd g.right)).card ≤ 2 * Q := by
      intro g hg
      exact le_trans (card_badLevels_le _) (by
        have := hQ g hg
        omega)
    have h3 : (∑ g ∈ F, (badLevels L (Multiplicative.toAdd g.right)).card)
        ≤ ∑ _g ∈ F, 2 * Q := Finset.sum_le_sum h2
    have h4 : (∑ _g ∈ F, 2 * Q) = F.card * (2 * Q) := by
      rw [Finset.sum_const, smul_eq_mul]
    have : badAll.card ≤ F.card * (2 * Q) := by omega
    calc (badAll.card : ℝ) ≤ ((F.card * (2 * Q) : ℕ) : ℝ) := by exact_mod_cast this
      _ = 2 * (Q : ℝ) * (F.card : ℝ) := by push_cast; ring
  have hJcard : (L : ℝ) - 2 * (Q : ℝ) * (F.card : ℝ) ≤ (J.card : ℝ) := by
    have hcard : Fintype.card (ZMod L) = L := ZMod.card L
    have hle : badAll.card ≤ L := by
      have hsub := Finset.card_le_card (Finset.subset_univ badAll)
      rw [Finset.card_univ, hcard] at hsub
      exact hsub
    have hsub : J.card = L - badAll.card := by
      rw [hJdef, Finset.card_univ_sdiff, hcard]
    have hJR : (J.card : ℝ) = (L : ℝ) - (badAll.card : ℝ) := by
      rw [hsub]
      exact Nat.cast_sub hle
    rw [hJR]
    linarith [hbadCard]
  refine ⟨{
    Site := ZMod L × M₀.Site
    siteFintype := inferInstance
    siteDecEq := inferInstance
    siteNonempty := ?_
    act := fun g => stackPerm L φ M₀.act g
    act_one := stackPerm_one L φ M₀.act M₀.act_one
    act_mul := ?_
    good := J ×ˢ M₀.good
    good_card := ?_
    Chart := M₀.Chart
    chartFintype := inferInstance
    chart := fun p x => M₀.chart p.2 ((tpow φ (-((p.1).val : ℤ))) • x)
    chart_inj := ?_
    chart_equivariant := ?_ }⟩
  · rw [Fintype.card_prod, ZMod.card]
    exact Nat.mul_pos hLpos M₀.siteNonempty
  · -- multiplicativity
    intro g hg h hh
    have hqQ : (Multiplicative.toAdd g.right).natAbs ≤ Q := hQ g hg
    have hsp : ∀ y : N ⋊[φ] Multiplicative ℤ,
        stackPerm L φ M₀.act y
          = twistedShift L (Multiplicative.toAdd y.right)
              (fun i => M₀.act (tw φ (-(i.val : ℤ)) y.left)) := fun _ => rfl
    rw [hsp (g * h), hsp g, hsp h, twistedShift_mul]
    have hrightmul : Multiplicative.toAdd (g * h).right
        = Multiplicative.toAdd g.right + Multiplicative.toAdd h.right := by
      rw [SemidirectProduct.mul_right, toAdd_mul]
    rw [hrightmul]
    refine le_trans (permDist_twistedShift_le L _ _ _
      (badLevels L (-(Multiplicative.toAdd g.right))) (ε / 4) hδ.le ?_ hLpos) ?_
    · -- off the boundary the two fibre labels multiply exactly
      intro k hk
      have hval : ((k + ((-(Multiplicative.toAdd g.right) : ℤ) : ZMod L)).val : ℤ)
          = (k.val : ℤ) + (-(Multiplicative.toAdd g.right)) :=
        val_add_of_not_bad hk
      have hsub : k - ((Multiplicative.toAdd g.right : ℤ) : ZMod L)
          = k + ((-(Multiplicative.toAdd g.right) : ℤ) : ZMod L) := by
        push_cast; ring
      have hlabel : tw φ (-((k.val : ℤ)))
            (g.left * (φ g.right) h.left)
          = tw φ (-((k.val : ℤ))) g.left *
            tw φ (-(((k - ((Multiplicative.toAdd g.right : ℤ) : ZMod L)).val : ℤ)))
              h.left := by
        rw [tw_mul]
        congr 1
        have hg' : (φ g.right) h.left
            = tw φ (Multiplicative.toAdd g.right) h.left := by
          rw [tw, ofAdd_toAdd]
        rw [hg', ← tw_add, hsub, hval]
        congr 1
        ring
      have hmemu : tw φ (-((k.val : ℤ))) g.left ∈ M :=
        hMmem k.val (ZMod.val_lt k) g hg
      have hmemv : tw φ
          (-(((k - ((Multiplicative.toAdd g.right : ℤ) : ZMod L)).val : ℤ)))
          h.left ∈ M :=
        hMmem _ (ZMod.val_lt _) h hh
      have hleftmul : (g * h).left = g.left * (φ g.right) h.left :=
        SemidirectProduct.mul_left g h
      rw [hleftmul, hlabel]
      exact M₀.act_mul _ hmemu _ hmemv
    · -- the boundary is small
      have hb : ((badLevels L (-(Multiplicative.toAdd g.right))).card : ℝ)
          ≤ 2 * (Q : ℝ) := by
        have := card_badLevels_le (L := L) (-(Multiplicative.toAdd g.right))
        have hnat : (badLevels L (-(Multiplicative.toAdd g.right))).card ≤ 2 * Q := by
          simp only [Int.natAbs_neg] at this
          omega
        exact_mod_cast hnat
      have hstep : ((badLevels L (-(Multiplicative.toAdd g.right))).card : ℝ) / L
          ≤ 2 * (Q : ℝ) / L := by
        exact div_le_div_of_nonneg_right hb hLR.le
      have hfrac : 2 * (Q : ℝ) / L ≤ ε / 4 := by
        rw [div_le_div_iff₀ hLR (by norm_num : (0:ℝ) < 4)]
        nlinarith [hkey, Nat.cast_nonneg (α := ℝ) Q, Nat.cast_nonneg (α := ℝ) F.card]
      have hsum : ((badLevels L (-(Multiplicative.toAdd g.right))).card : ℝ) / L
            + ε / 4 ≤ ε / 4 + ε / 4 := by
        linarith [le_trans hstep hfrac]
      linarith
  · -- density of the good set
    rw [Finset.card_product, Fintype.card_prod, ZMod.card]
    have hS0' : (1 - ε / 4) * (Fintype.card M₀.Site : ℝ) ≤ (M₀.good.card : ℝ) :=
      M₀.good_card
    have hA0 : (0 : ℝ) ≤ (Fintype.card M₀.Site : ℝ) := Nat.cast_nonneg _
    have hJnn : (0 : ℝ) ≤ (J.card : ℝ) := Nat.cast_nonneg _
    have hGnn : (0 : ℝ) ≤ (M₀.good.card : ℝ) := Nat.cast_nonneg _
    have hfrac : 2 * (Q : ℝ) * (F.card : ℝ) ≤ ε / 4 * L := by
      nlinarith [hkey, Nat.cast_nonneg (α := ℝ) Q, Nat.cast_nonneg (α := ℝ) F.card]
    have hJ' : (1 - ε / 4) * (L : ℝ) ≤ (J.card : ℝ) := by nlinarith [hJcard]
    push_cast
    by_cases hε1 : ε ≤ 1
    · have h1 : (0 : ℝ) ≤ 1 - ε / 4 := by linarith
      have hprod : ((1 - ε / 4) * (L : ℝ)) *
            ((1 - ε / 4) * (Fintype.card M₀.Site : ℝ))
          ≤ (J.card : ℝ) * (M₀.good.card : ℝ) :=
        mul_le_mul hJ' hS0' (by positivity) hJnn
      have hLS : (0 : ℝ) ≤ (L : ℝ) * (Fintype.card M₀.Site : ℝ) := by positivity
      have hcoef : (1 - ε) ≤ (1 - ε / 4) * (1 - ε / 4) := by nlinarith [hε]
      calc (1 - ε) * ((L : ℝ) * (Fintype.card M₀.Site : ℝ))
          ≤ ((1 - ε / 4) * (1 - ε / 4)) *
              ((L : ℝ) * (Fintype.card M₀.Site : ℝ)) :=
            mul_le_mul_of_nonneg_right hcoef hLS
        _ = (1 - ε / 4) * (L : ℝ) *
              ((1 - ε / 4) * (Fintype.card M₀.Site : ℝ)) := by ring
        _ ≤ (J.card : ℝ) * (M₀.good.card : ℝ) := hprod
    · have hε1' : 1 < ε := lt_of_not_ge hε1
      have hLS : (0 : ℝ) ≤ (L : ℝ) * (Fintype.card M₀.Site : ℝ) := by positivity
      nlinarith [hLS, mul_nonneg hJnn hGnn,
        mul_nonneg (by linarith : (0 : ℝ) ≤ ε - 1) hLS]
  · -- charts are injective on the window
    intro s hs x hx y hy hxy
    rw [Finset.mem_product] at hs
    have hjlt : (s.1).val < L := ZMod.val_lt _
    have hxE' := hE'mem (s.1).val hjlt x hx
    have hyE' := hE'mem (s.1).val hjlt y hy
    have := M₀.chart_inj s.2 hs.2 _ hxE' _ hyE' hxy
    exact smul_left_cancel _ this
  · -- orbit covariance
    intro g hg s hs hgs x hx hgx
    rw [Finset.mem_product] at hs hgs
    set j : ZMod L := s.1 with hj
    set a : M₀.Site := s.2 with ha
    set q : ℤ := Multiplicative.toAdd g.right with hq
    have hjgood : j ∉ badAll := by
      have := hs.1
      rw [hJdef, Finset.mem_sdiff] at this
      exact this.2
    have hjbad : j ∉ badLevels L q := by
      intro hcon
      exact hjgood (Finset.mem_biUnion.mpr ⟨g, hg, hcon⟩)
    have hval : ((j + (q : ZMod L)).val : ℤ) = (j.val : ℤ) + q :=
      val_add_of_not_bad hjbad
    set k : ZMod L := j + (q : ZMod L) with hk
    set u : N := tw φ (-((k.val : ℤ))) g.left with hu
    have humem : u ∈ M := hMmem k.val (ZMod.val_lt k) g hg
    have hfst : (stackPerm L φ M₀.act g s).1 = k := rfl
    have hsnd : (stackPerm L φ M₀.act g s).2 = M₀.act u a := rfl
    have hyE' : (tpow φ (-((k.val : ℤ)))) • x ∈ E' :=
      hE'mem k.val (ZMod.val_lt k) x hx
    have htrans : u⁻¹ • ((tpow φ (-((k.val : ℤ)))) • x)
        = (tpow φ (-((j.val : ℤ)))) • (g⁻¹ • x) := by
      have hid := inv_tw_mul_tpow φ g (j.val : ℤ) (k.val : ℤ) (by rw [hval, hq])
      have hle : (inl u⁻¹ : N ⋊[φ] Multiplicative ℤ) • ((tpow φ (-((k.val : ℤ)))) • x)
          = ((inl u)⁻¹ * tpow φ (-((k.val : ℤ)))) • x := by
        rw [mul_smul, map_inv]
      rw [← hcompat u⁻¹, hle, hid, mul_smul]
    have hgxE' : u⁻¹ • ((tpow φ (-((k.val : ℤ)))) • x) ∈ E' := by
      rw [htrans]
      exact hE'mem (j.val) (ZMod.val_lt j) _ hgx
    have hgood2 : M₀.act u a ∈ M₀.good := by
      have hg2 := hgs.2
      rw [hsnd] at hg2
      exact hg2
    have hcov := M₀.chart_equivariant u humem a hs.2 hgood2 _ hyE' hgxE'
    show M₀.chart (stackPerm L φ M₀.act g s).2
        ((tpow φ (-(((stackPerm L φ M₀.act g s).1).val : ℤ))) • x)
        = M₀.chart s.2 ((tpow φ (-((s.1).val : ℤ))) • (g⁻¹ • x))
    rw [hfst, hsnd, ← hj, ← ha, hcov, htrans]

end CyclicStack
end GroupApproximation

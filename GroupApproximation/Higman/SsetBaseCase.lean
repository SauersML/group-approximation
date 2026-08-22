import GroupApproximation.Higman.ClosuresAssembly

/-!
# Higman's base case `S`

`Higman.BaseCases` proves the first of Higman's two base cases, `Z = {0}`, and
records that the second,

    S = {(n, n+1) : n ∈ ℤ} ,

is not immediate.  This file proves it, and it costs nothing beyond the group
`Higman.FlipGroup` already builds for the operation `ρ`.

## The one line the base case rests on

Write `rᵢ = c⁻ⁱ b cⁱ` for the row elements of `F₃` and `bₙ` for the conjugator
of the `n`-th sequence of `S`.  The sequence `succSeq n` is supported inside
the window `[0, 2)`, so `Seq.elt_window` reads its coding straight off the two
window coordinates:

    bₙ = r₀ⁿ r₁ⁿ⁺¹        (`bElt_succSeq`),

and therefore

    r₀ · bₙ · r₁ = r₀ⁿ⁺¹ r₁ⁿ⁺² = bₙ₊₁        (`shift_bElt_succSeq`).

So the index family of `S` is the orbit of a **two-sided translation** of the
index set `K`: multiply on the left by `r₀` and on the right by `r₁`.  Nothing
about `S` is sensitive to the order of the coding, and no machine is
simulated.  This is what makes `S` cheap and what makes it useless as a
template: `τ`'s index map is neither a translation nor an inversion.

## Why that is free

`Higman.FlipGroup` builds

    G₂ = F₃ ⋊_ψ K = N ⋊ (K × K) ,

finitely presented (`Flip.isFinitelyPresented_G₂`) and torsion-free
(`Flip.torsionFree_G₂`), in which *both* translations of the index of a basis
element `a ^ w` of the normal closure of `a` are realized by conjugation:

* on the right by `emb v⁻¹`, because `emb` is a homomorphism;
* on the left by `f0 u` for `u ∈ K`, which is `Flip.conj_left` together with
  `Flip.conj_f0_emb` --- the two commuting copies of `K` are exactly what the
  flip needed, and the left copy is what is used here.

So the whole group of two-sided translations `w ↦ u w v` is realized inside
`G₂` (`conj_f0_conj`), and

    succShift = f0 r₀ · (emb r₁)⁻¹

conjugates `a_{(n, n+1)}` to `a_{(n+1, n+2)}` (`conj_succShift_aElt`).  `G₂`
was built for `ρ`; it pays for `S` as well, at no extra cost.

The rest is Higman's collecting process, transcribed from
`Higman.Row.comap_Lsub`: the subgroup `L = ⟨a_{(0,1)}, s⟩` is two-generated,
every element of it is a member of `A_S` times a power of `s`
(`LSubS_le_normalSubS`), and a stable-letter grading kills `F₃` while counting
`s`.  The grading is the one new gadget: `G₂` is an HNN extension of `G₁`
along the copy of `F₃`, on which the first stage's grading
`HNNTorsionFree.lengthHom psiBTop` is constant, so that grading lifts to `G₂`
with stable letter `1`.  It counts `β`, and `succShift` contains exactly one
`β` because `r₀ = b` and `f0 b = β`.

## Relation to the sources

Both Higman and Mikaelian prove this base case on the `d`-side, inside
`⟨a, d, e⟩`, where the apparatus of their Section 4 is available.  The route
here is `F₃`-native and uses no apparatus; it works because `S`'s index family
is a translation orbit, which is special to `S` and does **not** generalize to
the other operations.  The costing behind the route is
`notes/W6_TAU_BASE_S_PRICING_2026-08-22.md`.  `Higman.BaseCases`' own docstring
predicted a "two-stable-letter extension whose base is `F₃`"; `G₂` is one, and
it was already built.

The payoff at the assembly level is `operationClosures_of_five_inputs` at the
end of this file: `Higman.ClosuresAssembly.operationClosures_of_inputs` takes
six inputs, and `hbase` is no longer one of them.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Flip

/-! ## 1.  The coding of Higman's `S` -/

theorem mem_Sset_iff {f : E} : f ∈ Sset ↔ ∃ n : ℤ, succSeq n = f := Set.mem_range

/-- The coordinates of the `n`-th sequence of `S`, read off the two
singletons it is built from. -/
theorem succSeq_apply (n i : ℤ) :
    succSeq n i
      = (if (0 : ℤ) = i then n else 0) + (if (1 : ℤ) = i then n + 1 else 0) := by
  have hs0 : (Finsupp.single (0 : ℤ) n) i = if (0 : ℤ) = i then n else 0 :=
    Finsupp.single_apply
  have hs1 : (Finsupp.single (1 : ℤ) (n + 1)) i = if (1 : ℤ) = i then n + 1 else 0 :=
    Finsupp.single_apply
  unfold succSeq
  rw [Finsupp.add_apply, hs0, hs1]

theorem succSeq_apply_zero (n : ℤ) : succSeq n 0 = n := by
  rw [succSeq_apply, if_pos (rfl : (0 : ℤ) = 0),
    if_neg (by omega : ¬ (1 : ℤ) = (0 : ℤ)), add_zero]

theorem succSeq_apply_one (n : ℤ) : succSeq n 1 = n + 1 := by
  rw [succSeq_apply, if_neg (by omega : ¬ (0 : ℤ) = (1 : ℤ)),
    if_pos (rfl : (1 : ℤ) = 1), zero_add]

theorem succSeq_apply_of_ne (n : ℤ) {i : ℤ} (h0 : i ≠ 0) (h1 : i ≠ 1) :
    succSeq n i = 0 := by
  rw [succSeq_apply, if_neg (Ne.symm h0), if_neg (Ne.symm h1), add_zero]

theorem lowPart_succSeq (n : ℤ) : lowPart (succSeq n) = 0 := by
  refine Finsupp.ext fun i => ?_
  unfold lowPart
  rw [Finsupp.filter_apply, Finsupp.zero_apply]
  by_cases h : i < 0
  · rw [if_pos h]
    exact succSeq_apply_of_ne n (by omega) (by omega)
  · rw [if_neg h]

theorem highPart_succSeq (n : ℤ) : highPart (succSeq n) = 0 := by
  refine Finsupp.ext fun i => ?_
  unfold highPart
  rw [Finsupp.filter_apply, Finsupp.zero_apply]
  by_cases h : (2 : ℤ) ≤ i
  · rw [if_pos h]
    exact succSeq_apply_of_ne n (by omega) (by omega)
  · rw [if_neg h]

/-- **The coding of the `n`-th sequence of `S`, in the free group on `ℤ`.**
The sequence is supported inside the window `[0, 2)`, so `Seq.elt_window`
collapses to its two window coordinates. -/
theorem elt_succSeq (n : ℤ) :
    elt (succSeq n) = FreeGroup.of (0 : ℤ) ^ n * FreeGroup.of (1 : ℤ) ^ (n + 1) := by
  rw [elt_window (succSeq n), lowPart_succSeq, highPart_succSeq, elt_zero,
    succSeq_apply_zero, succSeq_apply_one, one_mul, mul_one]

/-- **The conjugator of the `n`-th sequence of `S`.** -/
theorem bElt_succSeq (n : ℤ) :
    bElt (succSeq n) = rowElt 0 ^ n * rowElt 1 ^ (n + 1) := by
  unfold bElt
  rw [elt_succSeq, map_mul, map_zpow, map_zpow, rowHom_of, rowHom_of]

/-- **The one line the whole base case rests on.**  The index family of `S` is
the orbit of a two-sided translation: left by `r₀`, right by `r₁`. -/
theorem shift_bElt_succSeq (n : ℤ) :
    rowElt 0 * (bElt (succSeq n) * rowElt 1) = bElt (succSeq (n + 1)) := by
  have hx : rowElt 0 ^ (n + 1) = rowElt 0 * rowElt 0 ^ n := by
    rw [add_comm n 1, zpow_add, zpow_one]
  have hy : rowElt 1 ^ (n + 1 + 1) = rowElt 1 ^ (n + 1) * rowElt 1 := by
    rw [zpow_add, zpow_one]
  rw [bElt_succSeq, bElt_succSeq, hx, hy]
  group

/-! ## 2.  The two-sided translation, realized in `G₂` -/

/-- **Left translation of the index.**  The left-acting copy of `K` inside
`G₂` conjugates `a ^ v` to `a ^ (u v)`.  This is `Flip.conj_left` for the
generator and `Flip.conj_f0_emb` for the conjugator. -/
theorem conj_f0_conj (u : F₃) (hu : u ∈ K) (v : F₃) (hv : v ∈ K) :
    f0 u * emb (v⁻¹ * a * v) * (f0 u)⁻¹ = emb ((u * v)⁻¹ * a * (u * v)) := by
  calc f0 u * emb (v⁻¹ * a * v) * (f0 u)⁻¹
      = (f0 u * emb v⁻¹ * (f0 u)⁻¹) * (f0 u * emb a * (f0 u)⁻¹)
          * (f0 u * emb v * (f0 u)⁻¹) := by
        rw [map_mul emb, map_mul emb]
        group
    _ = emb v⁻¹ * emb (u⁻¹ * a * u) * emb v := by
        rw [conj_f0_emb u hu v⁻¹ (Subgroup.inv_mem K hv), conj_left u hu,
          conj_f0_emb u hu v hv]
    _ = emb ((u * v)⁻¹ * a * (u * v)) := by
        rw [← map_mul emb, ← map_mul emb]
        congr 1
        group

/-- The element of `G₂` that shifts Higman's `S` along. -/
noncomputable def succShift : G₂ := f0 (rowElt 0) * (emb (rowElt 1))⁻¹

/-- **What conjugation by it does to the index.**  Right translation is
`emb`'s multiplicativity; left translation is `conj_f0_conj`. -/
theorem conj_succShift (v : F₃) (hv : v ∈ K) :
    succShift * emb (v⁻¹ * a * v) * succShift⁻¹
      = emb ((rowElt 0 * (v * rowElt 1))⁻¹ * a * (rowElt 0 * (v * rowElt 1))) := by
  have hstep : (emb (rowElt 1))⁻¹ * emb (v⁻¹ * a * v) * emb (rowElt 1)
      = emb ((v * rowElt 1)⁻¹ * a * (v * rowElt 1)) := by
    rw [← map_inv emb, ← map_mul emb, ← map_mul emb]
    congr 1
    group
  unfold succShift
  calc f0 (rowElt 0) * (emb (rowElt 1))⁻¹ * emb (v⁻¹ * a * v)
        * (f0 (rowElt 0) * (emb (rowElt 1))⁻¹)⁻¹
      = f0 (rowElt 0) * ((emb (rowElt 1))⁻¹ * emb (v⁻¹ * a * v) * emb (rowElt 1))
          * (f0 (rowElt 0))⁻¹ := by group
    _ = f0 (rowElt 0) * emb ((v * rowElt 1)⁻¹ * a * (v * rowElt 1))
          * (f0 (rowElt 0))⁻¹ := by rw [hstep]
    _ = emb ((rowElt 0 * (v * rowElt 1))⁻¹ * a * (rowElt 0 * (v * rowElt 1))) :=
        conj_f0_conj (rowElt 0) (rowElt_mem_K 0) (v * rowElt 1)
          (Subgroup.mul_mem K hv (rowElt_mem_K 1))

/-- **The shift, on the generators of `A_S`.** -/
theorem conj_succShift_aElt (n : ℤ) :
    succShift * emb (aElt (succSeq n)) * succShift⁻¹
      = emb (aElt (succSeq (n + 1))) := by
  unfold aElt
  rw [conj_succShift (bElt (succSeq n)) (bElt_mem_K _), shift_bElt_succSeq]

/-- ... and the other way round. -/
theorem conj_succShift_inv_aElt (n : ℤ) :
    succShift⁻¹ * emb (aElt (succSeq n)) * succShift
      = emb (aElt (succSeq (n - 1))) := by
  have hn : n - 1 + 1 = n := by ring
  have h := conj_succShift_aElt (n - 1)
  rw [hn] at h
  rw [← h]
  group

/-! ## 3.  The collecting process -/

/-- The image of `A_S` in the ambient group. -/
noncomputable def MSubS : Subgroup G₂ := (ASub Sset).map emb

theorem aElt_succSeq_mem_ASub (n : ℤ) : aElt (succSeq n) ∈ ASub Sset :=
  Subgroup.subset_closure ⟨succSeq n, ⟨n, rfl⟩, rfl⟩

theorem emb_aElt_succSeq_mem_MSubS (n : ℤ) : emb (aElt (succSeq n)) ∈ MSubS :=
  Subgroup.mem_map.mpr ⟨aElt (succSeq n), aElt_succSeq_mem_ASub n, rfl⟩

/-- The generating set of `A_S`, named. -/
theorem mem_aElt_image_Sset {z : F₃} (hz : z ∈ aElt '' Sset) :
    ∃ n : ℤ, z = aElt (succSeq n) := by
  obtain ⟨f, hf, hfz⟩ := hz
  obtain ⟨n, hn⟩ := mem_Sset_iff.mp hf
  exact ⟨n, by rw [← hfz, hn]⟩

theorem conj_succShift_MSubS {x : G₂} (hx : x ∈ MSubS) :
    succShift * x * succShift⁻¹ ∈ MSubS := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.closure_induction
    (p := fun z _ => succShift * emb z * succShift⁻¹ ∈ MSubS) ?_ ?_ ?_ ?_ hy
  · intro z hz
    obtain ⟨n, rfl⟩ := mem_aElt_image_Sset hz
    rw [conj_succShift_aElt]
    exact emb_aElt_succSeq_mem_MSubS (n + 1)
  · rw [map_one, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · intro u v _ _ hu hv
    have hsplit : succShift * emb (u * v) * succShift⁻¹
        = (succShift * emb u * succShift⁻¹) * (succShift * emb v * succShift⁻¹) := by
      rw [map_mul]
      group
    rw [hsplit]
    exact Subgroup.mul_mem _ hu hv
  · intro u _ hu
    have hsplit : succShift * emb u⁻¹ * succShift⁻¹
        = (succShift * emb u * succShift⁻¹)⁻¹ := by
      rw [map_inv]
      group
    rw [hsplit]
    exact Subgroup.inv_mem _ hu

theorem conj_succShift_inv_MSubS {x : G₂} (hx : x ∈ MSubS) :
    succShift⁻¹ * x * succShift ∈ MSubS := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.closure_induction
    (p := fun z _ => succShift⁻¹ * emb z * succShift ∈ MSubS) ?_ ?_ ?_ ?_ hy
  · intro z hz
    obtain ⟨n, rfl⟩ := mem_aElt_image_Sset hz
    rw [conj_succShift_inv_aElt]
    exact emb_aElt_succSeq_mem_MSubS (n - 1)
  · rw [map_one, mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  · intro u v _ _ hu hv
    have hsplit : succShift⁻¹ * emb (u * v) * succShift
        = (succShift⁻¹ * emb u * succShift) * (succShift⁻¹ * emb v * succShift) := by
      rw [map_mul]
      group
    rw [hsplit]
    exact Subgroup.mul_mem _ hu hv
  · intro u _ hu
    have hsplit : succShift⁻¹ * emb u⁻¹ * succShift
        = (succShift⁻¹ * emb u * succShift)⁻¹ := by
      rw [map_inv]
      group
    rw [hsplit]
    exact Subgroup.inv_mem _ hu

theorem conj_zpow_MSubS (k : ℤ) {x : G₂} (hx : x ∈ MSubS) :
    succShift ^ k * x * (succShift ^ k)⁻¹ ∈ MSubS := by
  induction k using Int.induction_on with
  | zero =>
      rw [zpow_zero, one_mul, inv_one, mul_one]
      exact hx
  | succ m ih =>
      have hstep : succShift ^ ((m : ℤ) + 1) * x * (succShift ^ ((m : ℤ) + 1))⁻¹
          = succShift * (succShift ^ (m : ℤ) * x * (succShift ^ (m : ℤ))⁻¹)
              * succShift⁻¹ := by
        rw [zpow_add, zpow_one]
        group
      rw [hstep]
      exact conj_succShift_MSubS ih
  | pred m ih =>
      have hstep : succShift ^ (-(m : ℤ) - 1) * x * (succShift ^ (-(m : ℤ) - 1))⁻¹
          = succShift⁻¹ * (succShift ^ (-(m : ℤ)) * x * (succShift ^ (-(m : ℤ)))⁻¹)
              * succShift := by
        rw [zpow_sub, zpow_one]
        group
      rw [hstep]
      exact conj_succShift_inv_MSubS ih

/-- Elements of the shape "member of `A_S`, times a power of the shift".  This
is where the collecting happens: the set is a subgroup because `A_S` is
normalized by the shift. -/
noncomputable def NormalSubS : Subgroup G₂ where
  carrier := {w : G₂ | ∃ u ∈ MSubS, ∃ k : ℤ, w = u * succShift ^ k}
  one_mem' := by
    refine ⟨1, Subgroup.one_mem _, 0, ?_⟩
    rw [zpow_zero, mul_one]
  mul_mem' := by
    rintro x y ⟨u, hu, k, rfl⟩ ⟨v, hv, m, rfl⟩
    refine ⟨u * (succShift ^ k * v * (succShift ^ k)⁻¹),
      Subgroup.mul_mem _ hu (conj_zpow_MSubS k hv), k + m, ?_⟩
    rw [zpow_add]
    group
  inv_mem' := by
    rintro x ⟨u, hu, k, rfl⟩
    refine ⟨succShift ^ (-k) * u⁻¹ * (succShift ^ (-k))⁻¹,
      conj_zpow_MSubS (-k) (Subgroup.inv_mem _ hu), -k, ?_⟩
    group

/-- The two-generated subgroup that cuts `A_S` out. -/
noncomputable def LSubS : Subgroup G₂ :=
  Subgroup.closure {emb (aElt (succSeq 0)), succShift}

theorem LSubS_fg : LSubS.FG := by
  refine (Subgroup.fg_iff _).mpr ⟨{emb (aElt (succSeq 0)), succShift}, rfl, ?_⟩
  exact (Set.finite_singleton _).insert _

theorem LSubS_le_normalSubS : LSubS ≤ NormalSubS := by
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rcases hx with rfl | hx
  · refine ⟨emb (aElt (succSeq 0)), emb_aElt_succSeq_mem_MSubS 0, 0, ?_⟩
    rw [zpow_zero, mul_one]
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨1, Subgroup.one_mem _, 1, ?_⟩
    rw [zpow_one, one_mul]

/-! ## 4.  The stable-letter grading of `G₂` that counts the shift

`G₂` is an HNN extension of `G₁` whose associated subgroup is the copy of `F₃`,
and the first stage's grading is constant on that copy.  So it lifts, with the
second stable letter sent to `1`.  What comes out counts the *first* stable
letter, which is the one `succShift` contains. -/

theorem lenS_lift (y : ↥Acopy) :
    (1 : Multiplicative ℤ) * HNNTorsionFree.lengthHom psiBTop (y : G₁)
      = HNNTorsionFree.lengthHom psiBTop ((psiCA y : ↥Acopy) : G₁) * 1 := by
  obtain ⟨z, hz⟩ := y.2
  have hy : (y : G₁) = HNNExtension.of z := hz.symm
  have hyz : y = embA z := Subtype.ext (by rw [hy, coe_embA])
  rw [hyz, psiCA_embA, coe_embA, coe_embA, HNNTorsionFree.lengthHom_of,
    HNNTorsionFree.lengthHom_of]

/-- The grading. -/
noncomputable def lenS : G₂ →* Multiplicative ℤ :=
  HNNExtension.lift (HNNTorsionFree.lengthHom psiBTop) 1 lenS_lift

theorem lenS_of (y : G₁) :
    lenS (HNNExtension.of y) = HNNTorsionFree.lengthHom psiBTop y :=
  HNNExtension.lift_of _ _ _ _

theorem lenS_emb (x : F₃) : lenS (emb x) = 1 := by
  unfold emb
  show lenS (HNNExtension.of (HNNExtension.of x)) = 1
  rw [lenS_of, HNNTorsionFree.lengthHom_of]

theorem lenS_succShift : lenS succShift = Multiplicative.ofAdd (1 : ℤ) := by
  have hb : f0 (rowElt 0) = beta := by rw [Omega.rowElt_zero, f0_b]
  unfold succShift
  rw [map_mul, map_inv, lenS_emb, inv_one, mul_one, hb]
  unfold beta
  rw [lenS_of, HNNTorsionFree.lengthHom_t]

theorem lenS_zpow (k : ℤ) : lenS (succShift ^ k) = Multiplicative.ofAdd k := by
  rw [map_zpow, lenS_succShift, ← ofAdd_zsmul]
  congr 1
  simp

/-! ## 5.  The intersection -/

theorem emb_aElt_succSeq_mem_LSubS (n : ℤ) : emb (aElt (succSeq n)) ∈ LSubS := by
  have hs : succShift ∈ LSubS :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  induction n using Int.induction_on with
  | zero => exact Subgroup.subset_closure (Set.mem_insert _ _)
  | succ m ih =>
      rw [← conj_succShift_aElt (m : ℤ)]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs ih) (Subgroup.inv_mem _ hs)
  | pred m ih =>
      rw [← conj_succShift_inv_aElt (-(m : ℤ))]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) ih) hs

/-- **`A_S` is exactly what `L` cuts out of `F₃`.**  One inclusion is the
translation orbit; the other is the collecting process plus the grading. -/
theorem comap_LSubS : LSubS.comap emb = ASub Sset := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' : emb x ∈ LSubS := Subgroup.mem_comap.mp hx
    obtain ⟨u, hu, k, hk⟩ := LSubS_le_normalSubS hx'
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hu
    have hlen := congrArg lenS hk
    rw [lenS_emb, map_mul, lenS_emb, lenS_zpow, one_mul] at hlen
    have hk0 : k = 0 := by
      have h3 := congrArg Multiplicative.toAdd hlen
      simpa using h3.symm
    rw [hk0, zpow_zero, mul_one] at hk
    have hxy : x = y := emb_injective hk
    rw [hxy]
    exact hy
  · intro x hx
    refine Subgroup.mem_comap.mpr ?_
    refine Subgroup.closure_induction (p := fun z _ => emb z ∈ LSubS) ?_ ?_ ?_ ?_ hx
    · intro z hz
      obtain ⟨n, rfl⟩ := mem_aElt_image_Sset hz
      exact emb_aElt_succSeq_mem_LSubS n
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro u v _ _ hu hv
      rw [map_mul]
      exact Subgroup.mul_mem _ hu hv
    · intro u _ hu
      rw [map_inv]
      exact Subgroup.inv_mem _ hu

/-! ## 6.  The witness -/

/-- The benign witness for `A_S`: the flip group, cut by two generators. -/
noncomputable def sWitness : BenignWitness (ASub Sset) where
  K := G₂
  fp := isFinitelyPresented_G₂
  emb := Flip.emb
  emb_injective := Flip.emb_injective
  L := LSubS
  L_fg := LSubS_fg
  comap_eq := comap_LSubS

/-- ... and it is torsion-free, because `G₂` is. -/
noncomputable def sTorsionFreeWitness : TorsionFreeBenignWitness (ASub Sset) where
  witness := sWitness
  torsionFree := torsionFree_G₂

/-- **Higman's base case `S`.**  `A_S = F₃ ∩ ⟨a_{(0,1)}, s⟩` inside the flip
group, with `s` the two-sided translation `r₀ · − · r₁` of the index. -/
theorem benignTF_ASub_Sset : BenignTF (ASub Sset) := ⟨sTorsionFreeWitness⟩

theorem benign_ASub_Sset : Benign (ASub Sset) := benignTF_ASub_Sset.toBenign

end Seq

/-! ## 7.  What this removes from the assembly -/

/-- **`OperationClosures` from five inputs.**

`Higman.ClosuresAssembly.operationClosures_of_inputs` takes six; `hbase` is
`Seq.benignTF_ASub_Sset` and is no longer one of them.  What is left is
`Omega.OmegaInput`, the `τ` closure, and the three benign rows. -/
theorem operationClosures_of_five_inputs (k : Omega.OmegaInput)
    (htau : ∀ B : Set Seq.E, BenignTF (Seq.ASub B) →
      BenignTF (Seq.ASub (Seq.tauOp B)))
    (hhalf : BenignTF (Agree.rowSub Agree.piV))
    (hzetaRow : BenignTF (Agree.rowSub Agree.zetaV))
    (hevenRow : BenignTF (Agree.rowSub (MonoidHom.ker (Split.killOn Seq.evenIdx)))) :
    OperationClosures :=
  operationClosures_of_inputs k htau Seq.benignTF_ASub_Sset hhalf hzetaRow hevenRow

end Higman
end GroupApproximation

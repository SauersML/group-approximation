import GroupApproximation.Higman.OperationClosureTheta

/-!
# Higman's operation `τ`, the coding at a cut, and what `τ` reduces to

`τ B = {f | ∃ g ∈ B, f 0 = g 1 ∧ f 1 = g 0 ∧ ∀ i ∉ {0, 1}, f i = g i}` ---
transpose the first two coordinates.

`τ` is the operation of the six that is furthest from an endomorphism of
`F₃`, and it is worth saying exactly why, because the reason is not the one
`ρ` fails for.  The transposition `i ↦ (0 1) i` is *not* order-preserving, but
`0` and `1` are adjacent, so nothing outside the window `[0, 2)` moves and the
sorted support is disturbed only inside it.  What comes out (`bElt_tauSeq`) is

    b_f      = X · r₀^{f 0} r₁^{f 1} · Y
    b_{τ f}  = X · r₀^{f 1} r₁^{f 0} · Y

with the *same* `X` and `Y`.  The two middles have the same letters and the
same exponents; only the order of the two syllables differs.  No endomorphism
of `F₃` does that: an endomorphism fixing the rows outside the window and
exchanging `r₀` with `r₁` would send `r₀^p r₁^q` to `r₁^p r₀^q`, which
exchanges the letters and keeps the *positions* --- the opposite of what is
wanted --- and no endomorphism transposes two adjacent syllables of a free
group.

So `τ`, like `ρ`, is a case of `benignTF_of_conj`: an element of an enlarged
finitely presented ambient group whose conjugation action realizes the
transposition on the coding.  `SwapWitness` is that input and
`benignTF_ASub_tauOp_of_swap` is the proof that it closes `τ`.  Unlike the
`FlipWitness` of `Higman.OperationClosureRho`, no construction of a
`SwapWitness` is offered here: the permutation of the free basis
`{a^w : w ∈ K}` that a swap has to induce is the identity off the set of
sorted normal forms, which is not the restriction of anything the row
calculus produces.  That is the honest state of `τ`.

## What is proved here, and is reusable

Sections 1 and 2 are not about `τ`.  They are the statement that the coding is
multiplicative across a cut,

    elt (u + v) = elt u * elt v      when supp u lies below supp v,

together with `elt (single i m) = (of i)^m`.  Every Higman operation that
touches a set of coordinates and leaves the rest alone --- `ζ` (free the
coordinate `0`), `π` (free the positive coordinates), `ωₘ` (blocks), and the
`κ` of `Higman.OperationClosureTheta` --- needs exactly this, and none of them
can be stated without it.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

open GroupApproximation.Higman.Conj

/-! ## 1.  The coding of a one-point sequence -/

theorem elt_single (i m : ℤ) : elt (Finsupp.single i m) = FreeGroup.of i ^ m := by
  by_cases hm : m = 0
  · rw [hm, Finsupp.single_zero, elt_zero, zpow_zero]
  · unfold elt
    rw [Finsupp.support_single i hm, Finset.sort_singleton, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, Finsupp.single_eq_same]

/-! ## 2.  The coding splits at a cut -/

/-- **The coding is multiplicative across a cut.**  If every index in the
support of `u` is below every index in the support of `v`, then the sorted
product that defines `elt (u + v)` is the concatenation of the two sorted
products, because a sorted list is determined by its multiset. -/
theorem elt_add_of_lt {u v : E} (h : ∀ i ∈ u.support, ∀ j ∈ v.support, i < j) :
    elt (u + v) = elt u * elt v := by
  have hdisj : Disjoint u.support v.support := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    exact absurd (h i hi i hi') (lt_irrefl i)
  have hsort : (u + v).support.sort (· ≤ ·)
      = u.support.sort (· ≤ ·) ++ v.support.sort (· ≤ ·) := by
    rw [Finsupp.support_add_eq hdisj]
    refine List.Perm.eq_of_sortedLE
      (List.Pairwise.sortedLE (Finset.pairwise_sort _ _)) ?_ ?_
    · refine List.Pairwise.sortedLE ?_
      rw [List.pairwise_append]
      refine ⟨Finset.pairwise_sort _ _, Finset.pairwise_sort _ _, fun i hi j hj => ?_⟩
      exact le_of_lt (h i (by simpa using hi) j (by simpa using hj))
    · rw [← Multiset.coe_eq_coe]
      have hcoe : ((u.support.sort (· ≤ ·) ++ v.support.sort (· ≤ ·) : List ℤ) : Multiset ℤ)
          = ((u.support.sort (· ≤ ·) : List ℤ) : Multiset ℤ)
            + ((v.support.sort (· ≤ ·) : List ℤ) : Multiset ℤ) := rfl
      rw [hcoe, Finset.sort_eq, Finset.sort_eq, Finset.sort_eq,
        ← Finset.disjUnion_eq_union u.support v.support hdisj]
      rfl
  unfold elt
  rw [hsort, List.map_append, List.prod_append]
  congr 1
  · refine congrArg List.prod (List.map_congr_left fun j hj => ?_)
    have hju : j ∈ u.support := by simpa using hj
    have hjv : v j = 0 :=
      Finsupp.notMem_support_iff.mp fun hc => absurd (h j hju j hc) (lt_irrefl j)
    rw [Finsupp.add_apply, hjv, add_zero]
  · refine congrArg List.prod (List.map_congr_left fun j hj => ?_)
    have hjv : j ∈ v.support := by simpa using hj
    have hju : u j = 0 :=
      Finsupp.notMem_support_iff.mp fun hc => absurd (h j hc j hjv) (lt_irrefl j)
    rw [Finsupp.add_apply, hju, zero_add]

/-! ## 3.  The window -/

/-- The part of a sequence below the window `[0, 2)`. -/
noncomputable def lowPart (f : E) : E := f.filter (fun i => i < 0)

/-- The part of a sequence above the window `[0, 2)`. -/
noncomputable def highPart (f : E) : E := f.filter (fun i => 2 ≤ i)

theorem lowPart_lt {f : E} {i : ℤ} (hi : i ∈ (lowPart f).support) : i < 0 := by
  unfold lowPart at hi
  rw [Finsupp.support_filter, Finset.mem_filter] at hi
  exact hi.2

theorem highPart_le {f : E} {i : ℤ} (hi : i ∈ (highPart f).support) : 2 ≤ i := by
  unfold highPart at hi
  rw [Finsupp.support_filter, Finset.mem_filter] at hi
  exact hi.2

theorem single_support_eq {a b i : ℤ} (hi : i ∈ (Finsupp.single a b).support) : i = a :=
  Finset.mem_singleton.mp (Finsupp.support_single_subset hi)

theorem support_add_bound {u v : E} {P : ℤ → Prop} (hu : ∀ i ∈ u.support, P i)
    (hv : ∀ i ∈ v.support, P i) : ∀ i ∈ (u + v).support, P i := by
  intro i hi
  rcases Finset.mem_union.mp (Finsupp.support_add hi) with hc | hc
  · exact hu i hc
  · exact hv i hc

/-- **The window decomposition.**  A sequence is its part below the window,
plus its two window coordinates, plus its part above. -/
theorem window_decomp (f : E) :
    f = lowPart f + (Finsupp.single (0 : ℤ) (f 0) +
      (Finsupp.single (1 : ℤ) (f 1) + highPart f)) := by
  refine Finsupp.ext fun i => ?_
  have hl : lowPart f i = if i < 0 then f i else 0 := Finsupp.filter_apply _ _ _
  have hh : highPart f i = if 2 ≤ i then f i else 0 := Finsupp.filter_apply _ _ _
  have hs0 : (Finsupp.single (0 : ℤ) (f 0)) i = if (0 : ℤ) = i then f 0 else 0 :=
    Finsupp.single_apply
  have hs1 : (Finsupp.single (1 : ℤ) (f 1)) i = if (1 : ℤ) = i then f 1 else 0 :=
    Finsupp.single_apply
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply, hl, hh, hs0, hs1]
  by_cases h0 : i < 0
  · rw [if_pos h0, if_neg (by omega : ¬ (0 : ℤ) = i), if_neg (by omega : ¬ (1 : ℤ) = i),
      if_neg (by omega : ¬ (2 : ℤ) ≤ i)]
    ring
  by_cases h1 : i = 0
  · subst h1
    rw [if_neg h0, if_pos (rfl : (0 : ℤ) = 0), if_neg (by omega : ¬ (1 : ℤ) = (0 : ℤ)),
      if_neg (by omega : ¬ (2 : ℤ) ≤ (0 : ℤ))]
    ring
  by_cases h2 : i = 1
  · subst h2
    rw [if_neg h0, if_neg (by omega : ¬ (0 : ℤ) = (1 : ℤ)), if_pos (rfl : (1 : ℤ) = 1),
      if_neg (by omega : ¬ (2 : ℤ) ≤ (1 : ℤ))]
    ring
  · rw [if_neg h0, if_neg (by omega : ¬ (0 : ℤ) = i), if_neg (by omega : ¬ (1 : ℤ) = i),
      if_pos (by omega : (2 : ℤ) ≤ i)]
    ring

/-- **The coding, read off the window.** -/
theorem elt_window (f : E) :
    elt f = elt (lowPart f) * (FreeGroup.of (0 : ℤ) ^ f 0 *
      (FreeGroup.of (1 : ℤ) ^ f 1 * elt (highPart f))) := by
  have hord2 : ∀ i ∈ (Finsupp.single (1 : ℤ) (f 1)).support,
      ∀ j ∈ (highPart f).support, i < j := by
    intro i hi j hj
    have hi1 : i = 1 := single_support_eq hi
    have hj2 : 2 ≤ j := highPart_le hj
    omega
  have hA := elt_add_of_lt hord2
  rw [elt_single] at hA
  have hord1 : ∀ i ∈ (Finsupp.single (0 : ℤ) (f 0)).support,
      ∀ j ∈ (Finsupp.single (1 : ℤ) (f 1) + highPart f).support, i < j := by
    intro i hi j hj
    have hi0 : i = 0 := single_support_eq hi
    have hj1 : 1 ≤ j :=
      support_add_bound (P := fun j => 1 ≤ j)
        (fun k hk => by rw [single_support_eq hk]) (fun k hk => by
          have := highPart_le hk; omega) j hj
    omega
  have hB := elt_add_of_lt hord1
  rw [elt_single, hA] at hB
  have hord0 : ∀ i ∈ (lowPart f).support,
      ∀ j ∈ (Finsupp.single (0 : ℤ) (f 0) +
        (Finsupp.single (1 : ℤ) (f 1) + highPart f)).support, i < j := by
    intro i hi j hj
    have hi0 : i < 0 := lowPart_lt hi
    have hj0 : 0 ≤ j :=
      support_add_bound (P := fun j => 0 ≤ j)
        (fun k hk => by rw [single_support_eq hk])
        (support_add_bound (P := fun j => 0 ≤ j)
          (fun k hk => by rw [single_support_eq hk]; norm_num)
          (fun k hk => by have := highPart_le hk; omega)) j hj
    omega
  have hC := elt_add_of_lt hord0
  rw [hB] at hC
  conv_lhs => rw [window_decomp f]
  exact hC

/-! ## 4.  The transposition -/

/-- The transposition of the first two coordinates of a sequence. -/
noncomputable def tauSeq (f : E) : E :=
  Finsupp.equivMapDomain (Equiv.swap (0 : ℤ) 1) f

theorem tauSeq_apply (f : E) (i : ℤ) : tauSeq f i = f (Equiv.swap (0 : ℤ) 1 i) := by
  unfold tauSeq
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_swap]

@[simp] theorem tauSeq_zero (f : E) : tauSeq f 0 = f 1 := by
  rw [tauSeq_apply, Equiv.swap_apply_left]

@[simp] theorem tauSeq_one (f : E) : tauSeq f 1 = f 0 := by
  rw [tauSeq_apply, Equiv.swap_apply_right]

theorem tauSeq_of_ne (f : E) (i : ℤ) (h0 : i ≠ 0) (h1 : i ≠ 1) : tauSeq f i = f i := by
  rw [tauSeq_apply, Equiv.swap_apply_of_ne_of_ne h0 h1]

theorem lowPart_tauSeq (f : E) : lowPart (tauSeq f) = lowPart f := by
  refine Finsupp.ext fun i => ?_
  unfold lowPart
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases h : i < 0
  · rw [if_pos h, if_pos h, tauSeq_of_ne f i (by omega) (by omega)]
  · rw [if_neg h, if_neg h]

theorem highPart_tauSeq (f : E) : highPart (tauSeq f) = highPart f := by
  refine Finsupp.ext fun i => ?_
  unfold highPart
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases h : 2 ≤ i
  · rw [if_pos h, if_pos h, tauSeq_of_ne f i (by omega) (by omega)]
  · rw [if_neg h, if_neg h]

/-- **The transposition moves nothing but the two window syllables.** -/
theorem elt_tauSeq (f : E) :
    elt (tauSeq f) = elt (lowPart f) * (FreeGroup.of (0 : ℤ) ^ f 1 *
      (FreeGroup.of (1 : ℤ) ^ f 0 * elt (highPart f))) := by
  rw [elt_window (tauSeq f), lowPart_tauSeq, highPart_tauSeq, tauSeq_zero, tauSeq_one]

/-- **The two codings differ in the order of the two window syllables, and in
nothing else.** -/
theorem bElt_tauSeq (f : E) :
    ∃ X Y : F₃,
      bElt f = X * (rowElt 0 ^ f 0 * (rowElt 1 ^ f 1 * Y)) ∧
      bElt (tauSeq f) = X * (rowElt 0 ^ f 1 * (rowElt 1 ^ f 0 * Y)) := by
  refine ⟨bElt (lowPart f), bElt (highPart f), ?_, ?_⟩
  · unfold bElt
    rw [elt_window f, map_mul, map_mul, map_mul, map_zpow, map_zpow, rowHom_of, rowHom_of]
  · unfold bElt
    rw [elt_tauSeq f, map_mul, map_mul, map_mul, map_zpow, map_zpow, rowHom_of, rowHom_of]

theorem tauOp_eq_image (B : Set E) : tauOp B = tauSeq '' B := by
  refine Set.ext fun f => ?_
  constructor
  · rintro ⟨g, hg, h0, h1, hrest⟩
    refine ⟨g, hg, Finsupp.ext fun i => ?_⟩
    by_cases hi0 : i = 0
    · subst hi0
      rw [tauSeq_zero]
      exact h0.symm
    by_cases hi1 : i = 1
    · subst hi1
      rw [tauSeq_one]
      exact h1.symm
    · rw [tauSeq_of_ne g i hi0 hi1]
      exact (hrest i hi0 hi1).symm
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, tauSeq_zero g, tauSeq_one g, fun i h0 h1 => tauSeq_of_ne g i h0 h1⟩

/-! ## 5.  What `τ` reduces to -/

/-- **Input: a group in which the two window syllables can be transposed.**

The shape is the one `Higman.OperationClosureRho.FlipWitness` has, and
`benignTF_of_conj` consumes both: a finitely presented torsion-free overgroup
of `F₃` in which benignness with a torsion-free witness survives the
enlargement, and one element of it whose conjugation action realizes the
operation on the coding.  `bElt_tauSeq` says exactly what that action has to
be: fix the parts of the conjugator below and above the window, and exchange
the two syllables inside it.

**Nothing inhabits this structure**, and unlike the flip no construction is
proposed: the permutation of the free basis `{a ^ w : w ∈ K}` that a swap
induces is the identity off the sorted normal forms, and the row calculus of
`Higman.RowSubgroup` produces no such permutation. -/
structure SwapWitness where
  /-- The overgroup. -/
  G : Type
  /-- Its group structure. -/
  [group : Group G]
  /-- It is finitely presented. -/
  [fp : Group.IsFinitelyPresented G]
  /-- It is torsion-free. -/
  torsionFree : IsPowerTorsionFree G
  /-- `F₃` sits inside it. -/
  emb : F₃ →* G
  /-- ... as a subgroup. -/
  emb_injective : Function.Injective emb
  /-- The element that transposes the two window syllables. -/
  swap : G
  /-- ... which does. -/
  swap_conj : ∀ f : E, swap * emb (aElt f) * swap⁻¹ = emb (aElt (tauSeq f))
  /-- Benignness with a torsion-free witness survives the enlargement of the
  ambient group. -/
  transport : ∀ H : Subgroup F₃, BenignTF H → BenignTF (H.map emb)

attribute [instance] SwapWitness.group SwapWitness.fp

/-- **Higman's operation `τ`, from the swap.** -/
theorem benignTF_ASub_tauOp_of_swap (w : SwapWitness) (B : Set E)
    (h : BenignTF (ASub B)) : BenignTF (ASub (tauOp B)) := by
  refine benignTF_of_conj w.emb w.emb_injective w.swap w.transport ?_ h
  unfold ASub
  rw [tauOp_eq_image, MonoidHom.map_closure, MonoidHom.map_closure,
    MonoidHom.map_closure]
  simp only [Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  exact w.swap_conj x

end Seq
end Higman
end GroupApproximation

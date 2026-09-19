import GroupApproximation.Higman.OperationClosureTau
import GroupApproximation.Higman.TorsionFreeImageClosure

/-!
# What `τ` costs: the refutation, the sharp interface, and the apparatus it needs

`Higman.OperationClosureTau` reduces Higman's operation `τ` --- transpose the
first two coordinates --- to `Seq.SwapWitness`: an element of a finitely
presented torsion-free overgroup of `F₃` conjugating `a_f` to `a_{τ f}` for
every `f`.  Nothing inhabits that structure, and the file says, without proof,
that the row calculus produces no such permutation.  This file does four
things.

## 1.  The refutation, as a theorem

`not_tau_of_endomorphism`: **no endomorphism `ψ` of `F₃` fixing `a` and mapping
`K` into `K` satisfies `ψ (a_f) = a_{τ f}` for all `f`.**  This is strictly
stronger than the two-letter witness recorded in
`research/mikaelian-rho-tau-shortcuts-fail.md`, which refutes one candidate
`ψ` --- the swap of `b₀` and `b₁`.  Here the swap is not assumed: it is
*derived*.  Testing at `f = single 0 1` forces `ψ r₀ = r₁` and testing at
`f = single 1 1` forces `ψ r₁ = r₀`, because `a^u = a^v` with `u, v ∈ K` forces
`u = v` (`conj_a_inj`, from `Conj.cbHom_injective`).  Only then does the
two-letter witness `f 0 = f 1 = 1` apply, and it kills the whole family.

So `τ` is not an endomorphism of `F₃` in any disguise, and the search for a
cheap `F₃`-native route can stop.

## 2.  An automorphism suffices; an element is not needed

`Seq.SwapWitness` asks for an element, because `benignTF_of_conj` was the shape
in view.  `benignTF_of_aut` --- which `ρ` uses --- consumes an automorphism,
and that is the right shape here: the construction the sources point at
produces a *letter permutation* of the `d`-generators, which is outer.
`SwapAutWitness` and `benignTF_ASub_tauOp_of_swapAut` are the automorphism
version, and `SwapWitness.toSwapAutWitness` shows the element version is a
special case of it.

## 3.  The `transport` clause is free

Every witness structure in this lane carries
`transport : ∀ H, BenignTF H → BenignTF (H.map emb)` as an open field.  It is
open no longer: `Seq.torsionFreeImageClosure` proves it at every embedding into
a finitely presented torsion-free group.  `SwapAutWitness.ofAut` packages that,
so **`τ` now needs a construction and nothing else** --- a finitely presented
torsion-free overgroup of `F₃` and one automorphism of it.
`benignTF_ASub_tauOp_of_aut` is the closure in that form.

## 4.  What the construction has to look like

`WindowApparatus` is the interface Higman's `d/e` apparatus meets: an
automorphism fixing `a` that moves the conjugator `b_f` to `b_{τ f}` **up to an
element centralizing `a`**.  That slack is the whole point --- it is what
Higman's weight-vector property (his Lemma 4.2, that `a` is centralized by the
derived group of `⟨d_i⟩`) buys, and it is what makes the exponent swap into a
letter swap.  `WindowApparatus.toSwapAutWitness` proves the interface closes
`τ`.

The interface also says exactly what an inhabitant may **not** look like, and
this is the design constraint worth carrying: if the automorphism mapped
`emb F₃` into itself, the centralizing element would lie in
`emb F₃ ∩ C(emb a) = emb ⟨a⟩` --- because `emb` is injective --- and
`f = single 0 1` would force `r₀ = r₁`.  So an inhabitant must move `emb F₃`
off itself and the centralizing elements must be genuinely new.  That is the
reason Higman's Section 4 lives in `⟨a, d, e⟩` rather than in an overgroup of
`F₃`, and the reason the naive repair --- imposing `[r₀, r₁] ∈ C(a)` --- is not
available: it would identify `a^{b_f}` with `a^{b_g}` for `f ≠ g` and
contradict injectivity of the coding.

Costing for the apparatus is in `notes/W6_TAU_BASE_S_PRICING_2026-08-22.md`.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

open GroupApproximation.Higman.Conj

/-! ## 1.  Conjugates of `a` remember their conjugator -/

/-- **The coding is faithful on `K`.**  Two elements of `K` that conjugate `a`
the same way are equal.  This is `Conj.cbHom_injective` with the free basis
unwound, and it is the workhorse of the refutation below. -/
theorem conj_a_inj {u v : F₃} (hu : u ∈ K) (hv : v ∈ K)
    (h : u⁻¹ * a * u = v⁻¹ * a * v) : u = v := by
  have h1 : cbHom (FreeGroup.of (⟨u, hu⟩ : ↥K))
      = cbHom (FreeGroup.of (⟨v, hv⟩ : ↥K)) := by
    rw [cbHom_of, cbHom_of]
    exact h
  have h2 : (⟨u, hu⟩ : ↥K) = ⟨v, hv⟩ :=
    FreeGroup.of_injective (cbHom_injective h1)
  exact congrArg Subtype.val h2

/-! ## 2.  Two row elements do not commute

The two-letter witness needs one negative fact, and a free group gives it only
through a concrete non-abelian target.  `Equiv.Perm (Fin 3)` is the smallest
one, and the two transpositions `(0 1)` and `(1 2)` do not commute. -/

/-- A concrete non-abelian target for the index letters. -/
def permTest : FreeGroup ℤ →* Equiv.Perm (Fin 3) :=
  FreeGroup.lift (fun i : ℤ =>
    if i = 0 then Equiv.swap 0 1 else if i = 1 then Equiv.swap 1 2 else 1)

theorem permTest_of_zero : permTest (FreeGroup.of (0 : ℤ)) = Equiv.swap 0 1 := by
  unfold permTest
  rw [FreeGroup.lift_apply_of, if_pos (rfl : (0 : ℤ) = 0)]

theorem permTest_of_one : permTest (FreeGroup.of (1 : ℤ)) = Equiv.swap 1 2 := by
  unfold permTest
  rw [FreeGroup.lift_apply_of, if_neg (by omega : ¬ (1 : ℤ) = 0),
    if_pos (rfl : (1 : ℤ) = 1)]

theorem of_zero_of_one_not_commute :
    FreeGroup.of (0 : ℤ) * FreeGroup.of 1 ≠ FreeGroup.of (1 : ℤ) * FreeGroup.of 0 := by
  intro h
  have h3 := congrArg permTest h
  rw [map_mul, map_mul, permTest_of_zero, permTest_of_one] at h3
  -- The ascriptions are load-bearing: without them the product's type is still a
  -- metavariable when it is applied, and the application does not elaborate.
  have h4 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 3)) 0
      = (Equiv.swap (1 : Fin 3) 2 * Equiv.swap 0 1 : Equiv.Perm (Fin 3)) 0 := by
    rw [h3]
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1)
      (by decide : (0 : Fin 3) ≠ 2), Equiv.swap_apply_left,
    Equiv.swap_apply_left] at h4
  exact absurd h4 (by decide)

/-- **The two window rows do not commute.**  The rows are a free basis
(`rowHom_injective`), so this is the previous lemma transported. -/
theorem rowElt_zero_one_not_commute : rowElt 0 * rowElt 1 ≠ rowElt 1 * rowElt 0 := by
  intro h
  refine of_zero_of_one_not_commute (rowHom_injective ?_)
  rw [map_mul, map_mul, rowHom_of, rowHom_of]
  exact h

/-! ## 3.  The coding on the sequences the refutation tests -/

theorem bElt_single (i n : ℤ) : bElt (Finsupp.single i n) = rowElt i ^ n := by
  unfold bElt
  rw [Split.elt_single, map_zpow, rowHom_of]

theorem tauSeq_single_zero (n : ℤ) :
    tauSeq (Finsupp.single (0 : ℤ) n) = Finsupp.single (1 : ℤ) n := by
  refine Finsupp.ext fun i => ?_
  by_cases h0 : i = 0
  · subst h0
    rw [tauSeq_zero, Finsupp.single_apply, Finsupp.single_apply,
      if_neg (by omega : ¬ (0 : ℤ) = (1 : ℤ)), if_neg (by omega : ¬ (1 : ℤ) = (0 : ℤ))]
  by_cases h1 : i = 1
  · subst h1
    rw [tauSeq_one, Finsupp.single_apply, Finsupp.single_apply,
      if_pos (rfl : (0 : ℤ) = 0), if_pos (rfl : (1 : ℤ) = 1)]
  · rw [tauSeq_of_ne _ i h0 h1, Finsupp.single_apply, Finsupp.single_apply,
      if_neg (by omega : ¬ (0 : ℤ) = i), if_neg (by omega : ¬ (1 : ℤ) = i)]

theorem tauSeq_single_one (n : ℤ) :
    tauSeq (Finsupp.single (1 : ℤ) n) = Finsupp.single (0 : ℤ) n := by
  refine Finsupp.ext fun i => ?_
  by_cases h0 : i = 0
  · subst h0
    rw [tauSeq_zero, Finsupp.single_apply, Finsupp.single_apply,
      if_pos (rfl : (1 : ℤ) = 1), if_pos (rfl : (0 : ℤ) = 0)]
  by_cases h1 : i = 1
  · subst h1
    rw [tauSeq_one, Finsupp.single_apply, Finsupp.single_apply,
      if_neg (by omega : ¬ (1 : ℤ) = (0 : ℤ)), if_neg (by omega : ¬ (0 : ℤ) = (1 : ℤ))]
  · rw [tauSeq_of_ne _ i h0 h1, Finsupp.single_apply, Finsupp.single_apply,
      if_neg (by omega : ¬ (1 : ℤ) = i), if_neg (by omega : ¬ (0 : ℤ) = i)]

/-- The two-letter witness: the sequence with `f 0 = f 1 = 1`.  `τ` fixes it,
and its coding is `r₀ r₁`. -/
noncomputable def oneOne : E := Finsupp.single (0 : ℤ) 1 + Finsupp.single (1 : ℤ) 1

theorem oneOne_apply_zero : oneOne 0 = 1 := by
  unfold oneOne
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
    if_pos (rfl : (0 : ℤ) = 0), if_neg (by omega : ¬ (1 : ℤ) = (0 : ℤ)), add_zero]

theorem oneOne_apply_one : oneOne 1 = 1 := by
  unfold oneOne
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
    if_neg (by omega : ¬ (0 : ℤ) = (1 : ℤ)), if_pos (rfl : (1 : ℤ) = 1), zero_add]

/-- **`τ` fixes the two-letter witness.** -/
theorem tauSeq_oneOne : tauSeq oneOne = oneOne := by
  refine Finsupp.ext fun i => ?_
  by_cases h0 : i = 0
  · subst h0
    rw [tauSeq_zero]
    exact oneOne_apply_one.trans oneOne_apply_zero.symm
  by_cases h1 : i = 1
  · subst h1
    rw [tauSeq_one]
    exact oneOne_apply_zero.trans oneOne_apply_one.symm
  · exact tauSeq_of_ne oneOne i h0 h1

/-- **... but its coding is `r₀ r₁`, which is not `r₁ r₀`.** -/
theorem bElt_oneOne : bElt oneOne = rowElt 0 * rowElt 1 := by
  have hord : ∀ i ∈ (Finsupp.single (0 : ℤ) (1 : ℤ)).support,
      ∀ j ∈ (Finsupp.single (1 : ℤ) (1 : ℤ)).support, i < j := by
    intro i hi j hj
    have hi0 : i = 0 := single_support_eq hi
    have hj1 : j = 1 := single_support_eq hj
    omega
  unfold bElt oneOne
  rw [elt_add_of_lt hord, Split.elt_single, Split.elt_single, map_mul,
    map_zpow, map_zpow, rowHom_of, rowHom_of, zpow_one, zpow_one]

/-! ## 4.  The refutation -/

/-- **No endomorphism of `F₃` realizes `τ`.**

The hypotheses are the weakest under which the question makes sense: `ψ` fixes
`a`, so that it acts on the conjugates of `a` at all, and `ψ` maps the
conjugating subgroup `K` into itself, so that `conj_a_inj` applies to its
values.  Neither hypothesis says anything about what `ψ` does to the rows ---
that is derived, and it is derived to be the swap that
`research/mikaelian-rho-tau-shortcuts-fail.md` refutes.

Together with `Seq.bElt_tauSeq` this is the precise statement that `τ`, unlike
`σ`, has no free-group shortcut: it is an adjacent-syllable transposition, and
no endomorphism performs one. -/
theorem not_tau_of_endomorphism (ψ : F₃ →* F₃) (hψa : ψ a = a)
    (hψK : ∀ x ∈ K, ψ x ∈ K) : ¬ ∀ f : E, ψ (aElt f) = aElt (tauSeq f) := by
  intro h
  have key : ∀ u : F₃, ψ (u⁻¹ * a * u) = (ψ u)⁻¹ * a * ψ u := by
    intro u
    rw [map_mul, map_mul, map_inv, hψa]
  have h0 : ψ (rowElt 0) = rowElt 1 := by
    have hf := h (Finsupp.single (0 : ℤ) 1)
    rw [tauSeq_single_zero] at hf
    unfold aElt at hf
    rw [bElt_single, bElt_single, zpow_one, zpow_one, key] at hf
    exact conj_a_inj (hψK _ (rowElt_mem_K 0)) (rowElt_mem_K 1) hf
  have h1 : ψ (rowElt 1) = rowElt 0 := by
    have hf := h (Finsupp.single (1 : ℤ) 1)
    rw [tauSeq_single_one] at hf
    unfold aElt at hf
    rw [bElt_single, bElt_single, zpow_one, zpow_one, key] at hf
    exact conj_a_inj (hψK _ (rowElt_mem_K 1)) (rowElt_mem_K 0) hf
  have hfin := h oneOne
  rw [tauSeq_oneOne] at hfin
  unfold aElt at hfin
  rw [bElt_oneOne, key, map_mul, h0, h1] at hfin
  have hswap : rowElt 1 * rowElt 0 = rowElt 0 * rowElt 1 :=
    conj_a_inj (Subgroup.mul_mem K (rowElt_mem_K 1) (rowElt_mem_K 0))
      (Subgroup.mul_mem K (rowElt_mem_K 0) (rowElt_mem_K 1)) hfin
  exact rowElt_zero_one_not_commute hswap.symm

/-! ## 5.  The interface an automorphism has to meet -/

/-- **Input: an overgroup *automorphism* realizing the transposition.**

This is `Seq.SwapWitness` with the element replaced by an automorphism.  It is
strictly weaker --- `SwapWitness.toSwapAutWitness` --- and it is the shape the
sources' construction actually produces, since a permutation of the
`d`-generators is outer.

**Nothing inhabits this structure.** -/
structure SwapAutWitness where
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
  /-- The automorphism that transposes the two window syllables. -/
  swapAut : G ≃* G
  /-- ... which does. -/
  swap_conj : ∀ f : E, swapAut (emb (aElt f)) = emb (aElt (tauSeq f))
  /-- Benignness with a torsion-free witness survives the enlargement of the
  ambient group. -/
  transport : ∀ H : Subgroup F₃, BenignTF H → BenignTF (H.map emb)

attribute [instance] SwapAutWitness.group SwapAutWitness.fp

/-- **Higman's operation `τ`, from the automorphism.** -/
theorem benignTF_ASub_tauOp_of_swapAut (w : SwapAutWitness) (B : Set E)
    (h : BenignTF (ASub B)) : BenignTF (ASub (tauOp B)) := by
  refine benignTF_of_aut w.emb w.emb_injective w.swapAut w.transport ?_ h
  unfold ASub
  rw [tauOp_eq_image, MonoidHom.map_closure, MonoidHom.map_closure,
    MonoidHom.map_closure]
  simp only [Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  exact w.swap_conj x

/-- The element form is a special case: conjugation is an automorphism. -/
def SwapWitness.toSwapAutWitness (w : SwapWitness) : SwapAutWitness where
  G := w.G
  torsionFree := w.torsionFree
  emb := w.emb
  emb_injective := w.emb_injective
  swapAut := MulAut.conj w.swap
  swap_conj := fun f => w.swap_conj f
  transport := w.transport

/-! ## 6.  The `transport` clause is not an input any more -/

/-- **Benignness with a torsion-free witness survives any enlargement to a
finitely presented torsion-free group.**  This is
`Seq.torsionFreeImageClosure`, which `Higman.TorsionFreeImageClosure` proves,
specialized to embeddings of `F₃`.  Every witness structure in this lane
carries this as an open field; it is not open. -/
theorem transport_of_torsionFreeImageClosure {Γ : Type} [Group Γ]
    [Group.IsFinitelyPresented Γ] (hΓ : IsPowerTorsionFree Γ) (φ : F₃ →* Γ)
    (hφ : Function.Injective φ) :
    ∀ H : Subgroup F₃, BenignTF H → BenignTF (H.map φ) := by
  letI : Group.FG F₃ :=
    ProductFinitePresentation.fg_of_isFinitelyPresented F₃
  intro H hH
  exact torsionFreeImageClosure F₃ Γ hΓ H φ hφ hH

/-- **The sharp input for `τ`: a group and an automorphism, nothing else.** -/
def SwapAutWitness.ofAut {Γ : Type} [Group Γ]
    [Group.IsFinitelyPresented Γ] (hΓ : IsPowerTorsionFree Γ) (φ : F₃ →* Γ)
    (hφ : Function.Injective φ) (Φ : Γ ≃* Γ)
    (hΦ : ∀ f : E, Φ (φ (aElt f)) = φ (aElt (tauSeq f))) : SwapAutWitness where
  G := Γ
  torsionFree := hΓ
  emb := φ
  emb_injective := hφ
  swapAut := Φ
  swap_conj := hΦ
  transport := transport_of_torsionFreeImageClosure hΓ φ hφ

/-- **Higman's operation `τ` from a construction alone.**  No classical input
remains: given a finitely presented torsion-free overgroup of `F₃` and one
automorphism of it transposing the two window syllables of every coded
conjugator, `τ` preserves benignness with a torsion-free witness. -/
theorem benignTF_ASub_tauOp_of_aut {Γ : Type} [Group Γ]
    [Group.IsFinitelyPresented Γ] (hΓ : IsPowerTorsionFree Γ) (φ : F₃ →* Γ)
    (hφ : Function.Injective φ) (Φ : Γ ≃* Γ)
    (hΦ : ∀ f : E, Φ (φ (aElt f)) = φ (aElt (tauSeq f))) (B : Set E)
    (h : BenignTF (ASub B)) : BenignTF (ASub (tauOp B)) :=
  benignTF_ASub_tauOp_of_swapAut (SwapAutWitness.ofAut hΓ φ hφ Φ hΦ) B h

/-! ## 7.  The apparatus interface: the swap, modulo the centralizer of `a` -/

/-- Conjugating by something times a central-for-`a` element is conjugating by
the something.  This is the slack Higman's weight-vector property provides. -/
theorem conj_of_centralizer {Γ : Type} [Group Γ] {A z B : Γ}
    (hz : z * A = A * z) : (z * B)⁻¹ * A * (z * B) = B⁻¹ * A * B := by
  calc (z * B)⁻¹ * A * (z * B) = B⁻¹ * (z⁻¹ * (A * z)) * B := by group
    _ = B⁻¹ * (z⁻¹ * (z * A)) * B := by rw [← hz]
    _ = B⁻¹ * A * B := by group

/-- **Input: the shape Higman's `d/e` apparatus meets.**

An automorphism of a finitely presented torsion-free overgroup of `F₃` that
fixes `a` and carries the conjugator of `f` to the conjugator of `τ f` **up to
an element centralizing `a`**.  The slack is essential: without it the
requirement is an equation between two elements of `F₃`, which
`not_tau_of_endomorphism` refutes.

Higman's Lemma 4.2 --- `a` is centralized by the derived group of `⟨d_i⟩`, so
that `a ^ w` for a `d`-word `w` depends only on the weight vector of `w` ---
is exactly a supply of such elements, and with it the exponent swap becomes the
letter swap `d₀ ↔ d₁`.

**Nothing inhabits this structure**, and the constraint an inhabitant must meet
is recorded in this file's header: `swapAut` cannot map `emb F₃` into itself,
and the elements `z` cannot lie in `emb F₃`. -/
structure WindowApparatus where
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
  /-- The automorphism. -/
  swapAut : G ≃* G
  /-- It fixes `a`. -/
  swapAut_a : swapAut (emb a) = emb a
  /-- It transposes the window syllables of every conjugator, up to the
  centralizer of `a`. -/
  swapAut_bElt : ∀ f : E, ∃ z : G, z * emb a = emb a * z ∧
    swapAut (emb (bElt f)) = z * emb (bElt (tauSeq f))
  /-- Benignness with a torsion-free witness survives the enlargement of the
  ambient group.  `transport_of_torsionFreeImageClosure` discharges this. -/
  transport : ∀ H : Subgroup F₃, BenignTF H → BenignTF (H.map emb)

attribute [instance] WindowApparatus.group WindowApparatus.fp

/-- **The apparatus interface closes `τ`.** -/
def WindowApparatus.toSwapAutWitness (w : WindowApparatus) : SwapAutWitness where
  G := w.G
  torsionFree := w.torsionFree
  emb := w.emb
  emb_injective := w.emb_injective
  swapAut := w.swapAut
  transport := w.transport
  swap_conj := by
    intro f
    obtain ⟨z, hz, hzf⟩ := w.swapAut_bElt f
    have hembf : w.emb (aElt f)
        = (w.emb (bElt f))⁻¹ * w.emb a * w.emb (bElt f) := by
      unfold aElt
      rw [map_mul, map_mul, map_inv]
    have hembt : w.emb (aElt (tauSeq f))
        = (w.emb (bElt (tauSeq f)))⁻¹ * w.emb a * w.emb (bElt (tauSeq f)) := by
      unfold aElt
      rw [map_mul, map_mul, map_inv]
    rw [hembf, hembt, map_mul, map_mul, map_inv, hzf, w.swapAut_a]
    exact conj_of_centralizer hz

/-- **Higman's operation `τ`, from the apparatus.** -/
theorem benignTF_ASub_tauOp_of_apparatus (w : WindowApparatus) (B : Set E)
    (h : BenignTF (ASub B)) : BenignTF (ASub (tauOp B)) :=
  benignTF_ASub_tauOp_of_swapAut w.toSwapAutWitness B h

/-! ## 8.  The construction, reduced to a finitely generated carrier

Sections 5--7 say what a solution looks like.  This one says how to *build*
one, and reduces the whole of `τ` to a statement with no group extension in it.

The observation is that the transposition already **is** an automorphism of the
subgroup `A_E = ⟨a_f : f ∈ E⟩`.  The `a_f` are a free basis of it
(`Seq.aElt_injective`, off `Conj.cbHom_injective`), and `f ↦ τ f` is an
involution of the index set (`tauSeq_involutive`), so it permutes that basis.
The HNN extension of `F₃` along it therefore exists, is torsion-free, and its
stable letter does exactly what `Seq.SwapWitness` asks for.  The *only* thing
wrong with it is that `A_E` is not finitely generated, so the extension is not
finitely presented.

So it is enough to find a finitely presented torsion-free overgroup `K` of `F₃`
and a **finitely generated** `L ≤ K` that contains every `a_f` and carries the
permutation as an automorphism `ψ`.  Then `HNNExtension K L L ψ` is finitely
presented (`HNNFinitePresentation.isFinitelyPresented_hnnExtension`, because `L`
is finitely generated), torsion-free (`HNNBritton.isPowerTorsionFree_hnn`), and
its stable letter conjugates `a_f` to `a_{τ f}` --- a `Seq.SwapWitness`
outright, `transport` included by §6.  That is `SwapCarrier.toSwapWitness`.

Two things make this the right target rather than another restatement.

*It is the shape the sources build.*  Mikaelian's constructions are chains of
HNN extensions whose stable letters act on a finitely generated subgroup of the
stage below; the centralizing case `ψ = id` is `Higman.CentHNN`, and
`SwapCarrier` is that device with an arbitrary automorphism in place of the
identity, which is the generality `τ` needs.  No amalgam appears, so no
`Algebra.PushoutITorsionFree` is consumed.

*It is the shape this repository already produces.*  A benign witness for a
subgroup is precisely a finitely generated `L` inside a finitely presented `K`
cutting that subgroup out, and `Omega.benignTF_ASub_univ` produces one for
`A_E` itself --- conditionally on `Omega.OmegaInput`, which is a separate leaf
of the same list.  What `SwapCarrier` asks, on top of a benign witness for
`A_E`, is one automorphism of its `L`.  Higman's base case `S` is the same
pattern one size down: there `L = ⟨a_{(0,1)}, s⟩` inside `Higman.FlipGroup`'s
`G₂` and the automorphism is conjugation by `s`, which is why that leaf comes
out free.

**Nothing inhabits `SwapCarrier`.** -/

/-- **The transposition is an involution of the index set.**  With
`Seq.aElt_injective` this is why it permutes the free basis `{a_f}`. -/
theorem tauSeq_involutive (f : E) : tauSeq (tauSeq f) = f := by
  refine Finsupp.ext fun i => ?_
  by_cases h0 : i = 0
  · subst h0
    rw [tauSeq_zero, tauSeq_one]
  by_cases h1 : i = 1
  · subst h1
    rw [tauSeq_one, tauSeq_zero]
  · rw [tauSeq_of_ne _ i h0 h1, tauSeq_of_ne _ i h0 h1]

/-- **Input: a finitely generated carrier for the transposition.**

`L` is finitely generated, lives in a finitely presented torsion-free overgroup
of `F₃`, contains every coded conjugate `a_f`, and has an automorphism
performing `f ↦ τ f` on them.  Nothing is asked about what `ψ` does elsewhere
in `L`, and nothing is asked about `L ∩ F₃`.

**Nothing inhabits this structure.** -/
structure SwapCarrier where
  /-- The finitely presented overgroup. -/
  K : Type
  /-- Its group structure. -/
  [group : Group K]
  /-- It is finitely presented. -/
  [fp : Group.IsFinitelyPresented K]
  /-- It is torsion-free. -/
  torsionFree : IsPowerTorsionFree K
  /-- `F₃` sits inside it. -/
  emb : F₃ →* K
  /-- ... as a subgroup. -/
  emb_injective : Function.Injective emb
  /-- The carrier. -/
  L : Subgroup K
  /-- ... which is finitely generated; this is the whole content. -/
  L_fg : L.FG
  /-- It contains every coded conjugate. -/
  mem_L : ∀ f : E, emb (aElt f) ∈ L
  /-- The automorphism of the carrier. -/
  psi : ↥L ≃* ↥L
  /-- ... which transposes the window. -/
  psi_apply : ∀ f : E,
    ((psi ⟨emb (aElt f), mem_L f⟩ : ↥L) : K) = emb (aElt (tauSeq f))

attribute [instance] SwapCarrier.group SwapCarrier.fp

/-- The HNN extension of the carrier's ambient group along its automorphism. -/
abbrev SwapCarrier.Ext (w : SwapCarrier) : Type := HNNExtension w.K w.L w.L w.psi

theorem SwapCarrier.fg_carrier (w : SwapCarrier) : Group.FG ↥w.L :=
  (Group.fg_iff_subgroup_fg w.L).mpr w.L_fg

theorem SwapCarrier.isFinitelyPresented_ext (w : SwapCarrier) :
    Group.IsFinitelyPresented w.Ext := by
  letI : Group.FG ↥w.L := w.fg_carrier
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension w.psi

theorem SwapCarrier.torsionFree_ext (w : SwapCarrier) :
    IsPowerTorsionFree w.Ext :=
  HNNBritton.isPowerTorsionFree_hnn w.psi w.torsionFree

/-- `F₃` inside the extension. -/
noncomputable def SwapCarrier.embExt (w : SwapCarrier) : F₃ →* w.Ext :=
  (HNNExtension.of : w.K →* w.Ext).comp w.emb

theorem SwapCarrier.embExt_injective (w : SwapCarrier) :
    Function.Injective w.embExt :=
  (HNNExtension.of_injective w.psi).comp w.emb_injective

/-- **The stable letter transposes the window.** -/
theorem SwapCarrier.conj_t (w : SwapCarrier) (f : E) :
    (HNNExtension.t : w.Ext) * w.embExt (aElt f) * (HNNExtension.t : w.Ext)⁻¹
      = w.embExt (aElt (tauSeq f)) := by
  have h := HNNExtension.equiv_eq_conj (φ := w.psi) ⟨w.emb (aElt f), w.mem_L f⟩
  rw [w.psi_apply f] at h
  exact h.symm

/-- **A finitely generated carrier gives Higman's swap outright.**  Finite
presentation is the HNN permanence theorem at a finitely generated associated
subgroup, torsion-freeness is Britton, and `transport` is §6. -/
noncomputable def SwapCarrier.toSwapWitness (w : SwapCarrier) : SwapWitness where
  G := w.Ext
  fp := w.isFinitelyPresented_ext
  torsionFree := w.torsionFree_ext
  emb := w.embExt
  emb_injective := w.embExt_injective
  swap := HNNExtension.t
  swap_conj := w.conj_t
  transport := by
    letI : Group.IsFinitelyPresented w.Ext := w.isFinitelyPresented_ext
    exact transport_of_torsionFreeImageClosure w.torsionFree_ext w.embExt
      w.embExt_injective

/-- **Higman's operation `τ`, from a finitely generated carrier.**  This is the
sharpest form the reduction reaches: no ambient construction is left, only a
finitely generated subgroup carrying the permutation. -/
theorem benignTF_ASub_tauOp_of_carrier (w : SwapCarrier) (B : Set E)
    (h : BenignTF (ASub B)) : BenignTF (ASub (tauOp B)) :=
  benignTF_ASub_tauOp_of_swap w.toSwapWitness B h

end Seq
end Higman
end GroupApproximation

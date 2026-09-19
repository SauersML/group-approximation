import GroupApproximation.Algebra.PermutationalWreathSimple
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Finiteness
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Range

/-!
# A continuum of finitely generated groups: the alternating lamp family

`non_mf_groups_exist.tex`, the second multiplicity paragraph of
`\subsection{Undecidability of MF recognition}` -- the one beginning *"Beyond
finite presentation, pairing $E$ with a continuum of pairwise nonisomorphic
finitely generated groups"* and ending in the `\leanverified` badge for
`ContinuumMultiplicity.manuscriptContinuumMultiplicity`.  (Anchor on those
phrases: the file's line numbers drift.)  It concludes that there are
`2^{\aleph_0}` pairwise nonisomorphic **finitely generated** non-MF groups.  The
counting step on top of Neumann's family is `Sofic/ContinuumMultiplicityCore`,
with
Neumann's family a quantified hypothesis there, reduced to its smallest form in
`Sofic/ContinuumFamilyCriterion`.  This file and `Monsters/NeumannContinuum`
discharge that hypothesis by constructing such a family and proving its
properties.

## The construction

Fix the free group `F₂ = FreeGroup (Fin 2)` on generators `a, b` and the
alternating group `A₅` as lamp group.  For a subgroup `H ≤ F₂` put

  `W H = A₅ ≀_{F₂/H} F₂ = (⨁_{F₂/H} A₅) ⋊ F₂`,

the permutational wreath product over the coset space.  Because `F₂` acts
transitively on `F₂/H`, `W H` is finitely generated (`fg_wreathQuotient`): the
two free generators together with the sixty one-site lamps at the base coset
generate it.

The index set is supplied by the subgroups

  `markedSubgroup S = ⟨ aⁿ b a⁻ⁿ : n ∈ S ⟩`,  `S ⊆ ℕ`,

which are pairwise distinct (`markedSubgroup_injective`): the lamplighter
picture `a ↦ inr a`, `b ↦ inl (single 1 k)` of `F₂` inside `A₅ ≀ F₂` sends
`aⁿ b a⁻ⁿ` to the one-site lamp at the site `aⁿ`, and the sites `aⁿ` are
pairwise distinct, so the subgroup remembers `S`.

## The separation mechanism

Distinct subgroups need not give nonisomorphic wreath products -- conjugate
subgroups give isomorphic ones -- so the family is separated by counting, in
exactly the manner of the manuscript's own paragraph.  The counting input is
`countable_isomorphic_subgroups`: for a fixed countable group `Q` only countably
many `H` satisfy `W H ≅ Q`.  The reason is that an isomorphism `e : W H ≃* Q`
transports three canonical generators to elements of `Q`, and `H` is recoverable
from those elements alone, because for `g ∈ F₂` the *detector*

  `detector H k g = inl (single base k) * (inr g * (inl (single base k))⁻¹ * (inr g)⁻¹)`

is trivial exactly when `g` fixes the base coset, i.e. exactly when `g ∈ H`
(`detector_eq_one_iff`), and its image under `e` is one fixed word in the
recorded elements.  So `H ↦ (recorded elements)` is injective on the fibre,
whose cardinality is therefore at most that of `(Fin 2 → Q) × Q`.

## What is *not* claimed

Neumann's groups are two-generator; the groups here are finitely generated (the
displayed generating set has sixty-two elements) and no attempt is made to
compute the minimal number of generators.  Two-generation is never used in the
manuscript's deduction, whose conclusion is about finitely generated groups and
whose Lean form `ContinuumMultiplicity.exists_continuum_pairwise_nonisomorphic`
consumes
`Group.FG` only.
-/

namespace GroupApproximation

namespace NeumannFamily

open SemidirectProduct

universe u v

/-! ## Lamps supported in a prescribed set of sites -/

section SuppInSet

variable {K : Type u} [Group K] {X : Type v}

/-- The configurations supported inside an arbitrary — possibly infinite — set
of sites.  This is the infinite-support companion of `suppIn`. -/
def lampSuppInSet (A : Set X) : Subgroup (Lamp K X) where
  carrier := {f | ∀ x : X, x ∉ A → f.toFun x = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro f g hf hg x hx
    show f.toFun x * g.toFun x = 1
    rw [hf x hx, hg x hx, one_mul]
  inv_mem' := by
    intro f hf x hx
    show (f.toFun x)⁻¹ = 1
    rw [hf x hx, inv_one]

/-- Membership in `lampSuppInSet` is support containment. -/
theorem mem_lampSuppInSet {A : Set X} {f : Lamp K X} :
    f ∈ lampSuppInSet (K := K) A ↔ ∀ x : X, x ∉ A → f.toFun x = 1 := Iff.rfl

/-- A one-site lamp is supported in any set of sites containing its site. -/
theorem single_mem_lampSuppInSet [DecidableEq X] {A : Set X} {x : X} (hx : x ∈ A) (k : K) :
    Lamp.single x k ∈ lampSuppInSet (K := K) A := by
  refine mem_lampSuppInSet.mpr fun y hy => ?_
  have hne : y ≠ x := by
    rintro rfl
    exact hy hx
  exact Lamp.single_apply_of_ne hne k

end SuppInSet

/-! ## The ambient data -/

/-- The acting group of the construction: the free group on two generators. -/
abbrev Acting : Type := FreeGroup (Fin 2)

/-- The lamp group of the construction: the alternating group on five letters,
the smallest nonabelian simple group. -/
abbrev AltLamp : Type := ↥(alternatingGroup (Fin 5))

/-- The lamp group is nontrivial, because it is simple. -/
theorem altLamp_nontrivial : Nontrivial AltLamp := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  infer_instance

/-- The first free generator. -/
def genA : Acting := FreeGroup.of 0

/-- The second free generator. -/
def genB : Acting := FreeGroup.of 1

@[simp] theorem genA_eq : genA = FreeGroup.of 0 := rfl

@[simp] theorem genB_eq : genB = FreeGroup.of 1 := rfl

/-- The `n`-th translate of the second generator by the first. -/
def conjGen (n : ℕ) : Acting := genA ^ n * genB * (genA ^ n)⁻¹

@[simp] theorem conjGen_def (n : ℕ) : conjGen n = genA ^ n * genB * (genA ^ n)⁻¹ := rfl

/-- The subgroup of the free group attached to a set of naturals. -/
def markedSubgroup (S : Set ℕ) : Subgroup Acting :=
  Subgroup.closure (conjGen '' S)

@[simp] theorem markedSubgroup_def (S : Set ℕ) :
    markedSubgroup S = Subgroup.closure (conjGen '' S) := rfl

/-! ## The sites `genA ^ n` are pairwise distinct -/

/-- The `genA`-degree homomorphism.  It is used only to separate the sites
`genA ^ n` from one another. -/
def degHom : Acting →* Multiplicative ℤ :=
  FreeGroup.lift fun i : Fin 2 => Multiplicative.ofAdd (if i = 0 then (1 : ℤ) else 0)

theorem degHom_genA : degHom genA = Multiplicative.ofAdd (1 : ℤ) := by
  simp [degHom]

/-- The degree of a power of the first generator, by induction.  Stated
separately because `Multiplicative.toAdd_pow` does not exist in this Mathlib. -/
theorem degHom_genA_pow (m : ℕ) :
    degHom (genA ^ m) = Multiplicative.ofAdd (m : ℤ) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, map_mul, ih, degHom_genA, ← ofAdd_add]
    push_cast
    rfl

/-- Distinct exponents give distinct powers of the first generator. -/
theorem genA_pow_injective : Function.Injective fun n : ℕ => genA ^ n := by
  intro m n hmn
  have hpow : (genA : Acting) ^ m = genA ^ n := hmn
  have h : degHom (genA ^ m) = degHom (genA ^ n) := congrArg degHom hpow
  rw [degHom_genA_pow, degHom_genA_pow] at h
  have h3 : (m : ℤ) = (n : ℤ) := Multiplicative.ofAdd.injective h
  exact_mod_cast h3

/-- The sites of the lamplighter picture: the translates of the base site by the
powers of the first generator.  They are pairwise distinct. -/
theorem site_injective :
    Function.Injective fun n : ℕ => ((genA ^ n : Acting) • (1 : Acting)) := by
  intro m n h
  have hm : ((genA ^ m : Acting) • (1 : Acting)) = genA ^ m := mul_one _
  have hn : ((genA ^ n : Acting) • (1 : Acting)) = genA ^ n := mul_one _
  refine genA_pow_injective ?_
  show (genA : Acting) ^ m = genA ^ n
  rw [← hm, ← hn]
  exact h

/-! ## Distinct sets of naturals give distinct subgroups -/

/-- The translates indexed by `S` lie in the subgroup they generate. -/
theorem conjGen_mem_markedSubgroup {S : Set ℕ} {n : ℕ} (hn : n ∈ S) :
    conjGen n ∈ markedSubgroup S := by
  rw [markedSubgroup_def]
  exact Subgroup.subset_closure ⟨n, hn, rfl⟩

/-- **The subgroup remembers the set.**  A translate outside the index set does
not lie in the subgroup: the lamplighter picture of the free group inside
`A₅ ≀ F₂` sends `conjGen n` to the one-site lamp at the site `genA ^ n`, and
those sites are pairwise distinct. -/
theorem conjGen_notMem_markedSubgroup {S : Set ℕ} {m : ℕ} (hm : m ∉ S) :
    conjGen m ∉ markedSubgroup S := by
  classical
  haveI := altLamp_nontrivial
  obtain ⟨k, hk⟩ := exists_ne (1 : AltLamp)
  obtain ⟨Φ, hΦA, hΦB⟩ :
      ∃ Φ : Acting →* Wreath AltLamp Acting Acting,
        Φ genA = inr genA ∧ Φ genB = inl (Lamp.single (1 : Acting) k) := by
    refine ⟨FreeGroup.lift fun i : Fin 2 =>
      if i = 0 then (inr genA : Wreath AltLamp Acting Acting)
      else inl (Lamp.single (1 : Acting) k), ?_, ?_⟩
    · simp
    · simp
  have hΦconj : ∀ n : ℕ,
      Φ (conjGen n) = inl (Lamp.single ((genA ^ n : Acting) • (1 : Acting)) k) := by
    intro n
    rw [conjGen_def, map_mul, map_mul, map_inv, map_pow, hΦA, hΦB, ← map_pow]
    exact conj_inl_single AltLamp Acting Acting (genA ^ n) (1 : Acting) k
  have hgen : markedSubgroup S ≤
      Subgroup.comap Φ (Subgroup.map
        (inl : Lamp AltLamp Acting →* Wreath AltLamp Acting Acting)
        (lampSuppInSet ((fun n : ℕ => ((genA ^ n : Acting) • (1 : Acting))) '' S))) := by
    rw [markedSubgroup_def]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨n, hn, rfl⟩
    show Φ (conjGen n) ∈ Subgroup.map
      (inl : Lamp AltLamp Acting →* Wreath AltLamp Acting Acting)
      (lampSuppInSet ((fun n : ℕ => ((genA ^ n : Acting) • (1 : Acting))) '' S))
    rw [hΦconj n]
    exact Subgroup.mem_map_of_mem _ (single_mem_lampSuppInSet (Set.mem_image_of_mem _ hn) k)
  intro hcon
  have hmem : Φ (conjGen m) ∈ Subgroup.map
      (inl : Lamp AltLamp Acting →* Wreath AltLamp Acting Acting)
      (lampSuppInSet ((fun n : ℕ => ((genA ^ n : Acting) • (1 : Acting))) '' S)) := hgen hcon
  rw [hΦconj m] at hmem
  obtain ⟨flamp, hflamp, hfe⟩ := hmem
  have hfeq : flamp = Lamp.single ((genA ^ m : Acting) • (1 : Acting)) k :=
    SemidirectProduct.inl_injective hfe
  have hnot : ((genA ^ m : Acting) • (1 : Acting)) ∉
      (fun n : ℕ => ((genA ^ n : Acting) • (1 : Acting))) '' S := by
    rintro ⟨n, hn, hnm⟩
    have hnm' : n = m := site_injective hnm
    subst hnm'
    exact hm hn
  have hval := (mem_lampSuppInSet.mp hflamp) ((genA ^ m : Acting) • (1 : Acting)) hnot
  rw [hfeq, Lamp.single_apply_self] at hval
  exact hk hval

/-- **Distinct sets give distinct subgroups.** -/
theorem markedSubgroup_injective : Function.Injective markedSubgroup := by
  intro S T h
  ext n
  constructor
  · intro hn
    by_contra hnT
    have h1 : conjGen n ∈ markedSubgroup T := by
      rw [← h]
      exact conjGen_mem_markedSubgroup hn
    exact conjGen_notMem_markedSubgroup hnT h1
  · intro hn
    by_contra hnS
    have h1 : conjGen n ∈ markedSubgroup S := by
      rw [h]
      exact conjGen_mem_markedSubgroup hn
    exact conjGen_notMem_markedSubgroup hnS h1

/-! ## The coset space and the family -/

/-- The base coset, the site at which the distinguished lamps sit. -/
def baseSite (H : Subgroup Acting) : Acting ⧸ H := QuotientGroup.mk 1

@[simp] theorem baseSite_def (H : Subgroup Acting) :
    baseSite H = (QuotientGroup.mk (1 : Acting) : Acting ⧸ H) := rfl

/-- Translating the base coset. -/
theorem smul_baseSite (H : Subgroup Acting) (g : Acting) :
    g • baseSite H = (QuotientGroup.mk g : Acting ⧸ H) := by
  show (QuotientGroup.mk (g * 1) : Acting ⧸ H) = QuotientGroup.mk g
  rw [mul_one]

/-- An element fixes the base coset exactly when it lies in the subgroup. -/
theorem smul_baseSite_iff (H : Subgroup Acting) (g : Acting) :
    g • baseSite H = baseSite H ↔ g ∈ H := by
  rw [smul_baseSite, baseSite_def, QuotientGroup.eq]
  simp

/-- **The members of the family are finitely generated.**  The action of the
free group on the coset space is transitive, so the wreath product is generated
by the two free generators together with the one-site lamps at the base
coset. -/
theorem fg_wreathQuotient (H : Subgroup Acting) :
    Group.FG (Wreath AltLamp Acting (Acting ⧸ H)) := by
  classical
  have htrans : ∀ x : Acting ⧸ H, ∃ g : Acting, g • baseSite H = x := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨g, smul_baseSite H g⟩
  have hclosure := wreath_eq_closure (K := AltLamp) (G := Acting) (X := Acting ⧸ H)
    (baseSite H) htrans (SG := Set.range (FreeGroup.of : Fin 2 → Acting))
    (FreeGroup.closure_range_of (Fin 2)) (SK := (Set.univ : Set AltLamp))
    Subgroup.closure_univ
  refine Group.fg_iff.mpr ⟨_, hclosure, ?_⟩
  exact (Set.Finite.image _ (Set.finite_range _)).union (Set.Finite.image _ Set.finite_univ)

/-- The member of the family attached to a set of naturals: the permutational
wreath product of `A₅` over the coset space of `markedSubgroup S`. -/
abbrev NeumannGroup (S : Set ℕ) : Type :=
  Wreath AltLamp Acting (Acting ⧸ markedSubgroup S)

instance instFGNeumannGroup (S : Set ℕ) : Group.FG (NeumannGroup S) :=
  fg_wreathQuotient (markedSubgroup S)

/-! ## The detector: the subgroup is visible inside the wreath product -/

/-- The detector element attached to `g`: the base lamp times the inverse of its
`g`-translate.  It is trivial exactly when `g` fixes the base coset. -/
def detector (H : Subgroup Acting) [DecidableEq (Acting ⧸ H)] (k : AltLamp) (g : Acting) :
    Wreath AltLamp Acting (Acting ⧸ H) :=
  inl (Lamp.single (baseSite H) k) *
    (inr g * (inl (Lamp.single (baseSite H) k))⁻¹ * (inr g)⁻¹)

@[simp] theorem detector_def (H : Subgroup Acting) [DecidableEq (Acting ⧸ H)]
    (k : AltLamp) (g : Acting) :
    detector H k g = inl (Lamp.single (baseSite H) k) *
      (inr g * (inl (Lamp.single (baseSite H) k))⁻¹ * (inr g)⁻¹) := rfl

/-- **The detector detects the subgroup.**  For a nontrivial lamp value the
detector element vanishes exactly on the subgroup. -/
theorem detector_eq_one_iff (H : Subgroup Acting) [DecidableEq (Acting ⧸ H)]
    {k : AltLamp} (hk : k ≠ 1) (g : Acting) :
    detector H k g = 1 ↔ g ∈ H := by
  have hinv : (Lamp.single (baseSite H) k : Lamp AltLamp (Acting ⧸ H))⁻¹
      = Lamp.single (baseSite H) k⁻¹ := by
    -- the base site is generalized first so that no simp set can unfold it and
    -- leave `single_apply_of_ne` without a match
    generalize baseSite H = b
    refine Lamp.ext fun y => ?_
    by_cases h : y = b
    · subst h
      simp
    · simp [Lamp.single_apply_of_ne h]
  have hinl : (inl (Lamp.single (baseSite H) k) : Wreath AltLamp Acting (Acting ⧸ H))⁻¹
      = inl (Lamp.single (baseSite H) k⁻¹) := by
    rw [← hinv, map_inv]
  have hone : (inl (1 : Lamp AltLamp (Acting ⧸ H)) : Wreath AltLamp Acting (Acting ⧸ H)) = 1 :=
    map_one _
  have hprod : detector H k g
      = inl (Lamp.single (baseSite H) k * Lamp.single (g • baseSite H) k⁻¹) := by
    rw [detector_def, hinl, conj_inl_single AltLamp Acting (Acting ⧸ H) g (baseSite H) k⁻¹,
      ← map_mul]
  rw [hprod]
  constructor
  · intro h1
    have h2 : Lamp.single (baseSite H) k * Lamp.single (g • baseSite H) k⁻¹ = 1 :=
      SemidirectProduct.inl_injective (h1.trans hone.symm)
    by_contra hgH
    have hne : baseSite H ≠ g • baseSite H := by
      intro hcon
      exact hgH ((smul_baseSite_iff H g).mp hcon.symm)
    exact single_mul_single_inv_ne_one hne hk h2
  · intro hgH
    rw [(smul_baseSite_iff H g).mpr hgH, ← Lamp.single_mul, mul_inv_cancel, Lamp.single_one]
    exact hone

/-! ## Countability of the isomorphism fibres -/

/-- **Countable fibres.**  For a fixed countable group `Q`, only countably many
subgroups `H ≤ F₂` give `A₅ ≀_{F₂/H} F₂ ≅ Q`.

An isomorphism `e` onto `Q` records three elements of `Q`: the images of the two
free generators and the image of the base lamp.  Since `F₂` is free on the two
generators, those three elements determine the image under `e` of every detector
element, and the detector elements determine `H`.  So the fibre injects into
`(Fin 2 → Q) × Q`. -/
theorem countable_isomorphic_subgroups (Q : Type) [Group Q] [Countable Q] :
    {H : Subgroup Acting |
      Nonempty (Wreath AltLamp Acting (Acting ⧸ H) ≃* Q)}.Countable := by
  classical
  haveI := altLamp_nontrivial
  obtain ⟨k, hk⟩ := exists_ne (1 : AltLamp)
  have hne : ∀ H : {H : Subgroup Acting |
      Nonempty (Wreath AltLamp Acting (Acting ⧸ H) ≃* Q)},
      Nonempty (Wreath AltLamp Acting (Acting ⧸ (H : Subgroup Acting)) ≃* Q) := fun H => H.2
  have he : ∀ H : {H : Subgroup Acting |
      Nonempty (Wreath AltLamp Acting (Acting ⧸ H) ≃* Q)},
      Wreath AltLamp Acting (Acting ⧸ (H : Subgroup Acting)) ≃* Q :=
    fun H => Classical.choice (hne H)
  have hinj : Function.Injective
      (fun H : {H : Subgroup Acting |
          Nonempty (Wreath AltLamp Acting (Acting ⧸ H) ≃* Q)} =>
        ((fun i : Fin 2 => he H (inr (FreeGroup.of i))),
          he H (inl (Lamp.single (baseSite (H : Subgroup Acting)) k)))) := by
    intro H H' hEq
    have hfst : (fun i : Fin 2 => he H (inr (FreeGroup.of i)))
        = (fun i : Fin 2 => he H' (inr (FreeGroup.of i))) := congrArg Prod.fst hEq
    have h2 : he H (inl (Lamp.single (baseSite (H : Subgroup Acting)) k))
        = he H' (inl (Lamp.single (baseSite (H' : Subgroup Acting)) k)) := congrArg Prod.snd hEq
    have h1 : ∀ i : Fin 2, he H (inr (FreeGroup.of i)) = he H' (inr (FreeGroup.of i)) :=
      fun i => congrFun hfst i
    have hhom : ((he H).toMonoidHom.comp (inr : Acting →* _))
        = ((he H').toMonoidHom.comp (inr : Acting →* _)) := FreeGroup.ext_hom _ _ h1
    have hE : ∀ g : Acting, he H (inr g) = he H' (inr g) := fun g =>
      DFunLike.congr_fun hhom g
    have key : ∀ g : Acting, g ∈ (H : Subgroup Acting) ↔ g ∈ (H' : Subgroup Acting) := by
      intro g
      rw [← detector_eq_one_iff (H : Subgroup Acting) hk g,
        ← detector_eq_one_iff (H' : Subgroup Acting) hk g,
        ← (he H).map_eq_one_iff, ← (he H').map_eq_one_iff, detector_def, detector_def]
      simp only [map_mul, map_inv, h2, hE]
    exact Subtype.ext (Subgroup.ext key)
  haveI : Countable {H : Subgroup Acting |
      Nonempty (Wreath AltLamp Acting (Acting ⧸ H) ≃* Q)} := hinj.countable
  exact Set.countable_coe_iff.mp inferInstance

end NeumannFamily

end GroupApproximation

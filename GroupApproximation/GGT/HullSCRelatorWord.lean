import GroupApproximation.GGT.HullSCRelatorFamily

/-!
# Hull's relator, spelled out, and §6 reduced to the separation estimate

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, Groups
Geom. Dyn. 10 (2016) 1077-1119, §6.

`HullSC.RelatorChoice` still carries six clauses.  Five of them are about the
*shape* of Hull's relator rather than about small cancellation, and this module
discharges all five by writing the relator down:

> `v = p · h^{m₁} h^{m₂} ⋯ h^{m_k}`, with `p` a spelling of `t⁻¹` in the base
> and `h = E.lox` the loxodromic element of the hyperbolically embedded
> subgroup.

* **`u ∈ N` is free.**  `listVal v = p.prod · h^{Σmᵢ} = t⁻¹ · h^{Σmᵢ}`, so
  `u = h^{Σmᵢ}`, which lies in `E.H` and hence in `N`.  Hull's `u` is not a
  choice at all once the relator has this shape.
* **Admissibility is free**, the base letters being letters of `A` and the
  `H`-letters powers of an element of `H`.
* **Depth is free.**  `exists_deep_pow` proves that all but finitely many powers
  of `h` escape `relBall ρ` together with their inverses, because `relBall ρ` is
  finite (`IsHyperbolicallyEmbedded.locallyFinite`) and `h` has infinite order
  (`not_isOfFinOrder_of_isLoxodromic`).  `exists_deep_exponents` turns that into
  arbitrarily long lists of deep exponents.
* **Length is free**, by taking more exponents.
* **`μ` is free**, and this is the one that matters: the estimate produces a
  constant `B` *before* the length, and the relator is then taken long enough
  that `B < μ|v|`.  `RelatorSeparation` has the quantifiers in that order.

What is left is Olshanskii's separation for this relator and nothing else.

## Why the leaf is not vacuous

`exists_base_spelling` and `exists_deep_relator_exponents` prove that every
clause of `RelatorSeparation` except the separation itself can be met, at every
`ρ` and every length.  So the leaf is a statement about matches, not a bundle in
which an unsatisfiable side condition could hide.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## Words built from a base spelling and a run of powers -/

section Spelling

variable {G : Type u} [Group G] {Λ : Type*}

omit [Group G] in
/-- The element a base letter names. -/
theorem val_base (g : G) :
    (GGT.RelLetter.base g : GGT.RelLetter G Λ).val = g := rfl

omit [Group G] in
/-- The element a component letter names. -/
theorem val_comp (lam : Λ) (h : G) :
    (GGT.RelLetter.comp lam h : GGT.RelLetter G Λ).val = h := rfl

/-- A word of base letters names the product of the letters. -/
theorem listVal_map_base (l : List G) :
    GGT.RelLetter.listVal
        (l.map (GGT.RelLetter.base : G → GGT.RelLetter G Λ)) = l.prod := by
  induction l with
  | nil => rfl
  | cons g t ih =>
      rw [List.map_cons, RelWord.listVal_cons, val_base, ih, List.prod_cons]

/-- A run of powers names the power of the sum. -/
theorem listVal_map_comp (lam : Λ) (a : G) (ms : List ℕ) :
    GGT.RelLetter.listVal
        (ms.map (fun m => (GGT.RelLetter.comp lam (a ^ m) : GGT.RelLetter G Λ)))
      = a ^ ms.sum := by
  induction ms with
  | nil =>
      rw [List.map_nil, GGT.RelLetter.listVal_nil, List.sum_nil, pow_zero]
  | cons m t ih =>
      rw [List.map_cons, RelWord.listVal_cons, val_comp, ih, List.sum_cons,
        pow_add]

end Spelling

/-! ## Hull's relator -/

variable {G : Type u} [Group G]

/-- **Hull's relator**: a spelling of `t⁻¹` in the base, followed by a run of
powers of the loxodromic element of the hyperbolically embedded subgroup.  The
element it names is `p.prod · a^{Σ mᵢ}`, so with `p.prod = t⁻¹` the second
factor is Hull's `u`, and it lies in `H` by construction. -/
def relatorWord (p : List G) (a : G) (ms : List ℕ) :
    List (GGT.RelLetter G Unit) :=
  p.map GGT.RelLetter.base
    ++ ms.map (fun m => GGT.RelLetter.comp () (a ^ m))

theorem listVal_relatorWord (p : List G) (a : G) (ms : List ℕ) :
    GGT.RelLetter.listVal (relatorWord p a ms) = p.prod * a ^ ms.sum := by
  show GGT.RelLetter.listVal
      (p.map GGT.RelLetter.base
        ++ ms.map (fun m => GGT.RelLetter.comp () (a ^ m)))
    = p.prod * a ^ ms.sum
  rw [RelWord.listVal_append, listVal_map_base, listVal_map_comp]

theorem length_relatorWord (p : List G) (a : G) (ms : List ℕ) :
    (relatorWord p a ms).length = p.length + ms.length := by
  show (p.map GGT.RelLetter.base
      ++ ms.map (fun m => GGT.RelLetter.comp () (a ^ m))).length
    = p.length + ms.length
  rw [List.length_append, List.length_map, List.length_map]

theorem mem_relatorWord {p : List G} {a : G} {ms : List ℕ}
    {x : GGT.RelLetter G Unit} (hx : x ∈ relatorWord p a ms) :
    (∃ g ∈ p, x = GGT.RelLetter.base g) ∨
      (∃ m ∈ ms, x = GGT.RelLetter.comp () (a ^ m)) := by
  have h : x ∈ p.map GGT.RelLetter.base ∨
      x ∈ ms.map (fun m => GGT.RelLetter.comp () (a ^ m)) := List.mem_append.mp hx
  rcases h with h | h
  · obtain ⟨g, hg, hgx⟩ := List.mem_map.mp h
    exact Or.inl ⟨g, hg, hgx.symm⟩
  · obtain ⟨m, hm, hmx⟩ := List.mem_map.mp h
    exact Or.inr ⟨m, hm, hmx.symm⟩

/-! ## Deep exponents exist -/

/-- An element of infinite order has injective natural powers. -/
theorem injective_pow_of_not_isOfFinOrder {a : G} (h : ¬ IsOfFinOrder a) :
    Function.Injective (fun n : ℕ => a ^ n) := by
  have hz : Function.Injective (fun n : ℤ => a ^ n) :=
    injective_zpow_iff_not_isOfFinOrder.mpr h
  intro m n hmn
  have hcast : a ^ (m : ℤ) = a ^ (n : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact hmn
  exact Nat.cast_injective (hz hcast)

/-- **All but finitely many powers are deep.**  The powers of an element of
infinite order are distinct, so only finitely many of them can lie in a finite
set together with their inverses. -/
theorem exists_deep_pow {a : G} (hinj : Function.Injective (fun n : ℕ => a ^ n))
    {S : Set G} (hS : S.Finite) (n₀ : ℕ) :
    ∃ m : ℕ, n₀ ≤ m ∧ a ^ m ∉ S ∧ (a ^ m)⁻¹ ∉ S := by
  have hS' : (S ∪ (fun x : G => x⁻¹) '' S).Finite := hS.union (hS.image _)
  have hT : ((fun n : ℕ => a ^ n) ⁻¹' (S ∪ (fun x : G => x⁻¹) '' S)).Finite :=
    Set.Finite.preimage (fun _ _ _ _ hxy => hinj hxy) hS'
  obtain ⟨M, hM⟩ := hT.bddAbove
  refine ⟨max n₀ (M + 1), le_max_left _ _, ?_, ?_⟩
  · intro hmem
    have h1 : max n₀ (M + 1)
        ∈ (fun n : ℕ => a ^ n) ⁻¹' (S ∪ (fun x : G => x⁻¹) '' S) := Or.inl hmem
    have h2 : max n₀ (M + 1) ≤ M := hM h1
    have h3 : M + 1 ≤ max n₀ (M + 1) := le_max_right _ _
    omega
  · intro hmem
    have h1 : max n₀ (M + 1)
        ∈ (fun n : ℕ => a ^ n) ⁻¹' (S ∪ (fun x : G => x⁻¹) '' S) :=
      Or.inr ⟨(a ^ max n₀ (M + 1))⁻¹, hmem, inv_inv _⟩
    have h2 : max n₀ (M + 1) ≤ M := hM h1
    have h3 : M + 1 ≤ max n₀ (M + 1) := le_max_right _ _
    omega

/-- Arbitrarily long lists of deep exponents. -/
theorem exists_deep_exponents {a : G}
    (hinj : Function.Injective (fun n : ℕ => a ^ n)) {S : Set G} (hS : S.Finite)
    (L : ℕ) : ∃ ms : List ℕ, L ≤ ms.length ∧
      ∀ m ∈ ms, a ^ m ∉ S ∧ (a ^ m)⁻¹ ∉ S := by
  induction L with
  | zero =>
      refine ⟨[], Nat.zero_le _, ?_⟩
      intro m hm
      simp at hm
  | succ L ih =>
      obtain ⟨ms, hlen, hdeep⟩ := ih
      obtain ⟨m, -, h1, h2⟩ := exists_deep_pow hinj hS 0
      refine ⟨m :: ms, ?_, ?_⟩
      · rw [List.length_cons]
        omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨h1, h2⟩
        · exact hdeep x hx'

/-! ## Both free clauses, certified -/

/-- **A base spelling of `t⁻¹` exists**, the alphabet being a generating
set. -/
theorem exists_base_spelling (A : HullGeneratingSet G) {N : Subgroup G}
    (E : HypEmbeddedCore A N) (t : G) :
    ∃ p : List G, (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ := by
  obtain ⟨l, hl⟩ := exists_isWord A.alphabet.symmetricGenerating t⁻¹
  refine ⟨l, ?_, hl.prod_eq⟩
  intro g hg
  rw [E.base_eq]
  exact hl.letters g hg

/-- **Arbitrarily long lists of deep exponents for Hull's relator exist.**  The
relative ball is finite because `H` is hyperbolically embedded, and `E.lox` has
infinite order because it is loxodromic. -/
theorem exists_deep_relator_exponents {A : HullGeneratingSet G}
    {N : Subgroup G} (E : HypEmbeddedCore A N) (rho L : ℕ) :
    ∃ ms : List ℕ, L ≤ ms.length ∧ ∀ m ∈ ms,
      E.lox ^ m ∉ E.rel.relBall () rho ∧
        (E.lox ^ m)⁻¹ ∉ E.rel.relBall () rho :=
  exists_deep_exponents
    (injective_pow_of_not_isOfFinOrder
      (not_isOfFinOrder_of_isLoxodromic E.lox_isLoxodromic))
    (E.embedded.locallyFinite () rho) L

/-! ## Hull's §6, reduced to the separation -/

/-- **Olshanskii's separation for Hull's relator, and nothing else.**

> Let `G` be acylindrically hyperbolic with Hull's alphabet `A`, let `N` be
> suitable, let `H ≤ N` be hyperbolically embedded with the loxodromic element
> `h`, let `t ∈ G` and let `ε, ρ` be given.  Then there is a constant `B` such
> that for every length `L` there are a base spelling `p` of `t⁻¹` and at least
> `L` deep exponents `m₁, …, m_k` for which every `ε`-match of a prefix longer
> than `B`, between two members of the symmetrized closure of
> `p · h^{m₁} ⋯ h^{m_k}`, is a global translation of the member.

The quantifier order is the content: `B` is produced **before** `L`, so it does
not grow with the relator, and that is what lets `μ` be met by taking the
relator long.  Everything else `RelatorChoice` asks for is proved in
`relatorChoice_of_relatorSeparation`, and `exists_base_spelling` with
`exists_deep_relator_exponents` shows the clauses other than the separation can
always be met. -/
def RelatorSeparation : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
    (E : HypEmbeddedCore A N), Suitable A.alphabet N → ∀ (t : G) (eps rho : ℕ),
      ∃ B : ℕ, ∀ L : ℕ, ∃ (p : List G) (ms : List ℕ),
        (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ ∧ L ≤ ms.length ∧
          (∀ m ∈ ms, E.lox ^ m ∉ E.rel.relBall () rho ∧
            (E.lox ^ m)⁻¹ ∉ E.rel.relBall () rho) ∧
          ∀ w w' u₀ u₀' : List (GGT.RelLetter G Unit),
            RelWord.Sym (relatorWord p E.lox ms) w →
              RelWord.Sym (relatorWord p E.lox ms) w' →
                (∃ s, w = u₀ ++ s) → (∃ s', w' = u₀' ++ s') → B < u₀.length →
                  ∀ y z : G, wordNorm E.rel.base y ≤ eps →
                    wordNorm E.rel.base z ≤ eps →
                      GGT.RelLetter.listVal u₀'
                          = y * GGT.RelLetter.listVal u₀ * z →
                        GGT.RelLetter.listVal w'
                          = y * GGT.RelLetter.listVal w * y⁻¹

/-- **Hull's §6 from the separation.**  The relator is written down, so `u`,
admissibility, depth, length and `μ` are all discharged here; only the
separation is passed through. -/
theorem relatorChoice_of_relatorSeparation (h : RelatorSeparation.{u}) :
    RelatorChoice.{u} := by
  intro G _ A N E hN t eps rho mu hmu
  obtain ⟨B, hB⟩ := h A N E hN t eps rho
  obtain ⟨n, hn⟩ := exists_nat_gt ((B : ℝ) / mu)
  obtain ⟨p, ms, hpbase, hpprod, hlen, hdeep, hsep⟩ := hB (max rho n)
  have hBL : (B : ℝ) < mu * (max rho n : ℕ) := by
    have h1 : (B : ℝ) < (n : ℝ) * mu := (div_lt_iff₀ hmu).mp hn
    have h2 : (n : ℝ) ≤ ((max rho n : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_max_right rho n
    have h3 : (n : ℝ) * mu ≤ ((max rho n : ℕ) : ℝ) * mu :=
      mul_le_mul_of_nonneg_right h2 (le_of_lt hmu)
    calc (B : ℝ) < (n : ℝ) * mu := h1
      _ ≤ ((max rho n : ℕ) : ℝ) * mu := h3
      _ = mu * ((max rho n : ℕ) : ℝ) := mul_comm _ _
  have hlenv : max rho n ≤ (relatorWord p E.lox ms).length := by
    rw [length_relatorWord]
    omega
  refine ⟨E.lox ^ ms.sum, E.le (E.H.pow_mem E.lox_mem ms.sum),
    relatorWord p E.lox ms, B, ?_, ?_, ?_, ?_, ?_, hsep⟩
  · rw [listVal_relatorWord, hpprod]
  · intro x hx
    rcases mem_relatorWord hx with ⟨g, hg, rfl⟩ | ⟨m, _, rfl⟩
    · exact hpbase g hg
    · show E.lox ^ m ∈ E.rel.fam ()
      have hfam : E.rel.fam () = E.H := by rw [E.fam_eq]
      rw [hfam]
      exact E.H.pow_mem E.lox_mem m
  · have h1 : rho ≤ max rho n := Nat.le_max_left rho n
    omega
  · intro x hx lam hcomp
    rcases mem_relatorWord hx with ⟨g, _, rfl⟩ | ⟨m, hm, rfl⟩
    · exact False.elim hcomp
    · exact hdeep m hm
  · have h2 : ((max rho n : ℕ) : ℝ) ≤ ((relatorWord p E.lox ms).length : ℝ) := by
      exact_mod_cast hlenv
    have h3 : mu * ((max rho n : ℕ) : ℝ)
        ≤ mu * ((relatorWord p E.lox ms).length : ℝ) :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hmu)
    linarith

/-- **Hull's §6 in the form Theorem 5.1 consumes it**, from the separation. -/
theorem hullRelatorStatement_of_relatorSeparation (h : RelatorSeparation.{u}) :
    HullRelatorStatement.{u} :=
  hullRelatorStatement_of_relatorChoice (relatorChoice_of_relatorSeparation h)

end HullSC
end GroupApproximation

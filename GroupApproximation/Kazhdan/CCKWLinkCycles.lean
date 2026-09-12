import GroupApproximation.GGT.SystolicDefs
import GroupApproximation.Kazhdan.CCKWLinkGirthTyped

/-!
# Short cycles in the links of a typed triangle complex

The coset complex of a triangle of groups `H : Fin 3 → Subgroup G` has vertices of three
types, and a group element `k` lies on the vertex `gHᵢ` when `k ∈ gHᵢ`.  Everything the link
of a vertex needs from that complex is recorded in `TypedPoints`: the three vertices of a
triangle have pairwise distinct types and a common point, two points on one vertex differ
by an element of its vertex group, and two vertices of one type with a common point are
equal.

`linkCycles_of_typedPoints` shows that a cycle of length `3 ≤ n < 8` in the link of a vertex
`v` of type `i` (neighbours of `v`, joined when they span a triangle with `v`) gives an
alternating relation between the edge groups `Hᵢ ⊓ Hⱼ` and `Hᵢ ⊓ Hₖ`: the types of the cycle
alternate between `j` and `k`, so `n` is even, and the quotients of consecutive common points
are nontrivial and multiply to `1`.  Over the typed girths `6, 8, 8` of `GHB(7)`
(`Kazhdan/CCKWLinkGirthTyped.lean`) no such cycle exists below length `6` at type `0` or below
length `8` at types `1`, `2` (`linkCycles_ghb7`).
-/

namespace GroupApproximation
namespace KMSGroup
namespace CCKW

/-- The first edge type at a vertex of type `i`, in the order of `CCKWLinkGirths`. -/
def aType : Fin 3 → Fin 3 := ![1, 0, 0]

/-- The second edge type at a vertex of type `i`, in the order of `CCKWLinkGirths`. -/
def bType : Fin 3 → Fin 3 := ![2, 2, 1]

variable {G : Type*} [Group G] {V : Type*}

/-- **Typed points on a triangle complex**: vertex types in `Fin 3`, and a relation `On k x`
saying that the group element `k` lies on the vertex `x`. -/
structure TypedPoints (X : Systolic.TriangleComplex V) (H : Fin 3 → Subgroup G) where
  type : V → Fin 3
  On : G → V → Prop
  tri : ∀ {x y z : V}, X.Tri x y z →
    type x ≠ type y ∧ type y ≠ type z ∧ type x ≠ type z ∧ ∃ k : G, On k x ∧ On k y ∧ On k z
  mem_of_on : ∀ {k k' : G} {x : V}, On k x → On k' x → k⁻¹ * k' ∈ H (type x)
  on_eq : ∀ {k : G} {x y : V}, On k x → On k y → type x = type y → x = y

/-! ## Types along a link cycle -/

theorem types_cycle3 : ∀ i t₀ t₁ t₂ : Fin 3, i ≠ t₀ → t₀ ≠ t₁ → i ≠ t₁ → t₁ ≠ t₂ → i ≠ t₂ →
    t₂ = t₀ := by
  decide +kernel

theorem types_cycle4 : ∀ i t₀ t₁ t₂ t₃ : Fin 3, i ≠ t₀ → t₀ ≠ t₁ → i ≠ t₁ → t₁ ≠ t₂ →
    i ≠ t₂ → t₂ ≠ t₃ → i ≠ t₃ → t₃ ≠ t₀ → t₂ = t₀ ∧ t₃ = t₁ := by
  decide +kernel

theorem types_cycle5 : ∀ i t₀ t₁ t₂ t₃ t₄ : Fin 3, i ≠ t₀ → t₀ ≠ t₁ → i ≠ t₁ → t₁ ≠ t₂ →
    i ≠ t₂ → t₂ ≠ t₃ → i ≠ t₃ → t₃ ≠ t₄ → i ≠ t₄ → t₄ = t₀ := by
  decide +kernel

theorem types_cycle6 : ∀ i t₀ t₁ t₂ t₃ t₄ t₅ : Fin 3, i ≠ t₀ → t₀ ≠ t₁ → i ≠ t₁ → t₁ ≠ t₂ →
    i ≠ t₂ → t₂ ≠ t₃ → i ≠ t₃ → t₃ ≠ t₄ → i ≠ t₄ → t₄ ≠ t₅ → i ≠ t₅ → t₅ ≠ t₀ →
    t₂ = t₀ ∧ t₄ = t₀ ∧ t₃ = t₁ ∧ t₅ = t₁ := by
  decide +kernel

theorem types_cycle7 : ∀ i t₀ t₁ t₂ t₃ t₄ t₅ t₆ : Fin 3, i ≠ t₀ → t₀ ≠ t₁ → i ≠ t₁ →
    t₁ ≠ t₂ → i ≠ t₂ → t₂ ≠ t₃ → i ≠ t₃ → t₃ ≠ t₄ → i ≠ t₄ → t₄ ≠ t₅ → i ≠ t₅ → t₅ ≠ t₆ →
    i ≠ t₆ → t₆ = t₀ := by
  decide +kernel

theorem types_ab : ∀ i t₀ t₁ : Fin 3, i ≠ t₀ → t₀ ≠ t₁ → i ≠ t₁ →
    (t₁ = aType i ∧ t₀ = bType i) ∨ (t₁ = bType i ∧ t₀ = aType i) := by
  decide +kernel

/-! ## Quotients of common points -/

theorem factor_mem {X : Systolic.TriangleComplex V} {H : Fin 3 → Subgroup G}
    (T : TypedPoints X H) {k k' : G} {v x : V} (hkv : T.On k v) (hk'v : T.On k' v)
    (hkx : T.On k x) (hk'x : T.On k' x) : k⁻¹ * k' ∈ H (T.type v) ⊓ H (T.type x) :=
  Subgroup.mem_inf.mpr ⟨T.mem_of_on hkv hk'v, T.mem_of_on hkx hk'x⟩

theorem factor_ne_one {X : Systolic.TriangleComplex V} {H : Fin 3 → Subgroup G}
    (T : TypedPoints X H) {k k' : G} {x y : V} (hkx : T.On k x) (hk'y : T.On k' y)
    (hxy : x ≠ y) (ht : T.type x = T.type y) : k⁻¹ * k' ≠ 1 := by
  intro h
  rw [inv_mul_eq_one] at h
  subst h
  exact hxy (T.on_eq hkx hk'y ht)

/-! ## Link cycles give alternating relations -/

/-- **A short link cycle gives an alternating relation.** -/
theorem linkCycles_of_typedPoints {X : Systolic.TriangleComplex V} {H : Fin 3 → Subgroup G}
    (T : TypedPoints X H) (girth : Fin 3 → ℕ) (hle : ∀ i, girth i ≤ 8)
    (hg : ∀ i, LinkGirthAtLeast (H i ⊓ H (aType i)) (H i ⊓ H (bType i)) (girth i))
    (v : V) (c : List V) (h3 : 3 ≤ c.length) (hlt : c.length < girth (T.type v))
    (hnd : c.Nodup) (hch : List.IsChain (X.Tri v) (c ++ c.take 1)) : False := by
  rcases c with _ | ⟨x₀, _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, _ | ⟨x₄, _ | ⟨x₅, _ | ⟨x₆, _ | ⟨x₇, c⟩⟩⟩⟩⟩⟩⟩⟩
  · simp at h3
  · simp at h3
  · simp at h3
  · -- length three: four pairwise distinct types
    have hch' : List.IsChain (X.Tri v) [x₀, x₁, x₂, x₀] := by simpa using hch
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch'
    obtain ⟨T01, T12, T20⟩ := hch'
    obtain ⟨hv0, h01, hv1, -⟩ := T.tri T01
    obtain ⟨-, h12, hv2, -⟩ := T.tri T12
    obtain ⟨-, h20, -, -⟩ := T.tri T20
    exact h20 (types_cycle3 _ _ _ _ hv0 h01 hv1 h12 hv2)
  · -- length four: an alternating relation of length four
    have hch' : List.IsChain (X.Tri v) [x₀, x₁, x₂, x₃, x₀] := by simpa using hch
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch'
    obtain ⟨T01, T12, T23, T30⟩ := hch'
    obtain ⟨hv0, h01, hv1, k₁, hk₁v, hk₁0, hk₁1⟩ := T.tri T01
    obtain ⟨-, h12, hv2, k₂, hk₂v, hk₂1, hk₂2⟩ := T.tri T12
    obtain ⟨-, h23, hv3, k₃, hk₃v, hk₃2, hk₃3⟩ := T.tri T23
    obtain ⟨-, h30, -, k₄, hk₄v, hk₄3, hk₄0⟩ := T.tri T30
    obtain ⟨ht2, ht3⟩ := types_cycle4 _ _ _ _ _ hv0 h01 hv1 h12 hv2 h23 hv3 h30
    have hnd02 : x₀ ≠ x₂ := by rintro rfl; simp at hnd
    have hnd13 : x₁ ≠ x₃ := by rintro rfl; simp at hnd
    have hf₁ := factor_mem T hk₁v hk₂v hk₁1 hk₂1
    have hf₂ := factor_mem T hk₂v hk₃v hk₂2 hk₃2
    have hf₃ := factor_mem T hk₃v hk₄v hk₃3 hk₄3
    have hf₄ := factor_mem T hk₄v hk₁v hk₄0 hk₁0
    have hn₁ := factor_ne_one T hk₁0 hk₂2 hnd02 ht2.symm
    have hn₂ := factor_ne_one T hk₂1 hk₃3 hnd13 ht3.symm
    have hn₃ := factor_ne_one T hk₃2 hk₄0 hnd02.symm ht2
    have hn₄ := factor_ne_one T hk₄3 hk₁1 hnd13.symm ht3
    simp only [List.length_cons, List.length_nil] at hlt
    have hrel := hg (T.type v) 2 (by omega) (by omega)
    rcases types_ab _ _ _ hv0 h01 hv1 with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · rw [ha] at hf₁
      rw [ht3, ha] at hf₃
      rw [ht2, hb] at hf₂
      rw [hb] at hf₄
      exact hrel ![k₁⁻¹ * k₂, k₃⁻¹ * k₄] ![k₂⁻¹ * k₃, k₄⁻¹ * k₁]
        (by intro j; fin_cases j <;> assumption) (by intro j; fin_cases j <;> assumption)
        (by intro j; fin_cases j <;> assumption) (by intro j; fin_cases j <;> assumption)
        (by simp [List.ofFn_succ, mul_assoc])
    · rw [hb] at hf₁
      rw [ht3, hb] at hf₃
      rw [ht2, ha] at hf₂
      rw [ha] at hf₄
      exact hrel ![k₂⁻¹ * k₃, k₄⁻¹ * k₁] ![k₃⁻¹ * k₄, k₁⁻¹ * k₂]
        (by intro j; fin_cases j <;> assumption) (by intro j; fin_cases j <;> assumption)
        (by intro j; fin_cases j <;> assumption) (by intro j; fin_cases j <;> assumption)
        (by simp [List.ofFn_succ, mul_assoc])
  · -- length five: an odd cycle cannot alternate between two types
    have hch' : List.IsChain (X.Tri v) [x₀, x₁, x₂, x₃, x₄, x₀] := by simpa using hch
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch'
    obtain ⟨T01, T12, T23, T34, T40⟩ := hch'
    obtain ⟨hv0, h01, hv1, -⟩ := T.tri T01
    obtain ⟨-, h12, hv2, -⟩ := T.tri T12
    obtain ⟨-, h23, hv3, -⟩ := T.tri T23
    obtain ⟨-, h34, hv4, -⟩ := T.tri T34
    obtain ⟨-, h40, -, -⟩ := T.tri T40
    exact h40 (types_cycle5 _ _ _ _ _ _ hv0 h01 hv1 h12 hv2 h23 hv3 h34 hv4)
  · -- length six: an alternating relation of length six
    have hch' : List.IsChain (X.Tri v) [x₀, x₁, x₂, x₃, x₄, x₅, x₀] := by simpa using hch
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch'
    obtain ⟨T01, T12, T23, T34, T45, T50⟩ := hch'
    obtain ⟨hv0, h01, hv1, k₁, hk₁v, hk₁0, hk₁1⟩ := T.tri T01
    obtain ⟨-, h12, hv2, k₂, hk₂v, hk₂1, hk₂2⟩ := T.tri T12
    obtain ⟨-, h23, hv3, k₃, hk₃v, hk₃2, hk₃3⟩ := T.tri T23
    obtain ⟨-, h34, hv4, k₄, hk₄v, hk₄3, hk₄4⟩ := T.tri T34
    obtain ⟨-, h45, hv5, k₅, hk₅v, hk₅4, hk₅5⟩ := T.tri T45
    obtain ⟨-, h50, -, k₆, hk₆v, hk₆5, hk₆0⟩ := T.tri T50
    obtain ⟨ht2, ht4, ht3, ht5⟩ :=
      types_cycle6 _ _ _ _ _ _ _ hv0 h01 hv1 h12 hv2 h23 hv3 h34 hv4 h45 hv5 h50
    have hnd02 : x₀ ≠ x₂ := by rintro rfl; simp at hnd
    have hnd13 : x₁ ≠ x₃ := by rintro rfl; simp at hnd
    have hnd24 : x₂ ≠ x₄ := by rintro rfl; simp at hnd
    have hnd35 : x₃ ≠ x₅ := by rintro rfl; simp at hnd
    have hnd40 : x₄ ≠ x₀ := by rintro rfl; simp at hnd
    have hnd51 : x₅ ≠ x₁ := by rintro rfl; simp at hnd
    have hf₁ := factor_mem T hk₁v hk₂v hk₁1 hk₂1
    have hf₂ := factor_mem T hk₂v hk₃v hk₂2 hk₃2
    have hf₃ := factor_mem T hk₃v hk₄v hk₃3 hk₄3
    have hf₄ := factor_mem T hk₄v hk₅v hk₄4 hk₅4
    have hf₅ := factor_mem T hk₅v hk₆v hk₅5 hk₆5
    have hf₆ := factor_mem T hk₆v hk₁v hk₆0 hk₁0
    have hn₁ := factor_ne_one T hk₁0 hk₂2 hnd02 ht2.symm
    have hn₂ := factor_ne_one T hk₂1 hk₃3 hnd13 ht3.symm
    have hn₃ := factor_ne_one T hk₃2 hk₄4 hnd24 (ht2.trans ht4.symm)
    have hn₄ := factor_ne_one T hk₄3 hk₅5 hnd35 (ht3.trans ht5.symm)
    have hn₅ := factor_ne_one T hk₅4 hk₆0 hnd40 ht4
    have hn₆ := factor_ne_one T hk₆5 hk₁1 hnd51 ht5
    simp only [List.length_cons, List.length_nil] at hlt
    have hrel := hg (T.type v) 3 (by omega) (by omega)
    rcases types_ab _ _ _ hv0 h01 hv1 with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · rw [ha] at hf₁
      rw [ht3, ha] at hf₃
      rw [ht5, ha] at hf₅
      rw [ht2, hb] at hf₂
      rw [ht4, hb] at hf₄
      rw [hb] at hf₆
      exact hrel ![k₁⁻¹ * k₂, k₃⁻¹ * k₄, k₅⁻¹ * k₆] ![k₂⁻¹ * k₃, k₄⁻¹ * k₅, k₆⁻¹ * k₁]
        (by intro j; fin_cases j <;> assumption) (by intro j; fin_cases j <;> assumption)
        (by intro j; fin_cases j <;> assumption) (by intro j; fin_cases j <;> assumption)
        (by simp [List.ofFn_succ, mul_assoc])
    · rw [hb] at hf₁
      rw [ht3, hb] at hf₃
      rw [ht5, hb] at hf₅
      rw [ht2, ha] at hf₂
      rw [ht4, ha] at hf₄
      rw [ha] at hf₆
      exact hrel ![k₂⁻¹ * k₃, k₄⁻¹ * k₅, k₆⁻¹ * k₁] ![k₃⁻¹ * k₄, k₅⁻¹ * k₆, k₁⁻¹ * k₂]
        (by intro j; fin_cases j <;> assumption) (by intro j; fin_cases j <;> assumption)
        (by intro j; fin_cases j <;> assumption) (by intro j; fin_cases j <;> assumption)
        (by simp [List.ofFn_succ, mul_assoc])
  · -- length seven: an odd cycle cannot alternate between two types
    have hch' : List.IsChain (X.Tri v) [x₀, x₁, x₂, x₃, x₄, x₅, x₆, x₀] := by simpa using hch
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch'
    obtain ⟨T01, T12, T23, T34, T45, T56, T60⟩ := hch'
    obtain ⟨hv0, h01, hv1, -⟩ := T.tri T01
    obtain ⟨-, h12, hv2, -⟩ := T.tri T12
    obtain ⟨-, h23, hv3, -⟩ := T.tri T23
    obtain ⟨-, h34, hv4, -⟩ := T.tri T34
    obtain ⟨-, h45, hv5, -⟩ := T.tri T45
    obtain ⟨-, h56, hv6, -⟩ := T.tri T56
    obtain ⟨-, h60, -, -⟩ := T.tri T60
    exact h60 (types_cycle7 _ _ _ _ _ _ _ _ hv0 h01 hv1 h12 hv2 h23 hv3 h34 hv4 h45 hv5 h56 hv6)
  · -- length at least eight exceeds every girth bound
    simp only [List.length_cons] at hlt
    have := hle (T.type v)
    omega

/-! ## `GHB(7)` -/

/-- The typed link girths of `GHB(7)` in the edge-type order of `aType`, `bType`. -/
theorem typedLinkGirths [Finite (U3 7)] [Finite (U4 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
    (h4 : Nat.card (U4 7) ≤ 7 ^ 4) (i : Fin 3) :
    LinkGirthAtLeast (vertexGroup i ⊓ vertexGroup (aType i)) (vertexGroup i ⊓ vertexGroup (bType i))
      (if i = 0 then 6 else 8) := by
  obtain ⟨h0, h1, h2⟩ := cckwLinkGirths h3 h4
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **No short link cycles in a typed triangle complex over `GHB(7)`**: below length `6` at
type `0`, below length `8` at types `1` and `2`. -/
theorem linkCycles_ghb7 [Finite (U3 7)] [Finite (U4 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
    (h4 : Nat.card (U4 7) ≤ 7 ^ 4) {X : Systolic.TriangleComplex V}
    (T : TypedPoints X vertexGroup) (v : V) (c : List V) (h3c : 3 ≤ c.length)
    (hlt : c.length < if T.type v = 0 then 6 else 8) (hnd : c.Nodup)
    (hch : List.IsChain (X.Tri v) (c ++ c.take 1)) : False :=
  linkCycles_of_typedPoints T (fun i => if i = 0 then 6 else 8) (by decide +kernel)
    (typedLinkGirths h3 h4) v c h3c hlt hnd hch

end CCKW
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.CCKW.linkCycles_of_typedPoints
#audit_axioms GroupApproximation.KMSGroup.CCKW.typedLinkGirths
#audit_axioms GroupApproximation.KMSGroup.CCKW.linkCycles_ghb7

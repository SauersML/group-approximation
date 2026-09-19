import GroupApproximation.GGT.HullSCRelatorSeparationComponent

/-!
# The base spelling may be taken long, which is what separates the two runs

Osin's isolated-component bound says a deep component of a quasi-geodesic
polygon is connected to some *other* component of the polygon -- possibly to
another component of its own side.  For Hull's relator that possibility is
concrete: a rotation of `p · h^{m₁} ⋯ h^{m_k}` splits the run in two, a tail at
the start and a head at the end, with the whole of `p` between them
(`GGT/HullSCRelatorSeparationComponent.lean` shows the `H`-letters form one run,
so a rotation carries at most two), and nothing so far stops those two from
being connected to each other.

The exclusion is a counting argument and it costs the design nothing.  If two
components of one side at index distance `d` are connected then their initial
vertices differ by an element of `H`, so they are at distance at most one in
`Γ(G, X ⊔ H)`; against a `(mu, b)`-quasi-geodesic side that forces
`d / mu - b ≤ 1`, i.e. `d ≤ mu * (1 + b)`.  So it is enough that the two runs be
more than `mu * (1 + b)` letters apart, and they are separated by the whole of
`p`.

`exists_long_base_spelling` is the freedom that makes this available: the base
spelling of `t⁻¹` may be taken as long as wanted, by padding with `g, g⁻¹` for
any letter `g` of the base.  `exists_mem_base` supplies such a letter, from
suitability: a suitable subgroup contains a loxodromic element, a loxodromic
element has infinite order and so is not the identity, and a nonidentity element
has a nonempty spelling.

The counting argument itself needs the relative metric and the quasi-geodesicity
of the relator, neither of which is in the repository: `RelWord.IsSmallCancellation`
has six clauses -- admissible, closure under inversion and rotation, length,
depth and small pieces -- and none of them is a quasi-geodesicity clause.  So
quasi-geodesicity is a separate input, carried as an explicit binder by whoever
assembles the estimate.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Spacing

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **The base of the core has a letter.**

Suitability gives a loxodromic element of `N`; a loxodromic element has infinite
order, so it is not the identity; and a nonidentity element has a nonempty
spelling over a generating set, whose first letter is the letter wanted. -/
theorem exists_mem_base (E : HypEmbeddedCore A N) (hN : Suitable A.alphabet N) :
    ∃ g : G, g ∈ E.rel.base := by
  obtain ⟨g, _hgN, _h, _hhN, hg, _hh, _hind⟩ := hN.actsNonElementarily
  have hg1 : g ≠ 1 := by
    intro h1
    refine not_isOfFinOrder_of_isLoxodromic hg ?_
    rw [h1]
    exact IsOfFinOrder.one
  obtain ⟨l, hl⟩ := exists_isWord A.alphabet.symmetricGenerating g
  cases l with
  | nil =>
      exfalso
      refine hg1 ?_
      rw [← hl.prod_eq, List.prod_nil]
  | cons b t =>
      refine ⟨b, ?_⟩
      rw [E.base_eq]
      exact hl.letters b (List.mem_cons.mpr (Or.inl rfl))

/-- **The base spelling of `t⁻¹` may be taken arbitrarily long.**

Padding with `g, g⁻¹` changes neither the element spelled nor the legality of
the letters, the base being symmetric, and it lengthens the spelling by two.  So
the length of the base part of Hull's relator is a free parameter of the
construction, and can be taken past any bound the geometry names -- in
particular past `mu * (1 + b)`, which is what keeps the two runs of a rotation
from being connected to each other. -/
theorem exists_long_base_spelling (E : HypEmbeddedCore A N)
    (hN : Suitable A.alphabet N) (t : G) (P : ℕ) :
    ∃ p : List G, P ≤ p.length ∧ (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ := by
  obtain ⟨g, hg⟩ := exists_mem_base E hN
  have hginv : g⁻¹ ∈ E.rel.base := by
    rw [E.base_eq] at hg ⊢
    exact A.alphabet.symmetricGenerating.inv_mem g hg
  obtain ⟨p₀, hp₀base, hp₀prod⟩ := exists_base_spelling A E t
  induction P with
  | zero => exact ⟨p₀, Nat.zero_le _, hp₀base, hp₀prod⟩
  | succ P ih =>
      obtain ⟨p, hlen, hbase, hprod⟩ := ih
      refine ⟨g :: g⁻¹ :: p, ?_, ?_, ?_⟩
      · rw [List.length_cons, List.length_cons]
        omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx1
        · exact hg
        · rcases List.mem_cons.mp hx1 with rfl | hx2
          · exact hginv
          · exact hbase x hx2
      · rw [List.prod_cons, List.prod_cons, hprod]
        exact mul_inv_cancel_left g t⁻¹

/-- **The relator can be taken long in its base part and long in its run at
once.**  The two clauses of the estimate that ask for length -- `rho ≤ |v|` and
`B < mu |v|` -- are met by either part, and the spacing argument asks for the
base part specifically. -/
theorem exists_long_spelling_and_exponents (E : HypEmbeddedCore A N)
    (hN : Suitable A.alphabet N) (t : G) (P rho eps L : ℕ) :
    ∃ (p : List G) (ms : List ℕ), P ≤ p.length ∧
      (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ ∧ L ≤ ms.length ∧ ms.Nodup ∧
      (∀ m ∈ ms, E.lox ^ m ∉ E.rel.relBall () rho ∧
        (E.lox ^ m)⁻¹ ∉ E.rel.relBall () rho) := by
  obtain ⟨p, hplen, hpbase, hpprod⟩ := exists_long_base_spelling E hN t P
  obtain ⟨ms, hlen, hnodup, hdeep, -⟩ :=
    exists_separated_relator_exponents E rho eps L
  exact ⟨p, ms, hplen, hpbase, hpprod, hlen, hnodup, hdeep⟩

end Spacing

end HullSC
end GroupApproximation

import GroupApproximation.GGT.HullSCRelatorSeparation2Design

/-!
# Block rigidity over two subgroups

The design of `GGT/HullSCRelatorSeparation2Design.lean`, instantiated at the
relative balls of a hyperbolically embedded family indexed by `Bool`, and the
two rigidity statements it buys.

A matched pair of blocks is a matched pair of components of the *same* index --
Osin's connectedness relates components of one `H_λ` only -- so both rigidity
statements are stated at a fixed index `s`, and no cross-subgroup clause enters.
That is the point of the alternation: over `Λ = Bool` each block letter is its
own component (`HullSC.isComp_relatorWord₂`), so the per-letter matching that the
`Λ = Unit` model put out of reach is reachable, and these are the statements
that consume it.

The geometric input is the same one as before, at a fixed index: an `eps`-match
between two deep blocks places the two conjugators in `H_s`.  Everything else is
proved.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u

section Rigid

variable {G : Type u} [Group G]

/-- **The exponent design at the relative balls of the family.**

`K` is the union of the two depth balls and `T` the union of the two
`eps`-balls; both are finite because the family is hyperbolically embedded, and
a separation against the larger union is a separation against each. -/
theorem exists_separated_relator_exponents₂ {D : GGT.RelGenSet G Bool}
    (hemb : D.IsHyperbolicallyEmbedded) {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (rho eps L : ℕ) :
    ∃ ms : List ℕ, L ≤ ms.length ∧ ms.Nodup ∧
      (∀ m ∈ ms, ∀ s : Bool, a s ^ m ∉ D.relBall s rho ∧
        (a s ^ m)⁻¹ ∉ D.relBall s rho) ∧
      ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ s : Bool, ∀ x ∈ D.relBall s eps,
        ∀ x' ∈ D.relBall s eps,
          x * a s ^ i * x' ≠ a s ^ j ∧ x * a s ^ i * x' ≠ (a s ^ j)⁻¹ := by
  obtain ⟨ms, hlen, hnodup, hdeep, hsep⟩ :=
    exists_separated_exponents_family hinj
      ((hemb.locallyFinite false rho).union (hemb.locallyFinite true rho))
      ((hemb.locallyFinite false eps).union (hemb.locallyFinite true eps)) L
  refine ⟨ms, hlen, hnodup, ?_, ?_⟩
  · intro m hm s
    have h := hdeep m hm s
    cases s with
    | false =>
        exact ⟨fun hc => h.1 (Set.mem_union_left _ hc),
          fun hc => h.2 (Set.mem_union_left _ hc)⟩
    | true =>
        exact ⟨fun hc => h.1 (Set.mem_union_right _ hc),
          fun hc => h.2 (Set.mem_union_right _ hc)⟩
  · intro i hi j hj hij s x hx x' hx'
    have hxT : x ∈ D.relBall false eps ∪ D.relBall true eps := by
      cases s with
      | false => exact Set.mem_union_left _ hx
      | true => exact Set.mem_union_right _ hx
    have hx'T : x' ∈ D.relBall false eps ∪ D.relBall true eps := by
      cases s with
      | false => exact Set.mem_union_left _ hx'
      | true => exact Set.mem_union_right _ hx'
    exact hsep i hi j hj hij s x hxT x' hx'T

/-- **Matched blocks of one subgroup carry equal exponents.**

The geometric input places the conjugators in `H_s`;
`HullSC.mem_relBall_of_wordNorm_le` places them in the relative `eps`-ball,
which the exponents were designed against. -/
theorem exponent_eq_of_blockMatch₂ {D : GGT.RelGenSet G Bool}
    (hbase : IsSymmetricGeneratingSet D.base) {a : Bool → G} {eps rho : ℕ}
    {ms : List ℕ} {s : Bool}
    (hgeo : ∀ (i j : ℕ) (x x' : G), wordNorm D.base x ≤ eps →
      wordNorm D.base x' ≤ eps → a s ^ i ∉ D.relBall s rho →
        a s ^ j ∉ D.relBall s rho → x * a s ^ i * x' = a s ^ j →
          x ∈ D.fam s ∧ x' ∈ D.fam s)
    (hdeep : ∀ m ∈ ms, ∀ t : Bool, a t ^ m ∉ D.relBall t rho ∧
      (a t ^ m)⁻¹ ∉ D.relBall t rho)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {i j : ℕ} (hi : i ∈ ms) (hj : j ∈ ms) {x x' : G}
    (hx : wordNorm D.base x ≤ eps) (hx' : wordNorm D.base x' ≤ eps)
    (heq : x * a s ^ i * x' = a s ^ j) : i = j := by
  by_contra hij
  obtain ⟨hxf, hx'f⟩ :=
    hgeo i j x x' hx hx' (hdeep i hi s).1 (hdeep j hj s).1 heq
  exact (hsep i hi j hj hij s x (mem_relBall_of_wordNorm_le hbase hxf hx) x'
    (mem_relBall_of_wordNorm_le hbase hx'f hx')).1 heq

/-- **Mirrored matched blocks of one subgroup carry equal exponents.**

The case a prefix matched against the formal inverse produces, where the
alignment reads `x · h_s^i · x' = (h_s^j)⁻¹`.  As over one subgroup, the design
forbids it for `i ≠ j` only: at `i = j` it is the genuine global translation. -/
theorem exponent_eq_of_mirroredBlockMatch₂ {D : GGT.RelGenSet G Bool}
    (hbase : IsSymmetricGeneratingSet D.base) {a : Bool → G} {eps rho : ℕ}
    {ms : List ℕ} {s : Bool}
    (hgeoInv : ∀ (i j : ℕ) (x x' : G), wordNorm D.base x ≤ eps →
      wordNorm D.base x' ≤ eps → a s ^ i ∉ D.relBall s rho →
        (a s ^ j)⁻¹ ∉ D.relBall s rho → x * a s ^ i * x' = (a s ^ j)⁻¹ →
          x ∈ D.fam s ∧ x' ∈ D.fam s)
    (hdeep : ∀ m ∈ ms, ∀ t : Bool, a t ^ m ∉ D.relBall t rho ∧
      (a t ^ m)⁻¹ ∉ D.relBall t rho)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {i j : ℕ} (hi : i ∈ ms) (hj : j ∈ ms) {x x' : G}
    (hx : wordNorm D.base x ≤ eps) (hx' : wordNorm D.base x' ≤ eps)
    (heq : x * a s ^ i * x' = (a s ^ j)⁻¹) : i = j := by
  by_contra hij
  obtain ⟨hxf, hx'f⟩ :=
    hgeoInv i j x x' hx hx' (hdeep i hi s).1 (hdeep j hj s).2 heq
  exact (hsep i hi j hj hij s x (mem_relBall_of_wordNorm_le hbase hxf hx) x'
    (mem_relBall_of_wordNorm_le hbase hx'f hx')).2 heq

end Rigid

end HullSC
end GroupApproximation

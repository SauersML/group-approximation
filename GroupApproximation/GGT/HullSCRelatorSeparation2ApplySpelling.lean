import GroupApproximation.GGT.HullSCRelatorSeparation2Core
import GroupApproximation.GGT.HullSCRelatorSeparationSpacing

/-!
# The base part, over either core

`HullSC.exists_long_base_spelling` is stated over `HullSC.HypEmbeddedCore`, the
one-subgroup core with `Λ = Unit`, and the two-subgroup chain needs it over
`HullSC.HypEmbeddedCore₂`.  Rather than transcribe it, the three lemmas it rests
on are restated over the only thing they use: that the relative generating set's
base IS Hull's alphabet.  Both cores carry that as a field, so both instantiate,
and the `Λ = Unit` originals are left alone.

## Why the composition wants this

`B` is chosen after `t` and before the length `L` the exponent list is asked
for, and the piece hypothesis is `B < |u₀|`.  For that to put a block letter
inside the matched prefix, `B` has to be past `|p|` --- otherwise a piece can lie
wholly inside the base arc, where `HullSC.exists_block_of_long_prefix_rotate`
has nothing to say.  So `p` must be fixed BEFORE `B`, at a length that does not
grow with `L`; padding it to length one for `0 < |p|` is all the rest of the
chain wants, and `exists_long_base_spelling₂` at `P := 1` is what supplies it.

The `Λ = Unit` statement cannot be used for that: its `E` is the wrong core.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Spelling

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **The base has a letter**, from suitability alone.

`HullSC.exists_mem_base` over any relative generating set whose base is Hull's
alphabet: suitability gives a loxodromic element of `N`, a loxodromic element
has infinite order and so is not the identity, and a nonidentity element has a
nonempty spelling whose first letter is the one wanted. -/
theorem exists_mem_base_of_base_eq {Λ : Type w} {D : GGT.RelGenSet G Λ}
    (hbase : D.base = A.alphabet.carrier) (hN : Suitable A.alphabet N) :
    ∃ g : G, g ∈ D.base := by
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
      rw [hbase]
      exact hl.letters b (List.mem_cons.mpr (Or.inl rfl))

/-- **`t⁻¹` has a base spelling.** -/
theorem exists_base_spelling_of_base_eq {Λ : Type w} {D : GGT.RelGenSet G Λ}
    (hbase : D.base = A.alphabet.carrier) (t : G) :
    ∃ p : List G, (∀ g ∈ p, g ∈ D.base) ∧ p.prod = t⁻¹ := by
  obtain ⟨l, hl⟩ := exists_isWord A.alphabet.symmetricGenerating t⁻¹
  refine ⟨l, ?_, hl.prod_eq⟩
  intro g hg
  rw [hbase]
  exact hl.letters g hg

/-- **The base spelling of `t⁻¹` may be taken arbitrarily long**, by padding
with a letter and its inverse. -/
theorem exists_long_base_spelling_of_base_eq {Λ : Type w}
    {D : GGT.RelGenSet G Λ} (hbase : D.base = A.alphabet.carrier)
    (hN : Suitable A.alphabet N) (t : G) (P : ℕ) :
    ∃ p : List G, P ≤ p.length ∧ (∀ g ∈ p, g ∈ D.base) ∧ p.prod = t⁻¹ := by
  obtain ⟨g, hg⟩ := exists_mem_base_of_base_eq hbase hN
  have hginv : g⁻¹ ∈ D.base := by
    rw [hbase] at hg ⊢
    exact A.alphabet.symmetricGenerating.inv_mem g hg
  obtain ⟨p₀, hp₀base, hp₀prod⟩ := exists_base_spelling_of_base_eq hbase t
  induction P with
  | zero => exact ⟨p₀, Nat.zero_le _, hp₀base, hp₀prod⟩
  | succ P ih =>
      obtain ⟨p, hlen, hpbase, hprod⟩ := ih
      refine ⟨g :: g⁻¹ :: p, ?_, ?_, ?_⟩
      · rw [List.length_cons, List.length_cons]
        omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx1
        · exact hg
        · rcases List.mem_cons.mp hx1 with rfl | hx2
          · exact hginv
          · exact hpbase x hx2
      · rw [List.prod_cons, List.prod_cons, hprod]
        exact mul_inv_cancel_left g t⁻¹

/-- **The two-subgroup core's base part, as long as wanted.**  This is the form
the composition takes it in: `p` is chosen once, at `P := 1`, before `B`. -/
theorem exists_long_base_spelling₂ (E : HypEmbeddedCore₂ A N)
    (hN : Suitable A.alphabet N) (t : G) (P : ℕ) :
    ∃ p : List G, P ≤ p.length ∧ (∀ g ∈ p, g ∈ E.rel.base) ∧ p.prod = t⁻¹ :=
  exists_long_base_spelling_of_base_eq E.base_eq hN t P

end Spelling

end HullSC
end GroupApproximation

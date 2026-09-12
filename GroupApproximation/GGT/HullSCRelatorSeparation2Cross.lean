import GroupApproximation.GGT.HullSCRelatorSeparation2Rigid

/-!
# Depth across the two subgroups, and what it excludes

The design of `GGT/HullSCRelatorSeparation2Design.lean` is built by avoiding the
**union** of the two depth balls, and
`HullSC.exists_separated_relator_exponents₂` then weakens the deep clause to one
index at a time, because that is all the rigidity lemmas ask for.  The
unweakened form costs nothing and excludes something the weakened one does not:
that a deep power of one of the two elements lies in the *other* subgroup.

`mem_relBall_one_of_mem_fam_ne` is the reason.  An element of `H_μ` that also
lies in `H_λ`, for `μ ≠ λ`, is spelled by the single letter `comp μ` -- an
admissible letter which never traverses an edge of `Γ_{H λ}`, since its index is
not `λ` -- so it sits in the d̂_λ-ball of radius one.  That ball is finite,
because the family is hyperbolically embedded, and the design avoids it.

`notMem_fam_of_crossDeep` is the consequence, and it is what discharges the
same-side exclusion for *adjacent* components of the alternating relator: two
consecutive component starts of one index are separated by a single block letter
of the other index, and that letter is a deep power, so the element joining them
is not in the subgroup.  Non-adjacent starts are joined by an alternating
product of deep powers, which this argument does not reach.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u w

section Cross

variable {G : Type u} [Group G] {Λ : Type w}

/-- **An element in two members of the family is at d̂-distance one.**

Its one-letter spelling in the other index is admissible and traverses no edge
of `Γ_{H λ}`, an index other than `λ` never doing so. -/
theorem mem_relBall_one_of_mem_fam_ne {D : GGT.RelGenSet G Λ} {lam mu : Λ}
    (hne : mu ≠ lam) {x : G} (hxmu : x ∈ D.fam mu) (hxlam : x ∈ D.fam lam) :
    x ∈ D.relBall lam 1 := by
  rw [GGT.RelGenSet.mem_relBall]
  refine ⟨hxlam, [GGT.RelLetter.comp mu x], ?_, ?_, ?_, ?_⟩
  · intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact hxmu
  · show GGT.RelLetter.listVal [GGT.RelLetter.comp mu x] = x
    simp [GGT.RelLetter.listVal, GGT.RelLetter.val]
  · refine ⟨?_, trivial⟩
    rintro ⟨hc, -⟩
    exact hne hc
  · simp

end Cross

section CrossBool

variable {G : Type u} [Group G]

/-- **A deep power of one element is not in the other subgroup.**

This is the adjacent case of the same-side exclusion: what joins two
consecutive component starts of index `lam` in the alternating relator is one
block letter of index `!lam`, and a deep power is not in `H_lam`. -/
theorem notMem_fam_of_crossDeep {D : GGT.RelGenSet G Bool} {a : Bool → G}
    {m rho : ℕ} (hrho : 1 ≤ rho) {lam : Bool}
    (hpow : a (!lam) ^ m ∈ D.fam (!lam))
    (hdeep : a (!lam) ^ m ∉ D.relBall lam rho) :
    a (!lam) ^ m ∉ D.fam lam := by
  intro hmem
  refine hdeep (relBall_mono hrho ?_)
  refine mem_relBall_one_of_mem_fam_ne ?_ hpow hmem
  cases lam <;> simp

/-- **The exponent design, with the deep clause kept across indices.**

The construction of `HullSC.exists_separated_relator_exponents₂` verbatim,
except that the deep clause is not weakened: the exponents are chosen against
the union of the two depth balls, so a deep power of either element misses the
depth ball of **either** index.  The separation clause is per index, as before,
because that is what a matched pair of components asks for. -/
theorem exists_separated_relator_exponents₂_cross {D : GGT.RelGenSet G Bool}
    (hemb : D.IsHyperbolicallyEmbedded) {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (rho eps L : ℕ) :
    ∃ ms : List ℕ, L ≤ ms.length ∧ ms.Nodup ∧
      (∀ m ∈ ms, ∀ s t : Bool, a s ^ m ∉ D.relBall t rho ∧
        (a s ^ m)⁻¹ ∉ D.relBall t rho) ∧
      ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ s : Bool, ∀ x ∈ D.relBall s eps,
        ∀ x' ∈ D.relBall s eps,
          x * a s ^ i * x' ≠ a s ^ j ∧ x * a s ^ i * x' ≠ (a s ^ j)⁻¹ := by
  obtain ⟨ms, hlen, hnodup, hdeep, hsep⟩ :=
    exists_separated_exponents_family hinj
      ((hemb.locallyFinite false rho).union (hemb.locallyFinite true rho))
      ((hemb.locallyFinite false eps).union (hemb.locallyFinite true eps)) L
  refine ⟨ms, hlen, hnodup, ?_, ?_⟩
  · intro m hm s t
    have h := hdeep m hm s
    cases t with
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

end CrossBool

end HullSC
end GroupApproximation

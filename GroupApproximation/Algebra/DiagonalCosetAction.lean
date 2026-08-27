import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The diagonal-coset splitting of a coset action

The elementary core of the commuting-sofic-actions counterexample — the part
its route calls "coset bookkeeping in `G × G`".  For a group `G` and a
subgroup `H ≤ G`, the left action of `G × G` on `X = (G × G)/ΔH` restricts to
two commuting coordinate actions of `G` that are **free for every `H`**, while
the diagonal copy of `G` cuts out an orbit canonically isomorphic to the coset
`G`-set `G/H`, with the base coset stabilized by exactly `H`.

Feeding a sofic `G` with a nonsofic coset action `G ↷ G/H` (Kun–Thom,
arXiv:2608.06222) through this construction answers Question 4.2 of
Gao–Kunnawalkam Elayavalli–Patchell (arXiv:2401.04945) in the negative: two
commuting sofic actions whose combination is not sofic.  The soficity
transfers themselves (their Theorem 2.14, Propositions 2.15 and 2.16) are
cited external inputs, not formalized; this file certifies every
group-theoretic step of the construction.  Graph nodes:
`research/nonsofic-orbit-forces-commuting-counterexample.md` (statement),
`research/diagonal-coset-commuting-counterexample-proof.md` (route),
`research/commuting-sofic-actions-need-not-combine.md` (the answered
question).

## What is proved

* `eq_one_of_fst_smul_fixed`, `eq_one_of_snd_smul_fixed` — both coordinate
  actions of `G` on `(G × G) ⧸ diagSubgroup H` are free, for **every**
  subgroup `H`: a diagonal element with one trivial coordinate is trivial.
* `fst_smul_snd_smul`, `snd_smul_fst_smul`, `fst_smul_snd_smul_comm` — the
  two coordinate actions commute, and their combination is the full left
  `G × G`-action.
* `diagOrbitMap` — the map `gH ↦ (g, g)ΔH`, a `G`-equivariant injection
  (`diagOrbitMap_injective`, `diagOrbitMap_smul`) whose range is exactly the
  orbit of the base coset under the diagonal copy of `G`
  (`mem_range_diagOrbitMap`).
* `diag_smul_base_eq_base_iff` — the stabilizer of the base coset in the
  diagonal copy of `G` is exactly `H`.
-/

namespace DiagonalCosetAction

variable {G : Type*} [Group G] (H : Subgroup G)

/-- `ΔH ≤ G × G`, the diagonal copy of the subgroup `H`. -/
def diagSubgroup : Subgroup (G × G) :=
  H.map ((MonoidHom.id G).prod (MonoidHom.id G))

theorem mem_diagSubgroup {p : G × G} :
    p ∈ diagSubgroup H ↔ ∃ h ∈ H, ((h, h) : G × G) = p := by
  simp only [diagSubgroup, Subgroup.mem_map, MonoidHom.prod_apply, MonoidHom.id_apply]

/-- The first-coordinate action of `G` on `(G × G)/ΔH` is free, for every
subgroup `H`: a diagonal element whose second coordinate is trivial is
trivial.  This is why the subgroup never obstructs the coordinate actions. -/
theorem eq_one_of_fst_smul_fixed {g : G} {x : (G × G) ⧸ diagSubgroup H}
    (hfix : ((g, 1) : G × G) • x = x) : g = 1 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hfix
  obtain ⟨h, -, heq⟩ := (mem_diagSubgroup H).mp hfix
  simp only [Prod.mk_mul_mk, one_mul, Prod.inv_mk, inv_mul_cancel,
    Prod.mk.injEq] at heq
  obtain ⟨h1, h2⟩ := heq
  rw [h2] at h1
  have hga : g * a = a := inv_mul_eq_one.mp h1.symm
  exact mul_right_cancel (show g * a = 1 * a by rw [one_mul, hga])

/-- The second-coordinate action of `G` on `(G × G)/ΔH` is free, for every
subgroup `H`. -/
theorem eq_one_of_snd_smul_fixed {g : G} {x : (G × G) ⧸ diagSubgroup H}
    (hfix : ((1, g) : G × G) • x = x) : g = 1 := by
  obtain ⟨⟨a, b⟩, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hfix
  obtain ⟨h, -, heq⟩ := (mem_diagSubgroup H).mp hfix
  simp only [Prod.mk_mul_mk, one_mul, Prod.inv_mk, inv_mul_cancel,
    Prod.mk.injEq] at heq
  obtain ⟨h1, h2⟩ := heq
  rw [h1] at h2
  have hgb : g * b = b := inv_mul_eq_one.mp h2.symm
  exact mul_right_cancel (show g * b = 1 * b by rw [one_mul, hgb])

/-- Acting by `(g, 1)` and then `(1, k)` is acting by `(g, k)`: the two
coordinate actions combine to the full left `G × G`-action. -/
theorem fst_smul_snd_smul (g k : G) (x : (G × G) ⧸ diagSubgroup H) :
    ((g, 1) : G × G) • ((1, k) : G × G) • x = ((g, k) : G × G) • x := by
  rw [smul_smul, Prod.mk_mul_mk, mul_one, one_mul]

/-- The same in the other order. -/
theorem snd_smul_fst_smul (g k : G) (x : (G × G) ⧸ diagSubgroup H) :
    ((1, k) : G × G) • ((g, 1) : G × G) • x = ((g, k) : G × G) • x := by
  rw [smul_smul, Prod.mk_mul_mk, one_mul, mul_one]

/-- The two coordinate actions commute. -/
theorem fst_smul_snd_smul_comm (g k : G) (x : (G × G) ⧸ diagSubgroup H) :
    ((g, 1) : G × G) • ((1, k) : G × G) • x
      = ((1, k) : G × G) • ((g, 1) : G × G) • x := by
  rw [fst_smul_snd_smul, snd_smul_fst_smul]

/-- `gH ↦ (g, g)ΔH`: the canonical map from the coset space `G/H` onto the
diagonal orbit inside `(G × G)/ΔH`. -/
def diagOrbitMap (x : G ⧸ H) : (G × G) ⧸ diagSubgroup H :=
  Quotient.liftOn' x
    (fun g => (QuotientGroup.mk (g, g) : (G × G) ⧸ diagSubgroup H))
    (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab
      exact QuotientGroup.eq.mpr ((mem_diagSubgroup H).mpr
        ⟨a⁻¹ * b, hab, by simp only [Prod.inv_mk, Prod.mk_mul_mk]⟩))

@[simp] theorem diagOrbitMap_mk (g : G) :
    diagOrbitMap H (QuotientGroup.mk g) = QuotientGroup.mk (g, g) := rfl

/-- The diagonal-orbit map is injective: distinct cosets of `H` land in
distinct cosets of `ΔH`. -/
theorem diagOrbitMap_injective : Function.Injective (diagOrbitMap H) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [diagOrbitMap_mk, diagOrbitMap_mk, QuotientGroup.eq] at hxy
  obtain ⟨h, hh, heq⟩ := (mem_diagSubgroup H).mp hxy
  simp only [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk.injEq] at heq
  rw [QuotientGroup.eq]
  rw [heq.1] at hh
  exact hh

/-- The diagonal-orbit map is equivariant for the identification of `G` with
the diagonal subgroup of `G × G`. -/
theorem diagOrbitMap_smul (k : G) (x : G ⧸ H) :
    diagOrbitMap H (k • x) = ((k, k) : G × G) • diagOrbitMap H x := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, diagOrbitMap_mk, diagOrbitMap_mk,
    MulAction.Quotient.smul_mk, smul_eq_mul, Prod.mk_mul_mk]

/-- The range of the diagonal-orbit map is exactly the orbit of the base
coset under the diagonal copy of `G`. -/
theorem mem_range_diagOrbitMap (y : (G × G) ⧸ diagSubgroup H) :
    y ∈ Set.range (diagOrbitMap H) ↔
      ∃ g : G,
        ((g, g) : G × G) • (QuotientGroup.mk 1 : (G × G) ⧸ diagSubgroup H)
          = y := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨a, ?_⟩
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, diagOrbitMap_mk]
  · rintro ⟨g, rfl⟩
    refine ⟨QuotientGroup.mk g, ?_⟩
    rw [diagOrbitMap_mk, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

/-- Under the identification of `G` with the diagonal subgroup of `G × G`,
the stabilizer of the base coset of `(G × G)/ΔH` is exactly `H`.  Together
with `diagOrbitMap`, this is the statement that the diagonal orbit is the
coset `G`-set `G/H`. -/
theorem diag_smul_base_eq_base_iff (g : G) :
    ((g, g) : G × G) • (QuotientGroup.mk 1 : (G × G) ⧸ diagSubgroup H)
        = QuotientGroup.mk 1
      ↔ g ∈ H := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq,
    mul_one, mem_diagSubgroup]
  constructor
  · rintro ⟨h, hh, heq⟩
    simp only [Prod.inv_mk, Prod.mk.injEq] at heq
    rw [heq.1] at hh
    simpa using H.inv_mem hh
  · intro hg
    exact ⟨g⁻¹, H.inv_mem hg, by simp only [Prod.inv_mk]⟩

end DiagonalCosetAction

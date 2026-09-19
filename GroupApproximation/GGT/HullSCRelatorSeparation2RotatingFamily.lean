import GroupApproximation.GGT.HullSCRelatorSeparation2ConeOffSpace
import GroupApproximation.GGT.HullSCRotatingFamily

/-!
# The rotating family of a family of subgroups

`HullSC.apexRot` assigns to a point the conjugates of one subgroup `K` by the
elements carrying one apex `c₀` to it.  Over a family the apices are the union
of the orbits, and the assignment has to pick the subgroup by index.

`apexRotFamily` is that assignment, and `isRotatingFamily_apexRotFamily` proves
Dahmani--Guirardel--Osin's three axioms for it.  Two hypotheses are spent, and
each exactly once:

* `hnorm` -- each `K lam` is normal in the stabiliser of its own apex -- makes
  the union a subgroup, as over one subgroup.
* `hne` -- the orbits of distinct apices do not meet -- makes the assignment
  **well posed**.  Without it a point in two orbits would carry two different
  rotation subgroups, and `mul_mem'` would have to multiply an element of
  `g (K lam) g⁻¹` by one of `g' (K mu) g'⁻¹` with no relation between them.
  It is spent in `mul_mem'` and nowhere else, which is the precise sense in
  which a family costs more than a single subgroup.

Neither hypothesis is derivable from the other clauses: `hne` in particular does
not follow from separation, which speaks only of apices already known to differ.
It is a field of `HullSC.ConeOffData₂` for that reason.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry

universe u v w

section Family

variable {G : Type u} [Group G] {X : Type v} [MulAction G X] {Λ : Type w}

/-- **The apices of a family**: the union of the orbits of the individual
apices. -/
def apexOrbitFamily (c₀ : Λ → X) : Set X :=
  {x | ∃ (lam : Λ) (g : G), g • c₀ lam = x}

theorem mem_apexOrbitFamily {c₀ : Λ → X} {x : X} :
    x ∈ apexOrbitFamily (G := G) c₀ ↔ ∃ (lam : Λ) (g : G), g • c₀ lam = x :=
  Iff.rfl

theorem apex_mem_apexOrbitFamily (c₀ : Λ → X) (lam : Λ) :
    c₀ lam ∈ apexOrbitFamily (G := G) c₀ :=
  ⟨lam, 1, one_smul G (c₀ lam)⟩

/-- **The rotation subgroup at an apex of the family.**  The conjugates of
`K lam` by the elements carrying `c₀ lam` to the point, over every index, and
the identity.

That the union is a subgroup is where `hnorm` is spent; that the index is
determined by the point, so that the two factors of a product come from one and
the same `K lam`, is where `hne` is spent. -/
def apexRotFamily (K : Λ → Subgroup G) (c₀ : Λ → X)
    (hnorm : ∀ (lam : Λ) (s : G), s • c₀ lam = c₀ lam →
      ∀ k ∈ K lam, s * k * s⁻¹ ∈ K lam)
    (hne : ∀ lam mu : Λ, lam ≠ mu → ∀ g g' : G, g • c₀ lam ≠ g' • c₀ mu)
    (x : X) : Subgroup G where
  carrier := {h : G | (∃ (lam : Λ) (g : G), g • c₀ lam = x ∧
      ∃ k ∈ K lam, h = g * k * g⁻¹) ∨ h = 1}
  one_mem' := Or.inr rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨lam, g, hg, k, hk, rfl⟩ | rfl
    · rcases hb with ⟨mu, g', hg', k', hk', rfl⟩ | rfl
      · have hlm : lam = mu := by
          by_contra hlm
          exact hne lam mu hlm g g' (hg.trans hg'.symm)
        have hg'' : g' • c₀ lam = x := by
          rw [hlm]
          exact hg'
        have hk'' : k' ∈ K lam := by
          rw [hlm]
          exact hk'
        have hs : (g⁻¹ * g') • c₀ lam = c₀ lam := by
          rw [mul_smul, hg'', ← hg, ← mul_smul, inv_mul_cancel, one_smul]
        have hk2 : (g⁻¹ * g') * k' * (g⁻¹ * g')⁻¹ ∈ K lam :=
          hnorm lam _ hs k' hk''
        refine Or.inl ⟨lam, g, hg, k * ((g⁻¹ * g') * k' * (g⁻¹ * g')⁻¹),
          mul_mem hk hk2, ?_⟩
        group
      · rw [mul_one]
        exact Or.inl ⟨lam, g, hg, k, hk, rfl⟩
    · rw [one_mul]
      exact hb
  inv_mem' := by
    intro a ha
    rcases ha with ⟨lam, g, hg, k, hk, rfl⟩ | rfl
    · refine Or.inl ⟨lam, g, hg, k⁻¹, inv_mem hk, ?_⟩
      group
    · rw [inv_one]
      exact Or.inr rfl

theorem mem_apexRotFamily {K : Λ → Subgroup G} {c₀ : Λ → X}
    {hnorm : ∀ (lam : Λ) (s : G), s • c₀ lam = c₀ lam →
      ∀ k ∈ K lam, s * k * s⁻¹ ∈ K lam}
    {hne : ∀ lam mu : Λ, lam ≠ mu → ∀ g g' : G, g • c₀ lam ≠ g' • c₀ mu}
    {x : X} {h : G} :
    h ∈ apexRotFamily K c₀ hnorm hne x ↔
      (∃ (lam : Λ) (g : G), g • c₀ lam = x ∧ ∃ k ∈ K lam, h = g * k * g⁻¹) ∨
        h = 1 := Iff.rfl

end Family

/-! ## The three axioms, for a family -/

/-- **The union of the orbits, with the conjugates of the fixing subgroups, is a
rotating family.**  Invariance and equivariance are formal; the fixing axiom is
that each `K lam` fixes its own apex. -/
theorem isRotatingFamily_apexRotFamily {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {Λ : Type w}
    (hiso : IsIsometricAction G X) (K : Λ → Subgroup G) (c₀ : Λ → X)
    (hfix : ∀ (lam : Λ), ∀ k ∈ K lam, k • c₀ lam = c₀ lam)
    (hnorm : ∀ (lam : Λ) (s : G), s • c₀ lam = c₀ lam →
      ∀ k ∈ K lam, s * k * s⁻¹ ∈ K lam)
    (hne : ∀ lam mu : Λ, lam ≠ mu → ∀ g g' : G, g • c₀ lam ≠ g' • c₀ mu) :
    IsRotatingFamily G X (apexOrbitFamily (G := G) c₀)
      (apexRotFamily K c₀ hnorm hne) where
  isometric := hiso
  apex_smul := by
    intro g x hx
    obtain ⟨lam, g₀, rfl⟩ := mem_apexOrbitFamily.mp hx
    exact mem_apexOrbitFamily.mpr ⟨lam, g * g₀, by rw [mul_smul]⟩
  rot_fix := by
    intro c _ h hh
    rcases mem_apexRotFamily.mp hh with ⟨lam, g, hg, k, hk, rfl⟩ | rfl
    · rw [← hg, ← mul_smul, inv_mul_cancel_right, mul_smul, hfix lam k hk]
    · exact one_smul G c
  rot_equivariant := by
    intro g c _ h
    constructor
    · intro hh
      rcases mem_apexRotFamily.mp hh with ⟨lam, g', hg', k, hk, rfl⟩ | rfl
      · refine mem_apexRotFamily.mpr (Or.inl ⟨lam, g⁻¹ * g', ?_, k, hk, ?_⟩)
        · rw [mul_smul, hg', ← mul_smul, inv_mul_cancel, one_smul]
        · group
      · rw [mul_one, inv_mul_cancel]
        exact mem_apexRotFamily.mpr (Or.inr rfl)
    · intro hh
      rcases mem_apexRotFamily.mp hh with ⟨lam, g', hg', k, hk, hEq⟩ | hEq
      · refine mem_apexRotFamily.mpr (Or.inl ⟨lam, g * g', ?_, k, hk, ?_⟩)
        · rw [mul_smul, hg']
        · have hh2 : h = g * (g' * k * g'⁻¹) * g⁻¹ := by
            rw [← hEq]
            group
          rw [hh2]
          group
      · refine mem_apexRotFamily.mpr (Or.inr ?_)
        have h1 : h = g * (g⁻¹ * h * g) * g⁻¹ := by group
        rw [hEq] at h1
        simpa using h1

end HullSC
end GroupApproximation

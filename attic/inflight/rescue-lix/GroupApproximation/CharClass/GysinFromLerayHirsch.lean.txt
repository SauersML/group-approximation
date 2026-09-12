import GroupApproximation.CharClass.ProjectiveSpaceRing
import GroupApproximation.Meta.AxiomGuard

/-!
# Gysin from Leray–Hirsch, above the hypothesis

The ring structure of `H^*(ℂP^n; K)` reduces, by `cupPowE_ne_zero`, to cupping
with the Euler class being an isomorphism in the right range.  This file derives
exactly that from Leray–Hirsch for the `ℂP^1`-bundle `P(L ⊕ 1)`, without
constructing the whole Gysin long exact sequence.

The derivation is short once the pieces are named.  `P(L ⊕ 1)` is covered by the
chart and the complement of the zero section, both of which retract onto the
base, meeting in the sphere bundle.  Where the sphere bundle is acyclic the
Mayer–Vietoris sequence makes the pair of restrictions

```text
H^k(P(L ⊕ 1))  →  H^k(X) ⊕ H^k(X)
```

bijective.  Leray–Hirsch writes the left side as `π^*a + (π^*b) ⌣ ξ`, and the
tautological class restricts to `0` on one piece and to `e` on the other, so in
those coordinates the pair of restrictions is `(a, b) ↦ (a, a + b ⌣ e)`.  A map
of that shape is bijective exactly when `⌣ e` is.

## The hypothesis

Everything above is packaged as `GysinData`, whose fields are the two
restrictions with their behaviour on `π^*` and on `ξ`, the bijectivity of the
pair, and Leray–Hirsch in the two statements `lh_surj` and `lh_uniq`.  Degrees
are written `n + 2` throughout rather than `n - 2`, so no truncated subtraction
and no degree transport appears anywhere in the file.

`GysinData` is what the Mayer–Vietoris ladder will produce once
`cc-cohom-api`'s `mvDelta_cup` and `mvExactZero` land; the point of stating it
separately is that everything above it is proved now.

## The coefficient ring

Generic in a commutative ring `K`, with `K` implicit throughout because the Euler class
`e : Hmod K X 2` determines it, so every `F₂` call site is byte-unchanged.  Nothing here
divides and nothing commutes two cup products: the one place the mod-2 source wrote a sum
for a difference (`neg_one_smul`, in the injectivity half) is true over any ring, so the
port is a substitution.  See `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory

noncomputable section

/-- **The input to the Gysin step.**  A `ℂP^1`-bundle `P → X` with its
tautological class, presented through the two retractions of the Gysin cover.

`rA` and `rB` are the restrictions to the chart and to the complement of the zero
section, each composed with the retraction onto `X`.  The tautological class
restricts to `0` on the first and to the Euler class on the second, which is what
`rA_taut` and `rB_taut` say. -/
structure GysinData {K : Type} [CommRing K] (X P : TopCat.{0}) (e : Hmod K X 2) where
  /-- The bundle projection. -/
  proj : P ⟶ X
  /-- The tautological degree-2 class of `P`. -/
  taut : Hmod K P 2
  /-- Restriction to the chart, retracted onto the base. -/
  rA : (k : ℕ) → Hmod K P k →+ Hmod K X k
  /-- Restriction to the complement of the zero section, retracted onto the base. -/
  rB : (k : ℕ) → Hmod K P k →+ Hmod K X k
  /-- Both pieces are sections of the projection. -/
  rA_pull : ∀ (k : ℕ) (a : Hmod K X k), rA k (pull proj k a) = a
  /-- Both pieces are sections of the projection. -/
  rB_pull : ∀ (k : ℕ) (a : Hmod K X k), rB k (pull proj k a) = a
  /-- The tautological class dies on the chart. -/
  rA_taut : ∀ (k : ℕ) (b : Hmod K X k), rA (k + 2) (cup (pull proj k b) taut) = 0
  /-- The tautological class restricts to the Euler class on the other piece. -/
  rB_taut : ∀ (k : ℕ) (b : Hmod K X k), rB (k + 2) (cup (pull proj k b) taut) = cup b e
  /-- **Mayer–Vietoris**, where the sphere bundle is acyclic: the pair of
  restrictions is bijective. -/
  pair_bijective : ∀ k : ℕ, Function.Bijective (fun z : Hmod K P k => (rA k z, rB k z))
  /-- **Leray–Hirsch**, spanning half. -/
  lh_surj : ∀ (n : ℕ) (z : Hmod K P (n + 2)),
      ∃ (a : Hmod K X (n + 2)) (b : Hmod K X n),
        z = pull proj (n + 2) a + cup (pull proj n b) taut
  /-- **Leray–Hirsch**, freeness half. -/
  lh_uniq : ∀ (n : ℕ) (a : Hmod K X (n + 2)) (b : Hmod K X n),
      pull proj (n + 2) a + cup (pull proj n b) taut = 0 → a = 0 ∧ b = 0

namespace GysinData

variable {K : Type} [CommRing K] {X P : TopCat.{0}} {e : Hmod K X 2}

/-- **Cupping with the Euler class is an isomorphism.**

In Leray–Hirsch coordinates the pair of restrictions is `(a, b) ↦ (a, a + b ⌣ e)`,
and a map of that shape is bijective exactly when `⌣ e` is.  This is the whole
content of the Gysin sequence that the ring structure of `ℂP^n` uses. -/
theorem bijective_cupRight (G : GysinData X P e) (n : ℕ) :
    Function.Bijective (cupRightE e n) := by
  constructor
  · -- injective
    have hzero : ∀ b : Hmod K X n, cup b e = 0 → b = 0 := by
      intro b hb
      have hA : G.rA (n + 2) (cup (pull G.proj n b) G.taut) = 0 := G.rA_taut n b
      have hB : G.rB (n + 2) (cup (pull G.proj n b) G.taut) = 0 := by
        rw [G.rB_taut n b, hb]
      have hpair : (fun z : Hmod K P (n + 2) => (G.rA (n + 2) z, G.rB (n + 2) z))
          (cup (pull G.proj n b) G.taut)
          = (fun z : Hmod K P (n + 2) => (G.rA (n + 2) z, G.rB (n + 2) z)) 0 := by
        show ((G.rA (n + 2) (cup (pull G.proj n b) G.taut),
            G.rB (n + 2) (cup (pull G.proj n b) G.taut)) :
              Hmod K X (n + 2) × Hmod K X (n + 2))
          = (G.rA (n + 2) 0, G.rB (n + 2) 0)
        rw [hA, hB, map_zero, map_zero]
      have hz : cup (pull G.proj n b) G.taut = 0 := (G.pair_bijective (n + 2)).1 hpair
      have h0 : pull G.proj (n + 2) 0 + cup (pull G.proj n b) G.taut = 0 := by
        rw [hz, pull_zero, add_zero]
      exact (G.lh_uniq n 0 b h0).2
    intro b b' hbb
    have h := hzero (b - b') (by
      have : cup (b - b') e = cup b e - cup b' e := by
        rw [sub_eq_add_neg, sub_eq_add_neg, cup_add_left]
        congr 1
        rw [← neg_one_smul K b', ← neg_one_smul K (cup b' e), cup_smul_left]
      rw [this]
      show cupRightE e n b - cupRightE e n b' = 0
      rw [hbb, sub_self])
    exact sub_eq_zero.mp h
  · -- surjective
    intro c
    obtain ⟨z, hz⟩ := (G.pair_bijective (n + 2)).2 ((0 : Hmod K X (n + 2)), c)
    obtain ⟨a, b, hab⟩ := G.lh_surj n z
    have hA : G.rA (n + 2) z = 0 := congrArg Prod.fst hz
    have hB : G.rB (n + 2) z = c := congrArg Prod.snd hz
    have ha : a = 0 := by
      rw [hab, map_add, G.rA_pull, G.rA_taut, add_zero] at hA
      exact hA
    refine ⟨b, ?_⟩
    show cup b e = c
    rw [← hB, hab, map_add, G.rB_pull, G.rB_taut, ha, zero_add]

end GysinData

/-! ## The ring of a space carrying such data -/

/-- **The cup powers of the Euler class never vanish**, in the range where the
Gysin data exists.  Same walk up the even degrees as `cupPowE_ne_zero`, but
taking the bijectivity directly rather than through a `GysinSequence`. -/
theorem cupPowE_ne_zero_of_bijective {K : Type} [CommRing K] {X : TopCat.{0}}
    {e : Hmod K X 2} (N : ℕ)
    (hbij : ∀ m : ℕ, m < N → Function.Bijective (cupRightE e (2 * m)))
    (hone : (one X : Hmod K X 0) ≠ 0) {m : ℕ} (hm : m ≤ N) : cupPowE e m ≠ 0 := by
  induction m with
  | zero => simpa using hone
  | succ m ih =>
    have hmN : m < N := by omega
    intro hcontra
    have hzero : cupPowE e m = 0 := by
      refine (hbij m hmN).1 ?_
      rw [cupRightE_cupPowE, hcontra, map_zero]
    exact ih (by omega) hzero

/-! Audited on every build: `#audit_axioms` prints the closure **and fails the build** if it
leaves the classical allowlist, which `#print axioms` does not. -/

#audit_axioms GysinData.bijective_cupRight

end

end CharClass
end GroupApproximation

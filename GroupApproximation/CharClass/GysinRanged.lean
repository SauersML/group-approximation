import GroupApproximation.CharClass.GysinFromLerayHirsch

/-!
# The Gysin step, one degree at a time

`GysinData.pair_bijective` asks for the pair of restrictions to be bijective in
*every* degree, and for the bundle the ring bootstrap actually uses it is not.
The intersection of the two pieces retracts onto the sphere bundle, which for the
tautological line over `ℂP^d` is `S^{2d+1}`; that has cohomology in degrees `0`
and `2d+1`, so the pair fails to be bijective at the bottom and at the top.

Nothing is lost, because the proof never needed all degrees.  `bijective_cupRight`
at degree `n` uses the pair only at `n + 2`, and `cupPowE_ne_zero_of_bijective`
needs degrees `2m` for `m < d`, so the pair is used only in degrees `2` through
`2d` — exactly the range where `S^{2d+1}` is acyclic.

So this file restates the step with its hypotheses spelled out at a single degree
rather than bundled into a structure.  `GysinData` is published and stays as it
is; `bijective_cupRight_of_pieces` is the form a consumer with a genuine bundle
can actually discharge.

## Main declarations

* `bijective_cupRight_of_pieces` — **the Gysin step at one degree**.
* `cupPowE_ne_zero_of_pieces` — the powers are nonzero, in the range.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace Gysin

open CategoryTheory

noncomputable section

variable {X P : TopCat.{0}} {e : Hmod2 X 2}

/-- **The Gysin step at one degree.**  Cupping with the Euler class is bijective on
`H^n(X)` as soon as the pair of restrictions is bijective on `H^{n+2}(P)` and
Leray–Hirsch holds in that degree.

This is `GysinData.bijective_cupRight` with the hypotheses named individually, so
that a consumer whose pair is bijective only in a range can still use it. -/
theorem bijective_cupRight_of_pieces (proj : P ⟶ X) (taut : Hmod2 P 2)
    (rA rB : (k : ℕ) → Hmod2 P k →+ Hmod2 X k)
    (rA_pull : ∀ (k : ℕ) (a : Hmod2 X k), rA k (pull proj k a) = a)
    (rB_pull : ∀ (k : ℕ) (a : Hmod2 X k), rB k (pull proj k a) = a)
    (rA_taut : ∀ (k : ℕ) (b : Hmod2 X k), rA (k + 2) (cup (pull proj k b) taut) = 0)
    (rB_taut : ∀ (k : ℕ) (b : Hmod2 X k),
      rB (k + 2) (cup (pull proj k b) taut) = cup b e)
    (n : ℕ)
    (hpair : Function.Bijective
      (fun z : Hmod2 P (n + 2) => (rA (n + 2) z, rB (n + 2) z)))
    (lh_surj : ∀ z : Hmod2 P (n + 2), ∃ (a : Hmod2 X (n + 2)) (b : Hmod2 X n),
      z = pull proj (n + 2) a + cup (pull proj n b) taut)
    (lh_uniq : ∀ (a : Hmod2 X (n + 2)) (b : Hmod2 X n),
      pull proj (n + 2) a + cup (pull proj n b) taut = 0 → a = 0 ∧ b = 0) :
    Function.Bijective (cupRightE e n) := by
  constructor
  · have hzero : ∀ b : Hmod2 X n, cup b e = 0 → b = 0 := by
      intro b hb
      have hA : rA (n + 2) (cup (pull proj n b) taut) = 0 := rA_taut n b
      have hB : rB (n + 2) (cup (pull proj n b) taut) = 0 := by
        rw [rB_taut n b, hb]
      have hpr : (fun z : Hmod2 P (n + 2) => (rA (n + 2) z, rB (n + 2) z))
          (cup (pull proj n b) taut)
          = (fun z : Hmod2 P (n + 2) => (rA (n + 2) z, rB (n + 2) z)) 0 := by
        show ((rA (n + 2) (cup (pull proj n b) taut),
            rB (n + 2) (cup (pull proj n b) taut)) :
              Hmod2 X (n + 2) × Hmod2 X (n + 2))
          = (rA (n + 2) 0, rB (n + 2) 0)
        rw [hA, hB, map_zero, map_zero]
      have hz : cup (pull proj n b) taut = 0 := hpair.1 hpr
      have h0 : pull proj (n + 2) 0 + cup (pull proj n b) taut = 0 := by
        rw [hz, pull_zero, add_zero]
      exact (lh_uniq 0 b h0).2
    intro b b' hbb
    have h := hzero (b - b') (by
      have hsub : cup (b - b') e = cup b e - cup b' e := by
        rw [sub_eq_add_neg, sub_eq_add_neg, cup_add_left]
        congr 1
        rw [← neg_one_smul (ZMod 2) b', ← neg_one_smul (ZMod 2) (cup b' e), cup_smul_left]
      rw [hsub]
      show cupRightE e n b - cupRightE e n b' = 0
      rw [hbb, sub_self])
    exact sub_eq_zero.mp h
  · intro c
    obtain ⟨z, hz⟩ := hpair.2 ((0 : Hmod2 X (n + 2)), c)
    obtain ⟨a, b, hab⟩ := lh_surj z
    have hA : rA (n + 2) z = 0 := congrArg Prod.fst hz
    have hB : rB (n + 2) z = c := congrArg Prod.snd hz
    have ha : a = 0 := by
      rw [hab, map_add, rA_pull, rA_taut, add_zero] at hA
      exact hA
    refine ⟨b, ?_⟩
    show cup b e = c
    rw [← hB, hab, map_add, rB_pull, rB_taut, ha, zero_add]

/-- **The powers of the Euler class are nonzero**, in the range where the pair of
restrictions is bijective.  The pair is needed only in degrees `2` through `2N`,
which for the tautological line over `ℂP^N` is exactly where the sphere bundle is
acyclic. -/
theorem cupPowE_ne_zero_of_pieces (proj : P ⟶ X) (taut : Hmod2 P 2)
    (rA rB : (k : ℕ) → Hmod2 P k →+ Hmod2 X k)
    (rA_pull : ∀ (k : ℕ) (a : Hmod2 X k), rA k (pull proj k a) = a)
    (rB_pull : ∀ (k : ℕ) (a : Hmod2 X k), rB k (pull proj k a) = a)
    (rA_taut : ∀ (k : ℕ) (b : Hmod2 X k), rA (k + 2) (cup (pull proj k b) taut) = 0)
    (rB_taut : ∀ (k : ℕ) (b : Hmod2 X k),
      rB (k + 2) (cup (pull proj k b) taut) = cup b e)
    (N : ℕ)
    (hpair : ∀ m : ℕ, m < N → Function.Bijective
      (fun z : Hmod2 P (2 * m + 2) => (rA (2 * m + 2) z, rB (2 * m + 2) z)))
    (lh_surj : ∀ (n : ℕ) (z : Hmod2 P (n + 2)),
      ∃ (a : Hmod2 X (n + 2)) (b : Hmod2 X n),
        z = pull proj (n + 2) a + cup (pull proj n b) taut)
    (lh_uniq : ∀ (n : ℕ) (a : Hmod2 X (n + 2)) (b : Hmod2 X n),
      pull proj (n + 2) a + cup (pull proj n b) taut = 0 → a = 0 ∧ b = 0)
    (hone : (one X) ≠ 0) {m : ℕ} (hm : m ≤ N) : cupPowE e m ≠ 0 :=
  cupPowE_ne_zero_of_bijective N
    (fun j hj => bijective_cupRight_of_pieces proj taut rA rB rA_pull rB_pull
      rA_taut rB_taut (2 * j) (hpair j hj) (lh_surj (2 * j)) (lh_uniq (2 * j)))
    hone hm

end

end Gysin
end CharClass
end GroupApproximation

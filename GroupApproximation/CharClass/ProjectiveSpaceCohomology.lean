import GroupApproximation.CharClass.CohomologyBasic

/-!
# `H^*(ℂP^n; F₂)` as a graded group, by Mayer–Vietoris

The cover of `ℂP^{d+1}` by the affine chart and the complement of a point has
pieces which are, up to homotopy, a point, `ℂP^d` and `S^{2d+1}`
(`CharClass/ProjectiveSpaceCover.lean`).  Feeding that into the mod-2
Mayer–Vietoris sequence and inducting on `d` gives

```text
H^k(ℂP^d; F₂) = F₂  for k = 2n with n ≤ d,     0 otherwise.
```

This file contains the whole of that argument **except** the construction of the
Mayer–Vietoris sequence itself, which is lane `cc-cohom-api`'s.  The sequence
enters as a `structure MVSequence`: five maps and three exactness statements, in
element form.  Nothing here is a `sorry` or an `axiom` — the results are
theorems about any space carrying such a structure, and the topological input is
supplied by instantiating it.

## The three ways the sequence is used

* `MVSequence.bijective_resV` — where the chart and the intersection both
  vanish, `H^k(X) ≅ H^k(V)`: this propagates `ℂP^d` up to `ℂP^{d+1}` in the
  middle degrees.
* `MVSequence.bijective_delta` — where `U` and `V` both vanish in two adjacent
  degrees, `δ : H^k(W) ≅ H^{k+1}(X)`: this creates the new top class
  `H^{2d+2}(ℂP^{d+1})` out of `H^{2d+1}(S^{2d+1})`.
* `MVSequence.eq_zero_of_delta` — the vanishing version of the same.

Degree `1` is the one place where the connecting map is not controlled by
vanishing: `H^0(W) ≠ 0`.  It is handled by the hypothesis `hres0`, that
restriction `H^0(U) → H^0(W)` is onto — true because both spaces are connected
and `1` restricts to `1` — which forces `δ` out of degree `0` to be zero.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory

/-- **Over `F₂` every additive map is linear**: the only scalars are `0` and `1`.
This is what lets the Mayer–Vietoris maps, which are additive by construction, be
turned into `ZMod 2`-linear equivalences. -/
def toLinearZMod2 {M N : Type} [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N] (f : M →+ N) : M →ₗ[ZMod 2] N where
  toFun := f
  map_add' := f.map_add
  map_smul' s a := by
    have hcase : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hcase s with rfl | rfl <;> simp

/-- A bijective additive map between `F₂`-modules is a linear equivalence. -/
noncomputable def linearEquivOfBijective {M N : Type} [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N] (f : M →+ N) (hf : Function.Bijective f) :
    M ≃ₗ[ZMod 2] N :=
  LinearEquiv.ofBijective (toLinearZMod2 f) hf

/-- **The mod-2 Mayer–Vietoris sequence of a two-piece cover, in element form.**
`X` is covered by `U` and `V` with intersection `W`; the maps are the four
restrictions and the connecting map, and the three `exact_*` fields are exactness
at `H^*(X)`, at `H^*(U) ⊕ H^*(V)` and at `H^*(W)`.  Mod 2 there are no signs, so
the difference map of the classical sequence is a sum. -/
structure MVSequence (X U V W : TopCat.{0}) where
  /-- Restriction `H^n(X) → H^n(U)`. -/
  resU : (n : ℕ) → Hmod2 X n →+ Hmod2 U n
  /-- Restriction `H^n(X) → H^n(V)`. -/
  resV : (n : ℕ) → Hmod2 X n →+ Hmod2 V n
  /-- Restriction `H^n(U) → H^n(W)`. -/
  resWU : (n : ℕ) → Hmod2 U n →+ Hmod2 W n
  /-- Restriction `H^n(V) → H^n(W)`. -/
  resWV : (n : ℕ) → Hmod2 V n →+ Hmod2 W n
  /-- The connecting map `H^n(W) → H^{n+1}(X)`. -/
  δ : (n : ℕ) → Hmod2 W n →+ Hmod2 X (n + 1)
  /-- Exactness at `H^{n+1}(X)`. -/
  exact_X : ∀ (n : ℕ) (x : Hmod2 X (n + 1)),
      (resU (n + 1) x = 0 ∧ resV (n + 1) x = 0) ↔ ∃ w, δ n w = x
  /-- Exactness at `H^n(U) ⊕ H^n(V)`. -/
  exact_sum : ∀ (n : ℕ) (a : Hmod2 U n) (b : Hmod2 V n),
      resWU n a = resWV n b ↔ ∃ x, resU n x = a ∧ resV n x = b
  /-- Exactness at `H^n(W)`. -/
  exact_W : ∀ (n : ℕ) (w : Hmod2 W n),
      δ n w = 0 ↔ ∃ (a : Hmod2 U n) (b : Hmod2 V n), resWU n a + resWV n b = w

namespace MVSequence

variable {X U V W : TopCat.{0}}

/-- **Propagation.**  When `H^{n+1}(U)`, `H^n(W)` and `H^{n+1}(W)` all vanish,
restriction to `V` is an isomorphism in degree `n+1`. -/
theorem bijective_resV (mv : MVSequence X U V W) (n : ℕ)
    (hU : ∀ a : Hmod2 U (n + 1), a = 0)
    (hWn : ∀ w : Hmod2 W n, w = 0)
    (hWn1 : ∀ w : Hmod2 W (n + 1), w = 0) :
    Function.Bijective (mv.resV (n + 1)) := by
  have hzero : ∀ z : Hmod2 X (n + 1), mv.resV (n + 1) z = 0 → z = 0 := by
    intro z hz
    obtain ⟨w, hw⟩ := (mv.exact_X n z).mp ⟨hU _, hz⟩
    rw [← hw, hWn w, map_zero]
  constructor
  · intro x y hxy
    have hx := hzero (x - y) (by rw [map_sub, hxy, sub_self])
    exact sub_eq_zero.mp hx
  · intro b
    obtain ⟨x, _, hx⟩ := (mv.exact_sum (n + 1) 0 b).mp
      (by rw [hWn1 (mv.resWU (n + 1) 0), hWn1 (mv.resWV (n + 1) b)])
    exact ⟨x, hx⟩

/-- **Creation.**  When `U` and `V` both vanish in degrees `n` and `n+1`, the
connecting map is an isomorphism `H^n(W) ≅ H^{n+1}(X)`. -/
theorem bijective_delta (mv : MVSequence X U V W) (n : ℕ)
    (hUn : ∀ a : Hmod2 U n, a = 0) (hVn : ∀ b : Hmod2 V n, b = 0)
    (hUn1 : ∀ a : Hmod2 U (n + 1), a = 0) (hVn1 : ∀ b : Hmod2 V (n + 1), b = 0) :
    Function.Bijective (mv.δ n) := by
  have hzero : ∀ z : Hmod2 W n, mv.δ n z = 0 → z = 0 := by
    intro z hz
    obtain ⟨a, b, hab⟩ := (mv.exact_W n z).mp hz
    rw [← hab, hUn a, hVn b, map_zero, map_zero, add_zero]
  constructor
  · intro w w' hww
    have hw := hzero (w - w') (by rw [map_sub, hww, sub_self])
    exact sub_eq_zero.mp hw
  · intro x
    exact (mv.exact_X n x).mp ⟨hUn1 (mv.resU (n + 1) x), hVn1 (mv.resV (n + 1) x)⟩

/-- **Vanishing.**  When `U` and `V` vanish in degree `n+1` and `W` vanishes in
degree `n`, so does `H^{n+1}(X)`. -/
theorem eq_zero_of_delta (mv : MVSequence X U V W) (n : ℕ)
    (hUn1 : ∀ a : Hmod2 U (n + 1), a = 0) (hVn1 : ∀ b : Hmod2 V (n + 1), b = 0)
    (hWn : ∀ w : Hmod2 W n, w = 0) (x : Hmod2 X (n + 1)) : x = 0 := by
  obtain ⟨w, hw⟩ := (mv.exact_X n x).mp ⟨hUn1 (mv.resU (n + 1) x), hVn1 (mv.resV (n + 1) x)⟩
  rw [← hw, hWn w, map_zero]

end MVSequence

/-! ## The three cohomology shapes that occur -/

/-- `X` has the mod-2 cohomology of a point. -/
def HasPointCohomology (X : TopCat.{0}) : Prop :=
  Nonempty (Hmod2 X 0 ≃ₗ[ZMod 2] ZMod 2) ∧ ∀ k : ℕ, k ≠ 0 → ∀ a : Hmod2 X k, a = 0

/-- `X` has the mod-2 cohomology of the sphere `S^m` (for `m ≠ 0`). -/
def HasSphereCohomology (X : TopCat.{0}) (m : ℕ) : Prop :=
  Nonempty (Hmod2 X 0 ≃ₗ[ZMod 2] ZMod 2) ∧
    Nonempty (Hmod2 X m ≃ₗ[ZMod 2] ZMod 2) ∧
    ∀ k : ℕ, k ≠ 0 → k ≠ m → ∀ a : Hmod2 X k, a = 0

/-- `X` has the mod-2 cohomology of `ℂP^d`: a line in each even degree up to
`2d`, and nothing else. -/
def HasCPCohomology (X : TopCat.{0}) (d : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ d → Nonempty (Hmod2 X (2 * n) ≃ₗ[ZMod 2] ZMod 2)) ∧
    ∀ k : ℕ, (∀ n : ℕ, n ≤ d → k ≠ 2 * n) → ∀ a : Hmod2 X k, a = 0

theorem HasPointCohomology.of_linearEquiv {X Y : TopCat.{0}}
    (e : ∀ k : ℕ, Hmod2 X k ≃ₗ[ZMod 2] Hmod2 Y k) (h : HasPointCohomology Y) :
    HasPointCohomology X :=
  ⟨⟨(e 0).trans h.1.some⟩, fun k hk a => by
    have := h.2 k hk (e k a)
    simpa using congrArg (e k).symm this⟩

theorem HasSphereCohomology.of_linearEquiv {X Y : TopCat.{0}} {m : ℕ}
    (e : ∀ k : ℕ, Hmod2 X k ≃ₗ[ZMod 2] Hmod2 Y k) (h : HasSphereCohomology Y m) :
    HasSphereCohomology X m :=
  ⟨⟨(e 0).trans h.1.some⟩, ⟨(e m).trans h.2.1.some⟩, fun k hk hm a => by
    have := h.2.2 k hk hm (e k a)
    simpa using congrArg (e k).symm this⟩

theorem HasCPCohomology.of_linearEquiv {X Y : TopCat.{0}} {d : ℕ}
    (e : ∀ k : ℕ, Hmod2 X k ≃ₗ[ZMod 2] Hmod2 Y k) (h : HasCPCohomology Y d) :
    HasCPCohomology X d :=
  ⟨fun n hn => ⟨(e (2 * n)).trans (h.1 n hn).some⟩, fun k hk a => by
    have := h.2 k hk (e k a)
    simpa using congrArg (e k).symm this⟩

/-! ## The inductive step -/

/-- **The Mayer–Vietoris step for complex projective space.**

If `X` is covered by an acyclic `U` and a `V` with the cohomology of `ℂP^d`,
meeting in a `W` with the cohomology of `S^{2d+1}`, and if `X` is connected and
`H^0(U) → H^0(W)` is onto, then `X` has the cohomology of `ℂP^{d+1}`.

The three degree ranges are: the old even classes `2n`, `1 ≤ n ≤ d`, which come
from `V` by `bijective_resV`; the new top class in degree `2d+2`, which comes
from `H^{2d+1}(W)` by `bijective_delta`; and everything else, which dies by
`eq_zero_of_delta`, except degree `1`, where the connecting map is killed by
`hres0` instead. -/
theorem hasCPCohomology_succ {X U V W : TopCat.{0}} (mv : MVSequence X U V W) (d : ℕ)
    (hU : HasPointCohomology U) (hV : HasCPCohomology V d)
    (hW : HasSphereCohomology W (2 * d + 1))
    (hres0 : Function.Surjective (mv.resWU 0))
    (h0 : Nonempty (Hmod2 X 0 ≃ₗ[ZMod 2] ZMod 2)) :
    HasCPCohomology X (d + 1) := by
  obtain ⟨hU0, hUz⟩ := hU
  obtain ⟨hVline, hVz⟩ := hV
  obtain ⟨hW0, hWtop, hWz⟩ := hW
  -- `V` has no odd cohomology, and none above `2d`.
  have hVodd : ∀ k : ℕ, k % 2 = 1 → ∀ b : Hmod2 V k, b = 0 := by
    intro k hk
    exact hVz k fun n _ => by omega
  have hVbig : ∀ k : ℕ, 2 * d < k → ∀ b : Hmod2 V k, b = 0 := by
    intro k hk
    exact hVz k fun n hn => by omega
  -- Degree `1` vanishes: the connecting map out of `H^0(W)` is zero.
  have hone : ∀ x : Hmod2 X 1, x = 0 := by
    intro x
    obtain ⟨w, hw⟩ := (mv.exact_X 0 x).mp
      ⟨hUz 1 one_ne_zero (mv.resU 1 x), hVodd 1 rfl (mv.resV 1 x)⟩
    obtain ⟨a, ha⟩ := hres0 w
    have hd : mv.δ 0 w = 0 := (mv.exact_W 0 w).mpr ⟨a, 0, by rw [ha, map_zero, add_zero]⟩
    rw [← hw, hd]
  refine ⟨?_, ?_⟩
  · -- the lines
    intro n hn
    match n, hn with
    | 0, _ => exact h0
    | (m + 1), hn =>
      rcases Nat.lt_or_ge m d with hmd | hmd
      · -- an old class, transported from `V`
        have hbij := mv.bijective_resV (2 * m + 1)
          (fun a => hUz (2 * m + 1 + 1) (by omega) a)
          (fun w => hWz (2 * m + 1) (by omega) (by omega) w)
          (fun w => hWz (2 * m + 1 + 1) (by omega) (by omega) w)
        exact ⟨(linearEquivOfBijective (mv.resV (2 * m + 1 + 1)) hbij).trans
          (hVline (m + 1) (by omega)).some⟩
      · -- the new top class
        have hmd' : m = d := by omega
        subst hmd'
        have hbij := mv.bijective_delta (2 * m + 1)
          (fun a => hUz (2 * m + 1) (by omega) a)
          (fun b => hVodd (2 * m + 1) (by omega) b)
          (fun a => hUz (2 * m + 1 + 1) (by omega) a)
          (fun b => hVbig (2 * m + 1 + 1) (by omega) b)
        exact ⟨(linearEquivOfBijective (mv.δ (2 * m + 1)) hbij).symm.trans hWtop.some⟩
  · -- the vanishing
    intro k hk a
    match k, hk, a with
    | 0, hk, _ => exact absurd rfl (hk 0 (Nat.zero_le _))
    | 1, _, a => exact hone a
    | (j + 2), hk, a =>
      have hne : j + 1 ≠ 2 * d + 1 := by
        intro hcontra
        exact hk (d + 1) (le_refl _) (by omega)
      exact mv.eq_zero_of_delta (j + 1)
        (fun b => hUz (j + 2) (by omega) b)
        (fun b => hVz (j + 2) (fun n hn => hk n (by omega)) b)
        (fun w => hWz (j + 1) (by omega) hne w) a

end CharClass
end GroupApproximation

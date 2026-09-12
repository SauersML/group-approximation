import GroupApproximation.CharClass.CohomologyBasic

/-!
# `H^*(ℂP^n; K)` as a graded module, by Mayer–Vietoris

The cover of `ℂP^{d+1}` by the affine chart and the complement of a point has
pieces which are, up to homotopy, a point, `ℂP^d` and `S^{2d+1}`
(`CharClass/ProjectiveSpaceCover.lean`).  Feeding that into the Mayer–Vietoris
sequence and inducting on `d` gives

```text
H^k(ℂP^d; K) = K  for k = 2n with n ≤ d,     0 otherwise.
```

This file contains the whole of that argument **except** the construction of the
Mayer–Vietoris sequence itself, which is lane `cc-cohom-api`'s.  The sequence
enters as a `structure MVSequenceOf K`: five maps and three exactness statements,
in element form.  Nothing here is a `sorry` or an `axiom` — the results are
theorems about any space carrying such a structure, and the topological input is
supplied by instantiating it.

## The coefficient parameter

Everything below is generic in a commutative ring `K` (`sp-coeff`'s `Hmod K`), and
`MVSequence`, `HasPointCohomology`, `HasSphereCohomology`, `HasCPCohomology` are
kept as reducible `abbrev`s at `K = ZMod 2`, so every existing `F₂` call site — in
this tree, seven of them outside `CharClass/Projective*` — is byte-unchanged.

**The five maps are now `K`-linear, and that is a change of design, not of
coefficients.**  They were declared `→+`, and the mod-2 file promoted them with
`toLinearZMod2` — "over `F₂` every additive map is linear", by `decide`.  That is
false over `K`, and threading the scalar condition as a hypothesis would have put
it on `hasCPCohomologyOf_succ`, on `exists_sum_eq_of_lines`, and on everything
that transports a line.  The maps were linear all along: `MayerVietorisSequence`
builds them from `ModuleCat` morphisms and had to *strip* the linearity with
`.toAddMonoidHom` to fit the fields.  So the fields carry it, the promotion is
deleted, and the cost is five tokens in the constructor.

Over `F₂` a nonzero element of a line *is* the generator; over `K` it is a **unit
multiple** of the generator (`CoeffLine.exists_ne_zero_smul_of_line`).  Nothing in
this file needs that — which is why `CoeffLine` is not imported here and
`[CommRing K]` suffices throughout — but `ProjectiveSpaceRing` does.

## The three ways the sequence is used

* `MVSequenceOf.bijective_resV` — where the chart and the intersection both
  vanish, `H^k(X) ≅ H^k(V)`: this propagates `ℂP^d` up to `ℂP^{d+1}` in the
  middle degrees.
* `MVSequenceOf.bijective_delta` — where `U` and `V` both vanish in two adjacent
  degrees, `δ : H^k(W) ≅ H^{k+1}(X)`: this creates the new top class
  `H^{2d+2}(ℂP^{d+1})` out of `H^{2d+1}(S^{2d+1})`.
* `MVSequenceOf.eq_zero_of_delta` — the vanishing version of the same.

Degree `1` is the one place where the connecting map is not controlled by
vanishing: `H^0(W) ≠ 0`.  It is handled by the hypothesis `hsum0`, that every
class of `H^0(W)` is a sum of restrictions from `H^0(U)` and `H^0(V)`, which by
exactness at `H^0(W)` forces `δ` out of degree `0` to be zero.

## The sign in `exact_W`, and why there is none

The classical middle map of the sequence is the *difference* `(a, b) ↦ a|_W - b|_W`,
and the mod-2 tree writes it as a sum.  That is **not** a characteristic-two
artefact of this structure: `exact_W` quantifies existentially over `b`, and
negation is a bijection of `H^n(V)`, so `∃ a b, resWU a + resWV b = w` and
`∃ a b, resWU a - resWV b = w` are the same statement over any ring.  The
characteristic-two step lives in the *construction* of the sequence
(`MayerVietorisElement.mvExactW`, owner `sp-coeff`), not here.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory

/-! ## 1. The sequence -/

section Sequence

variable (K : Type) [CommRing K]

/-- **The Mayer–Vietoris sequence of a two-piece cover, in element form.**
`X` is covered by `U` and `V` with intersection `W`; the maps are the four
restrictions and the connecting map, and the three `exact_*` fields are exactness
at `H^*(X)`, at `H^*(U) ⊕ H^*(V)` and at `H^*(W)`.  The middle map of the
classical sequence is a difference; `exact_W` is written with a sum, which is the
same statement because negation is a bijection of `H^n(V)` (see the module
docstring). -/
structure MVSequenceOf (X U V W : TopCat.{0}) where
  /-- Restriction `H^n(X) → H^n(U)`. -/
  resU : (n : ℕ) → Hmod K X n →ₗ[K] Hmod K U n
  /-- Restriction `H^n(X) → H^n(V)`. -/
  resV : (n : ℕ) → Hmod K X n →ₗ[K] Hmod K V n
  /-- Restriction `H^n(U) → H^n(W)`. -/
  resWU : (n : ℕ) → Hmod K U n →ₗ[K] Hmod K W n
  /-- Restriction `H^n(V) → H^n(W)`. -/
  resWV : (n : ℕ) → Hmod K V n →ₗ[K] Hmod K W n
  /-- The connecting map `H^n(W) → H^{n+1}(X)`. -/
  δ : (n : ℕ) → Hmod K W n →ₗ[K] Hmod K X (n + 1)
  /-- Exactness at `H^{n+1}(X)`. -/
  exact_X : ∀ (n : ℕ) (x : Hmod K X (n + 1)),
      (resU (n + 1) x = 0 ∧ resV (n + 1) x = 0) ↔ ∃ w, δ n w = x
  /-- Exactness at `H^n(U) ⊕ H^n(V)`. -/
  exact_sum : ∀ (n : ℕ) (a : Hmod K U n) (b : Hmod K V n),
      resWU n a = resWV n b ↔ ∃ x, resU n x = a ∧ resV n x = b
  /-- Exactness at `H^n(W)`. -/
  exact_W : ∀ (n : ℕ) (w : Hmod K W n),
      δ n w = 0 ↔ ∃ (a : Hmod K U n) (b : Hmod K V n), resWU n a + resWV n b = w

end Sequence

/-- The mod-2 Mayer–Vietoris sequence: the `K = ZMod 2` instance of
`MVSequenceOf`.  Reducible, so every existing call site and every anonymous
constructor elaborates unchanged. -/
abbrev MVSequence (X U V W : TopCat.{0}) : Type := MVSequenceOf (ZMod 2) X U V W

namespace MVSequenceOf

variable {K : Type} [CommRing K] {X U V W : TopCat.{0}}

/-- **Propagation.**  When `H^{n+1}(U)`, `H^n(W)` and `H^{n+1}(W)` all vanish,
restriction to `V` is an isomorphism in degree `n+1`. -/
theorem bijective_resV (mv : MVSequenceOf K X U V W) (n : ℕ)
    (hU : ∀ a : Hmod K U (n + 1), a = 0)
    (hWn : ∀ w : Hmod K W n, w = 0)
    (hWn1 : ∀ w : Hmod K W (n + 1), w = 0) :
    Function.Bijective (mv.resV (n + 1)) := by
  have hzero : ∀ z : Hmod K X (n + 1), mv.resV (n + 1) z = 0 → z = 0 := by
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
theorem bijective_delta (mv : MVSequenceOf K X U V W) (n : ℕ)
    (hUn : ∀ a : Hmod K U n, a = 0) (hVn : ∀ b : Hmod K V n, b = 0)
    (hUn1 : ∀ a : Hmod K U (n + 1), a = 0) (hVn1 : ∀ b : Hmod K V (n + 1), b = 0) :
    Function.Bijective (mv.δ n) := by
  have hzero : ∀ z : Hmod K W n, mv.δ n z = 0 → z = 0 := by
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
theorem eq_zero_of_delta (mv : MVSequenceOf K X U V W) (n : ℕ)
    (hUn1 : ∀ a : Hmod K U (n + 1), a = 0) (hVn1 : ∀ b : Hmod K V (n + 1), b = 0)
    (hWn : ∀ w : Hmod K W n, w = 0) (x : Hmod K X (n + 1)) : x = 0 := by
  obtain ⟨w, hw⟩ := (mv.exact_X n x).mp ⟨hUn1 (mv.resU (n + 1) x), hVn1 (mv.resV (n + 1) x)⟩
  rw [← hw, hWn w, map_zero]

end MVSequenceOf

/-! ### The mod-2 spellings of the three uses of the sequence

`MVSequence.bijective_resV` and its two siblings are named explicitly at one call
site (`ProjectiveSpaceStable`), so the namespace keeps them. -/

namespace MVSequence

variable {X U V W : TopCat.{0}}

theorem bijective_resV (mv : MVSequence X U V W) (n : ℕ)
    (hU : ∀ a : Hmod2 U (n + 1), a = 0)
    (hWn : ∀ w : Hmod2 W n, w = 0)
    (hWn1 : ∀ w : Hmod2 W (n + 1), w = 0) :
    Function.Bijective (mv.resV (n + 1)) :=
  MVSequenceOf.bijective_resV mv n hU hWn hWn1

theorem bijective_delta (mv : MVSequence X U V W) (n : ℕ)
    (hUn : ∀ a : Hmod2 U n, a = 0) (hVn : ∀ b : Hmod2 V n, b = 0)
    (hUn1 : ∀ a : Hmod2 U (n + 1), a = 0) (hVn1 : ∀ b : Hmod2 V (n + 1), b = 0) :
    Function.Bijective (mv.δ n) :=
  MVSequenceOf.bijective_delta mv n hUn hVn hUn1 hVn1

theorem eq_zero_of_delta (mv : MVSequence X U V W) (n : ℕ)
    (hUn1 : ∀ a : Hmod2 U (n + 1), a = 0) (hVn1 : ∀ b : Hmod2 V (n + 1), b = 0)
    (hWn : ∀ w : Hmod2 W n, w = 0) (x : Hmod2 X (n + 1)) : x = 0 :=
  MVSequenceOf.eq_zero_of_delta mv n hUn1 hVn1 hWn x

end MVSequence

/-! ## 2. The three cohomology shapes that occur -/

section Shapes

variable (K : Type) [CommRing K]

/-- `X` has the `K`-cohomology of a point. -/
def HasPointCohomologyOf (X : TopCat.{0}) : Prop :=
  Nonempty (Hmod K X 0 ≃ₗ[K] K) ∧ ∀ k : ℕ, k ≠ 0 → ∀ a : Hmod K X k, a = 0

/-- `X` has the `K`-cohomology of the sphere `S^m` (for `m ≠ 0`). -/
def HasSphereCohomologyOf (X : TopCat.{0}) (m : ℕ) : Prop :=
  Nonempty (Hmod K X 0 ≃ₗ[K] K) ∧
    Nonempty (Hmod K X m ≃ₗ[K] K) ∧
    ∀ k : ℕ, k ≠ 0 → k ≠ m → ∀ a : Hmod K X k, a = 0

/-- `X` has the `K`-cohomology of `ℂP^d`: a line in each even degree up to
`2d`, and nothing else. -/
def HasCPCohomologyOf (X : TopCat.{0}) (d : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ d → Nonempty (Hmod K X (2 * n) ≃ₗ[K] K)) ∧
    ∀ k : ℕ, (∀ n : ℕ, n ≤ d → k ≠ 2 * n) → ∀ a : Hmod K X k, a = 0

end Shapes

/-- `X` has the mod-2 cohomology of a point. -/
abbrev HasPointCohomology (X : TopCat.{0}) : Prop := HasPointCohomologyOf (ZMod 2) X

/-- `X` has the mod-2 cohomology of the sphere `S^m`. -/
abbrev HasSphereCohomology (X : TopCat.{0}) (m : ℕ) : Prop :=
  HasSphereCohomologyOf (ZMod 2) X m

/-- `X` has the mod-2 cohomology of `ℂP^d`. -/
abbrev HasCPCohomology (X : TopCat.{0}) (d : ℕ) : Prop := HasCPCohomologyOf (ZMod 2) X d

section ShapeTransport

variable {K : Type} [CommRing K]

theorem HasPointCohomologyOf.of_linearEquiv {X Y : TopCat.{0}}
    (e : ∀ k : ℕ, Hmod K X k ≃ₗ[K] Hmod K Y k) (h : HasPointCohomologyOf K Y) :
    HasPointCohomologyOf K X :=
  ⟨⟨(e 0).trans h.1.some⟩, fun k hk a => by
    have := h.2 k hk (e k a)
    simpa using congrArg (e k).symm this⟩

theorem HasSphereCohomologyOf.of_linearEquiv {X Y : TopCat.{0}} {m : ℕ}
    (e : ∀ k : ℕ, Hmod K X k ≃ₗ[K] Hmod K Y k) (h : HasSphereCohomologyOf K Y m) :
    HasSphereCohomologyOf K X m :=
  ⟨⟨(e 0).trans h.1.some⟩, ⟨(e m).trans h.2.1.some⟩, fun k hk hm a => by
    have := h.2.2 k hk hm (e k a)
    simpa using congrArg (e k).symm this⟩

theorem HasCPCohomologyOf.of_linearEquiv {X Y : TopCat.{0}} {d : ℕ}
    (e : ∀ k : ℕ, Hmod K X k ≃ₗ[K] Hmod K Y k) (h : HasCPCohomologyOf K Y d) :
    HasCPCohomologyOf K X d :=
  ⟨fun n hn => ⟨(e (2 * n)).trans (h.1 n hn).some⟩, fun k hk a => by
    have := h.2 k hk (e k a)
    simpa using congrArg (e k).symm this⟩

end ShapeTransport

/-- The mod-2 spellings, so that `HasSphereCohomology.of_linearEquiv` and its two
siblings keep resolving at their three call sites outside this directory. -/
theorem HasPointCohomology.of_linearEquiv {X Y : TopCat.{0}}
    (e : ∀ k : ℕ, Hmod2 X k ≃ₗ[ZMod 2] Hmod2 Y k) (h : HasPointCohomology Y) :
    HasPointCohomology X :=
  HasPointCohomologyOf.of_linearEquiv e h

theorem HasSphereCohomology.of_linearEquiv {X Y : TopCat.{0}} {m : ℕ}
    (e : ∀ k : ℕ, Hmod2 X k ≃ₗ[ZMod 2] Hmod2 Y k) (h : HasSphereCohomology Y m) :
    HasSphereCohomology X m :=
  HasSphereCohomologyOf.of_linearEquiv e h

theorem HasCPCohomology.of_linearEquiv {X Y : TopCat.{0}} {d : ℕ}
    (e : ∀ k : ℕ, Hmod2 X k ≃ₗ[ZMod 2] Hmod2 Y k) (h : HasCPCohomology Y d) :
    HasCPCohomology X d :=
  HasCPCohomologyOf.of_linearEquiv e h

/-! ## 3. The inductive step -/

section Induction

variable {K : Type} [CommRing K] {X U V W : TopCat.{0}}

/-- **The Mayer–Vietoris step for complex projective space.**

If `X` is covered by an acyclic `U` and a `V` with the cohomology of `ℂP^d`,
meeting in a `W` with the cohomology of `S^{2d+1}`, and if `X` is connected and
`H^0(U) → H^0(W)` is onto, then `X` has the cohomology of `ℂP^{d+1}`.

The three degree ranges are: the old even classes `2n`, `1 ≤ n ≤ d`, which come
from `V` by `bijective_resV`; the new top class in degree `2d+2`, which comes
from `H^{2d+1}(W)` by `bijective_delta`; and everything else, which dies by
`eq_zero_of_delta`, except degree `1`, where the connecting map is killed by
`hsum0` instead.

The two maps whose bijectivity carries a *line* across, `resV` and `δ`, are
`K`-linear as fields of the structure, so `LinearEquiv.ofBijective` applies
directly and no scalar hypothesis appears. -/
theorem hasCPCohomologyOf_succ (mv : MVSequenceOf K X U V W) (d : ℕ)
    (hU : HasPointCohomologyOf K U) (hV : HasCPCohomologyOf K V d)
    (hW : HasSphereCohomologyOf K W (2 * d + 1))
    (hsum0 : ∀ w : Hmod K W 0, ∃ (a : Hmod K U 0) (b : Hmod K V 0),
      mv.resWU 0 a + mv.resWV 0 b = w)
    (h0 : Nonempty (Hmod K X 0 ≃ₗ[K] K)) :
    HasCPCohomologyOf K X (d + 1) := by
  obtain ⟨hU0, hUz⟩ := hU
  obtain ⟨hVline, hVz⟩ := hV
  obtain ⟨hW0, hWtop, hWz⟩ := hW
  -- `V` has no odd cohomology, and none above `2d`.
  have hVodd : ∀ k : ℕ, k % 2 = 1 → ∀ b : Hmod K V k, b = 0 := by
    intro k hk
    exact hVz k fun n _ => by omega
  have hVbig : ∀ k : ℕ, 2 * d < k → ∀ b : Hmod K V k, b = 0 := by
    intro k hk
    exact hVz k fun n hn => by omega
  -- Degree `1` vanishes: the connecting map out of `H^0(W)` is zero.
  have hone : ∀ x : Hmod K X 1, x = 0 := by
    intro x
    obtain ⟨w, hw⟩ := (mv.exact_X 0 x).mp
      ⟨hUz 1 one_ne_zero (mv.resU 1 x), hVodd 1 rfl (mv.resV 1 x)⟩
    obtain ⟨a, b, hab⟩ := hsum0 w
    have hd : mv.δ 0 w = 0 := (mv.exact_W 0 w).mpr ⟨a, b, hab⟩
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
        exact ⟨(LinearEquiv.ofBijective (mv.resV (2 * m + 1 + 1)) hbij).trans
          (hVline (m + 1) (by omega)).some⟩
      · -- the new top class
        have hmd' : m = d := by omega
        subst hmd'
        have hbij := mv.bijective_delta (2 * m + 1)
          (fun a => hUz (2 * m + 1) (by omega) a)
          (fun b => hVodd (2 * m + 1) (by omega) b)
          (fun a => hUz (2 * m + 1 + 1) (by omega) a)
          (fun b => hVbig (2 * m + 1 + 1) (by omega) b)
        exact ⟨(LinearEquiv.ofBijective (mv.δ (2 * m + 1)) hbij).symm.trans hWtop.some⟩
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

end Induction

/-- The mod-2 inductive step: the statement the projective-space induction has
always used, unchanged. -/
theorem hasCPCohomology_succ {X U V W : TopCat.{0}} (mv : MVSequence X U V W) (d : ℕ)
    (hU : HasPointCohomology U) (hV : HasCPCohomology V d)
    (hW : HasSphereCohomology W (2 * d + 1))
    (hsum0 : ∀ w : Hmod2 W 0, ∃ (a : Hmod2 U 0) (b : Hmod2 V 0),
      mv.resWU 0 a + mv.resWV 0 b = w)
    (h0 : Nonempty (Hmod2 X 0 ≃ₗ[ZMod 2] ZMod 2)) :
    HasCPCohomology X (d + 1) :=
  hasCPCohomologyOf_succ mv d hU hV hW hsum0 h0

end CharClass
end GroupApproximation

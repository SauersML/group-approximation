import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Group.End
import GroupApproximation.Meta.AxiomGuard

/-!
# EXC: Nisnevich glueing for `St_r` (Lavrenov–Sinchuk–Voronetsky, Thm 4.1), the orbit reduction

Lane `fix-bh-a`, piece EXC of the K₂ program (board `k2-poly.md`, lead bh-pal-wire).  Source:
A. Lavrenov, S. Sinchuk, E. Voronetsky, *On the A¹-invariance of K₂ modeled on linear and even
orthogonal groups*, arXiv:2110.11087, §4 (type `A_{r-1}` here).

Setting: a ring map `ι : B → A` and `h ∈ B`, with `λ_h : B → B_h`, `λ_h : A → A_h` and the induced
`ι_h : B_h → A_h` (`iotaH`).

* `GlueingAt r ι h` (LSV Thm 4.1): `St_r(B)` surjects onto the pullback
  `St_r(B_h) ×_{St_r(A_h)} St_r(A)`.
* `kerSurj_of_glueingAt` (LSV Cor 4.2, axiom (A3)): then
  `ker(St_r(B) → St_r(B_h)) → ker(St_r(A) → St_r(A_h))` is onto.
* `orbitSetoid`: the orbits of `St_r(B)` acting on `St_r(B_h) × St_r(A)` by
  `g ⋆ (u, v) = (u λ_h(g)⁻¹, ι(g) v)` (LSV Def 4.3).  Their quotient is the set `V`.
* **Residual** `ActionAt r ι h` (the core of LSV Prop 4.4): an action `ρ` of `St_r(A_h)` on `V`
  with `ρ(λ_h v)[1, 1] = [1, v]` and `ρ(ι_h u)[1, v] = [u, v]` (LSV (4.2)).
* `glueingAt_of_actionAt`: **proved**, the argument of LSV Cor 4.5.  If `ι_h(u) = λ_h(v)`, then
  `[u⁻¹, v] = ρ(ι_h(u)⁻¹ λ_h(v))[1, 1] = [1, 1]`, so `(u⁻¹, v)` lies in the orbit of `(1, 1)`.
* `NisnevichGlueingStatement r` and `NisnevichActionStatement r`: the same, for all domains
  `B ⊆ A` with `h ≠ 0` and `B/h = A/h` (stated as `A = ι(B) + hA` and `ι(B) ∩ hA = ι(hB)`), and
  `nisnevichGlueing_of_action`.
* `exists_eq_add_pow_mul` and `exists_eq_pow_mul`: `B/h = A/h` gives `A = ι(B) + h^k A` and
  `ι(B) ∩ h^k A = ι(h^k B)` for every `k` (LSV §4.1, Step 2).

LOUD (strength).  `ActionAt` is the whole difficulty of LSV §4: the conjugation maps
`c_g : St(h^k A) → St(A)` built with Steinberg pro-groups (Voronetsky), the maps `T_α` on `V`, and the
check of the Steinberg relations (LSV Lemma 4.17, §4.4).  This file removes only the orbit
bookkeeping.  `ActionAt` is at least as strong as `GlueingAt`: it also makes `V → St_r(A_h)` onto.
-/

namespace GroupApproximation.K2Excision

open GroupApproximation SteinbergGroup

section Setup

variable (r : ℕ) {B A : Type*} [CommRing B] [CommRing A] (ι : B →+* A) (h : B)

/-- `ι_h : B_h → A_h`, the map induced by `ι`. -/
noncomputable abbrev iotaH : Localization.Away h →+* Localization.Away (ι h) :=
  IsLocalization.Away.map (Localization.Away h) (Localization.Away (ι h)) ι h

/-- `ι_h ∘ λ_h = λ_h ∘ ι`. -/
theorem iotaH_comp :
    (iotaH ι h).comp (algebraMap B (Localization.Away h)) =
      (algebraMap A (Localization.Away (ι h))).comp ι :=
  IsLocalization.map_comp (hy := _)

#audit_axioms GroupApproximation.K2Excision.iotaH_comp

/-- **Nisnevich glueing at rank `r`** (LSV Thm 4.1): `St_r(B)` surjects onto the pullback
`St_r(B_h) ×_{St_r(A_h)} St_r(A)`. -/
def GlueingAt : Prop :=
  ∀ (u : SteinbergGroup (Fin r) (Localization.Away h)) (v : SteinbergGroup (Fin r) A),
    ringMap (iotaH ι h) u = ringMap (algebraMap A (Localization.Away (ι h))) v →
      ∃ y : SteinbergGroup (Fin r) B,
        ringMap (algebraMap B (Localization.Away h)) y = u ∧ ringMap ι y = v

#audit_axioms GroupApproximation.K2Excision.GlueingAt

/-- LSV Cor 4.2 (axiom (A3)): glueing makes `ker(St_r(B) → St_r(B_h)) → ker(St_r(A) → St_r(A_h))`
onto. -/
theorem kerSurj_of_glueingAt (hG : GlueingAt r ι h) (v : SteinbergGroup (Fin r) A)
    (hv : ringMap (algebraMap A (Localization.Away (ι h))) v = 1) :
    ∃ y : SteinbergGroup (Fin r) B,
      ringMap (algebraMap B (Localization.Away h)) y = 1 ∧ ringMap ι y = v :=
  hG 1 v (by rw [map_one, hv])

#audit_axioms GroupApproximation.K2Excision.kerSurj_of_glueingAt

/-- `g ⋆ (u, v) = (u λ_h(g)⁻¹, ι(g) v)` (LSV Def 4.3). -/
def orbitAct (g : SteinbergGroup (Fin r) B)
    (p : SteinbergGroup (Fin r) (Localization.Away h) × SteinbergGroup (Fin r) A) :
    SteinbergGroup (Fin r) (Localization.Away h) × SteinbergGroup (Fin r) A :=
  (p.1 * (ringMap (algebraMap B (Localization.Away h)) g)⁻¹, ringMap ι g * p.2)

#audit_axioms GroupApproximation.K2Excision.orbitAct

/-- The orbit relation of `⋆`. -/
def orbitSetoid :
    Setoid (SteinbergGroup (Fin r) (Localization.Away h) × SteinbergGroup (Fin r) A) where
  r p q := ∃ g, q = orbitAct r ι h g p
  iseqv := by
    refine ⟨fun p => ⟨1, by simp [orbitAct]⟩, fun {p q} ⟨g, hg⟩ => ⟨g⁻¹, ?_⟩,
      fun {p q s} ⟨g, hg⟩ ⟨g', hg'⟩ => ⟨g' * g, ?_⟩⟩
    · subst hg
      simp [orbitAct, mul_assoc]
    · subst hg hg'
      simp [orbitAct, mul_assoc]

#audit_axioms GroupApproximation.K2Excision.orbitSetoid

/-- The class `[u, v]` of `(u, v)` in the orbit set `V`. -/
def mk (u : SteinbergGroup (Fin r) (Localization.Away h)) (v : SteinbergGroup (Fin r) A) :
    Quotient (orbitSetoid r ι h) :=
  Quotient.mk _ (u, v)

#audit_axioms GroupApproximation.K2Excision.mk

/-- **Residual (core of LSV Prop 4.4).** An action of `St_r(A_h)` on the orbit set `V` satisfying
LSV (4.2). -/
def ActionAt : Prop :=
  ∃ ρ : SteinbergGroup (Fin r) (Localization.Away (ι h)) →* Equiv.Perm (Quotient (orbitSetoid r ι h)),
    (∀ v, ρ (ringMap (algebraMap A (Localization.Away (ι h))) v) (mk r ι h 1 1) = mk r ι h 1 v) ∧
    (∀ u v, ρ (ringMap (iotaH ι h) u) (mk r ι h 1 v) = mk r ι h u v)

#audit_axioms GroupApproximation.K2Excision.ActionAt

/-- **LSV Cor 4.5 ⟹ Thm 4.1**: an action as in Prop 4.4 gives Nisnevich glueing. -/
theorem glueingAt_of_actionAt (hρ : ActionAt r ι h) : GlueingAt r ι h := by
  obtain ⟨ρ, h1, h2⟩ := hρ
  intro u v huv
  have key : mk r ι h u⁻¹ v = mk r ι h 1 1 := by
    rw [← h2 u⁻¹ v, ← h1 v, ← Equiv.Perm.mul_apply, ← map_mul, map_inv, huv, inv_mul_cancel,
      map_one, Equiv.Perm.one_apply]
  obtain ⟨g, hg⟩ := Quotient.exact key
  simp only [orbitAct, Prod.mk.injEq] at hg
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨g⁻¹, ?_, ?_⟩
  · have hu : u = (ringMap (algebraMap B (Localization.Away h)) g)⁻¹ := by
      simpa using congrArg (u * ·) hg1
    rw [map_inv, hu]
  · rw [map_inv]
    exact (eq_inv_of_mul_eq_one_right hg2.symm).symm

#audit_axioms GroupApproximation.K2Excision.glueingAt_of_actionAt

end Setup

section Pow

variable {B A : Type*} [CommRing B] [CommRing A] (ι : B →+* A) (h : B)

/-- `A = ι(B) + hA` gives `A = ι(B) + h^k A` for every `k`. -/
theorem exists_eq_add_pow_mul (hs : ∀ a : A, ∃ b : B, ∃ a' : A, a = ι b + ι h * a') (k : ℕ)
    (a : A) : ∃ b : B, ∃ a' : A, a = ι b + ι h ^ k * a' := by
  induction k generalizing a with
  | zero => exact ⟨0, a, by simp⟩
  | succ k ih =>
    obtain ⟨b, a', ha⟩ := ih a
    obtain ⟨b₁, a'', ha'⟩ := hs a'
    refine ⟨b + h ^ k * b₁, a'', ?_⟩
    rw [ha, ha', map_add, map_mul, map_pow]
    ring

#audit_axioms GroupApproximation.K2Excision.exists_eq_add_pow_mul

/-- In a domain `A`, with `ι` injective and `h ≠ 0`, `ι(B) ∩ hA = ι(hB)` gives
`ι(B) ∩ h^k A = ι(h^k B)` for every `k`. -/
theorem exists_eq_pow_mul [IsDomain A] (hι : Function.Injective ι) (h0 : h ≠ 0)
    (hi : ∀ (b : B) (a : A), ι b = ι h * a → ∃ b' : B, b = h * b') (k : ℕ) (b : B) (a : A)
    (hb : ι b = ι h ^ k * a) : ∃ b' : B, b = h ^ k * b' := by
  induction k generalizing b a with
  | zero => exact ⟨b, by simp⟩
  | succ k ih =>
    obtain ⟨b₁, rfl⟩ := hi b (ι h ^ k * a) (by rw [hb]; ring)
    have hιh : ι h ≠ 0 := (map_ne_zero_iff ι hι).mpr h0
    have hb₁ : ι b₁ = ι h ^ k * a := by
      apply mul_left_cancel₀ hιh
      rw [← map_mul, hb]
      ring
    obtain ⟨b', rfl⟩ := ih b₁ a hb₁
    exact ⟨b', by ring⟩

#audit_axioms GroupApproximation.K2Excision.exists_eq_pow_mul

end Pow

/-- **Nisnevich glueing for domains** (LSV Thm 4.1, type `A_{r-1}`): for domains `B ⊆ A`, `h ≠ 0`
and `B/h = A/h`. -/
def NisnevichGlueingStatement (r : ℕ) : Prop :=
  ∀ (B A : Type) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A] (ι : B →+* A),
    Function.Injective ι → ∀ h : B, h ≠ 0 →
    (∀ a : A, ∃ b : B, ∃ a' : A, a = ι b + ι h * a') →
    (∀ (b : B) (a : A), ι b = ι h * a → ∃ b' : B, b = h * b') →
      GlueingAt r ι h

#audit_axioms GroupApproximation.K2Excision.NisnevichGlueingStatement

/-- **Residual for domains** (core of LSV Prop 4.4). -/
def NisnevichActionStatement (r : ℕ) : Prop :=
  ∀ (B A : Type) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A] (ι : B →+* A),
    Function.Injective ι → ∀ h : B, h ≠ 0 →
    (∀ a : A, ∃ b : B, ∃ a' : A, a = ι b + ι h * a') →
    (∀ (b : B) (a : A), ι b = ι h * a → ∃ b' : B, b = h * b') →
      ActionAt r ι h

#audit_axioms GroupApproximation.K2Excision.NisnevichActionStatement

/-- The residual gives Nisnevich glueing. -/
theorem nisnevichGlueing_of_action {r : ℕ} (H : NisnevichActionStatement r) :
    NisnevichGlueingStatement r := by
  intro B A _ _ _ _ ι hι h h0 hs hi
  exact glueingAt_of_actionAt r ι h (H B A ι hι h h0 hs hi)

#audit_axioms GroupApproximation.K2Excision.nisnevichGlueing_of_action

end GroupApproximation.K2Excision

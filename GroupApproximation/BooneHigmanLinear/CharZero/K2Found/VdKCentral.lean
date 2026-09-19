import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdK

/-!
# vdK's Theorem 1 reduced to perfectness and the elements `X(v, w)` (k2-poly, piece F.1)

W. van der Kallen, *Another presentation for Steinberg groups*, Indag. Math. **39** (1977): the
proof of Corollary 1, and 3.5.

* `actPair M (k, l) = (M k, l M⁻¹)`. `GL(n, A)` acts on `U` (`actPair_mem`), and `e(i, j)` acts by
  vdK's `conjPair` (`actPair_eUnit`).
* `X_conj_general`: `x X(k, l) x⁻¹ = X(π(x) k, l π(x)⁻¹)` for every `x ∈ St*(n, A)`. For generators
  this is vdK's second relation.
* `ker_piStar_le_center`: `ker π` is central in `St*(n, A)` (proof of vdK's Corollary 1).
* `eq_of_comp_eq_of_perfect`: Milnor's Lemma 5.4. Two homomorphisms from a perfect group into a
  central extension that agree downstairs are equal.
* `theorem1_of_perfect_of_elements`: vdK 3.5. If `St*(n, A)` is perfect and `Elements I A` exists
  (vdK's requirements 3.6 (a)–(d)), then `φ : St(n, A) → St*(n, A)` is an isomorphism.

The two remaining inputs of vdK's Theorem 1 are 3.4 (`St*(n, A)` is perfect, using `n ≥ 4`) and
3.7–3.22 (the elements `X(i, j) ∈ St(n, A)`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace VdK

open scoped commutatorElement Matrix
open GroupApproximation.SteinbergGroup

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A]

section Action

/-- `M ∈ GL(n, A)` acts on pairs by `(k, l) ↦ (M k, l M⁻¹)`. -/
def actPair (M : (Matrix I I A)ˣ) (q : (I → A) × (I → A)) : (I → A) × (I → A) :=
  ((M : Matrix I I A) *ᵥ q.1, q.2 ᵥ* ((M⁻¹ : (Matrix I I A)ˣ) : Matrix I I A))

/-- `GL(n, A)` preserves `U`: `(m M⁻¹)(M k) = m k` and `(l M⁻¹)(M k) = l k`. -/
theorem actPair_mem (M : (Matrix I I A)ˣ) {q : (I → A) × (I → A)} (hq : q ∈ U I A) :
    actPair M q ∈ U I A := by
  obtain ⟨⟨m, hm⟩, hlk⟩ := mem_U.1 hq
  have key : ∀ u v : I → A, (u ᵥ* ((M⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) ⬝ᵥ
      ((M : Matrix I I A) *ᵥ v) = u ⬝ᵥ v := by
    intro u v
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
  refine mem_U.2 ⟨⟨m ᵥ* ((M⁻¹ : (Matrix I I A)ˣ) : Matrix I I A), ?_⟩, ?_⟩
  · show (m ᵥ* ((M⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) ⬝ᵥ ((M : Matrix I I A) *ᵥ q.1) = 1
    rw [key, hm]
  · show (q.2 ᵥ* ((M⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) ⬝ᵥ ((M : Matrix I I A) *ᵥ q.1) = 0
    rw [key, hlk]

#audit_axioms actPair_mem

theorem actPair_one (q : (I → A) × (I → A)) : actPair 1 q = q := by
  refine Prod.ext ?_ ?_
  · show ((1 : (Matrix I I A)ˣ) : Matrix I I A) *ᵥ q.1 = q.1
    rw [Units.val_one, Matrix.one_mulVec]
  · show q.2 ᵥ* (((1 : (Matrix I I A)ˣ)⁻¹ : (Matrix I I A)ˣ) : Matrix I I A) = q.2
    rw [inv_one, Units.val_one, Matrix.vecMul_one]

theorem actPair_mul (M N : (Matrix I I A)ˣ) (q : (I → A) × (I → A)) :
    actPair (M * N) q = actPair M (actPair N q) := by
  refine Prod.ext ?_ ?_
  · show ((M * N : (Matrix I I A)ˣ) : Matrix I I A) *ᵥ q.1 =
      (M : Matrix I I A) *ᵥ ((N : Matrix I I A) *ᵥ q.1)
    rw [Units.val_mul, Matrix.mulVec_mulVec]
  · show q.2 ᵥ* (((M * N)⁻¹ : (Matrix I I A)ˣ) : Matrix I I A) =
      (q.2 ᵥ* ((N⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) ᵥ* ((M⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)
    rw [mul_inv_rev, Units.val_mul, Matrix.vecMul_vecMul]

/-- `e(i, j)` acts by vdK's `conjPair`: `e(i, j) k = k + i (j k)` and
`l e(i, j)⁻¹ = l (1 - i j) = l - (l i) j`. -/
theorem actPair_eUnit (p q : (I → A) × (I → A)) (hp : p.2 ⬝ᵥ p.1 = 0) :
    actPair (eUnit p.1 p.2 hp) q = conjPair p q := by
  refine Prod.ext ?_ ?_
  · show (1 + Matrix.vecMulVec p.1 p.2) *ᵥ q.1 = q.1 + (p.2 ⬝ᵥ q.1) • p.1
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  · show q.2 ᵥ* (1 - Matrix.vecMulVec p.1 p.2) = q.2 - (q.2 ⬝ᵥ p.1) • p.2
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_vecMulVec]

#audit_axioms actPair_eUnit

end Action

section Central

/-- `x ∈ St*(n, A)` conjugates every generator through `π(x)`. -/
def ActsThroughPi (x : StStar I A) : Prop :=
  ∀ (q : (I → A) × (I → A)) (hq : q ∈ U I A),
    x * X q hq * x⁻¹ = X (actPair (piStar I A x) q) (actPair_mem _ hq)

theorem actsThroughPi_one : ActsThroughPi (1 : StStar I A) := by
  intro q hq
  rw [one_mul, inv_one, mul_one]
  exact X_congr (by rw [map_one, actPair_one]) _ _

theorem actsThroughPi_mul {x y : StStar I A} (hx : ActsThroughPi x) (hy : ActsThroughPi y) :
    ActsThroughPi (x * y) := by
  intro q hq
  have h1 : x * y * X q hq * (x * y)⁻¹ = x * (y * X q hq * y⁻¹) * x⁻¹ := by group
  rw [h1, hy q hq, hx _ (actPair_mem _ hq)]
  exact X_congr (by rw [map_mul, actPair_mul]) _ _

theorem actsThroughPi_inv {x : StStar I A} (hx : ActsThroughPi x) : ActsThroughPi x⁻¹ := by
  intro q hq
  have h := hx (actPair (piStar I A x⁻¹) q) (actPair_mem _ hq)
  have hback : actPair (piStar I A x) (actPair (piStar I A x⁻¹) q) = q := by
    rw [← actPair_mul, ← map_mul, mul_inv_cancel, map_one, actPair_one]
  rw [X_congr hback _ hq] at h
  rw [← h]
  group

variable (I A) in
/-- The subgroup of `x ∈ St*(n, A)` that conjugate every generator through `π(x)`. -/
def actsThroughPi : Subgroup (StStar I A) where
  carrier := {x | ActsThroughPi x}
  one_mem' := actsThroughPi_one
  mul_mem' := fun hx hy => actsThroughPi_mul hx hy
  inv_mem' := fun hx => actsThroughPi_inv hx

theorem X_mem_actsThroughPi (p : (I → A) × (I → A)) (hp : p ∈ U I A) :
    X p hp ∈ actsThroughPi I A := by
  show ActsThroughPi (X p hp)
  intro q hq
  rw [X_conj]
  exact X_congr (by rw [piStar_X, actPair_eUnit]) _ _

theorem mem_actsThroughPi (x : StStar I A) : x ∈ actsThroughPi I A :=
  PresentedGroup.generated_by _ _ (fun g => X_mem_actsThroughPi g.1 g.2) x

/-- **Conjugation through `π`.** For every `x ∈ St*(n, A)`,
`x X(k, l) x⁻¹ = X(π(x) k, l π(x)⁻¹)`. -/
theorem X_conj_general (x : StStar I A) (q : (I → A) × (I → A)) (hq : q ∈ U I A) :
    x * X q hq * x⁻¹ = X (actPair (piStar I A x) q) (actPair_mem _ hq) :=
  (show ActsThroughPi x from mem_actsThroughPi x) q hq

#audit_axioms X_conj_general

/-- **vdK, proof of Corollary 1.** `ker (π : St*(n, A) → GL(n, A))` is central. -/
theorem ker_piStar_le_center : (piStar I A).ker ≤ Subgroup.center (StStar I A) := by
  intro z hz
  rw [MonoidHom.mem_ker] at hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hcomm : ∀ (q : (I → A) × (I → A)) (hq : q ∈ U I A), X q hq * z = z * X q hq := by
    intro q hq
    have h := X_conj_general z q hq
    rw [X_congr (show actPair (piStar I A z) q = q by rw [hz, actPair_one]) _ hq] at h
    calc X q hq * z = z * X q hq * z⁻¹ * z := by rw [h]
      _ = z * X q hq := by group
  have hg : g ∈ Subgroup.centralizer ({z} : Set (StStar I A)) := by
    refine PresentedGroup.generated_by _ _ (fun w => ?_) g
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hcomm w.1 w.2).symm
  rw [Subgroup.mem_centralizer_iff] at hg
  exact (hg z (Set.mem_singleton z)).symm

#audit_axioms ker_piStar_le_center

end Central

section Milnor

/-- Central factors do not change a commutator. -/
theorem commutatorElement_mul_mem_center {G : Type*} [Group G] {x y c d : G}
    (hc : c ∈ Subgroup.center G) (hd : d ∈ Subgroup.center G) : ⁅x * c, y * d⁆ = ⁅x, y⁆ := by
  rw [Subgroup.mem_center_iff] at hc hd
  have h1 : c * (y * d) * c⁻¹ = y * d := by rw [← hc (y * d), mul_inv_cancel_right]
  have h2 : d * x⁻¹ = x⁻¹ * d := (hd x⁻¹).symm
  calc ⁅x * c, y * d⁆ = x * (c * (y * d) * c⁻¹) * x⁻¹ * (y * d)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = x * y * (d * x⁻¹) * d⁻¹ * y⁻¹ := by rw [h1]; group
    _ = x * y * (x⁻¹ * d) * d⁻¹ * y⁻¹ := by rw [h2]
    _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group

/-- **Milnor, *Introduction to algebraic K-theory*, Lemma 5.4.** Let `π : G → E` have central
kernel and let `P` be perfect. Two homomorphisms `f, g : P → G` with `π f = π g` are equal. -/
theorem eq_of_comp_eq_of_perfect {P G E : Type*} [Group P] [Group G] [Group E] (π : G →* E)
    (hc : π.ker ≤ Subgroup.center G) (hP : _root_.commutator P = ⊤) {f g : P →* G}
    (h : π.comp f = π.comp g) : f = g := by
  have hcen : ∀ a, (g a)⁻¹ * f a ∈ Subgroup.center G := by
    intro a
    apply hc
    have ha := DFunLike.congr_fun h a
    simp only [MonoidHom.comp_apply] at ha
    rw [MonoidHom.mem_ker, map_mul, map_inv, ha, inv_mul_cancel]
  have hfa : ∀ a, f a = g a * ((g a)⁻¹ * f a) := fun a => by group
  have hle : _root_.commutator P ≤ f.eqLocus g := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    show f ⁅a, b⁆ = g ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement, hfa a, hfa b,
      commutatorElement_mul_mem_center (hcen a) (hcen b)]
  ext a
  have ha : a ∈ _root_.commutator P := by rw [hP]; exact Subgroup.mem_top a
  exact hle ha

#audit_axioms eq_of_comp_eq_of_perfect

end Milnor

section Reduction

/-- The map `ψ : St*(n, A) → St(n, A)`, `X(v, w) ↦ X(v, w)`, defined by vdK's two relations for
the elements `X(v, w) ∈ St(n, A)`. -/
def psiOfElements (E : Elements I A) : StStar I A →* SteinbergGroup I A :=
  PresentedGroup.toGroup (f := fun g : Gen I A => E.elt g.1 g.2) (by
    intro w hw
    change IsRel w at hw
    cases hw with
    | add i j k h₁ h₂ h₃ =>
        simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
        change E.elt (i, j) h₁ * E.elt (i, k) h₂ * (E.elt (i, j + k) h₃)⁻¹ = 1
        rw [E.mul i j k h₁ h₂ h₃, mul_inv_cancel]
    | conj p q hp hq =>
        simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
        change E.elt p hp * E.elt q hq * (E.elt p hp)⁻¹ *
          (E.elt (conjPair p q) (conjPair_mem hp hq))⁻¹ = 1
        rw [E.conj p q hp hq, mul_inv_cancel])

@[simp] theorem psiOfElements_X (E : Elements I A) (p : (I → A) × (I → A)) (hp : p ∈ U I A) :
    psiOfElements E (X p hp) = E.elt p hp :=
  PresentedGroup.toGroup.of _

theorem psiOfElements_comp_phi (E : Elements I A) :
    (psiOfElements E).comp (phi I A) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  rintro ⟨p, q, hpq, a⟩
  change psiOfElements E (phi I A (x p q hpq a)) = x p q hpq a
  rw [phi_x, psiOfElements_X, E.std]

theorem proj_comp_psiOfElements (E : Elements I A) :
    ((elementaryGroup I A).subtype.comp projection).comp (psiOfElements E) = piStar I A := by
  apply PresentedGroup.ext
  rintro ⟨p, hp⟩
  change ((projection (psiOfElements E (X p hp)) : elementaryGroup I A) : (Matrix I I A)ˣ) =
    piStar I A (X p hp)
  rw [psiOfElements_X, piStar_X, E.proj]

/-- **vdK 3.5: Theorem 1 from perfectness and the elements `X(v, w)`.** If `St*(n, A)` is perfect
(vdK 3.4) and elements `X(v, w) ∈ St(n, A)` meeting vdK's requirements 3.6 (a)–(d) exist (vdK
3.7–3.22), then `φ : St(n, A) → St*(n, A)` is an isomorphism. The inverse is `ψ`. `ψ φ = id` on
generators, and `φ ψ = id` by Milnor's Lemma 5.4, because `ker π` is central. -/
theorem theorem1_of_perfect_of_elements (hP : _root_.commutator (StStar I A) = ⊤)
    (E : Elements I A) : Theorem1At I A := by
  have hφψ : (phi I A).comp (psiOfElements E) = MonoidHom.id _ := by
    apply eq_of_comp_eq_of_perfect (piStar I A) ker_piStar_le_center hP
    rw [← MonoidHom.comp_assoc, piStar_comp_phi, proj_comp_psiOfElements, MonoidHom.comp_id]
  refine ⟨fun a b hab => ?_, fun y => ⟨psiOfElements E y, ?_⟩⟩
  · have ha := DFunLike.congr_fun (psiOfElements_comp_phi E) a
    have hb := DFunLike.congr_fun (psiOfElements_comp_phi E) b
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at ha hb
    calc a = psiOfElements E (phi I A a) := ha.symm
      _ = psiOfElements E (phi I A b) := by rw [hab]
      _ = b := hb
  · have hy := DFunLike.congr_fun hφψ y
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using hy

#audit_axioms theorem1_of_perfect_of_elements

end Reduction

end VdK
end K2Found
end BooneHigmanLinear
end GroupApproximation

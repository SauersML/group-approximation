import GroupApproximation.GGT.HullSCRelatorSeparation2Aligned

/-!
# The mixed case, assembled: from the polygon estimate to a contradiction

`GGT/HullSCRelatorSeparation2MirrorGap.lean` closes the mixed case from matched
blocks whose exponents are already known to agree.  Making them agree is the
rigidity of `GGT/HullSCRelatorSeparation2Rigid.lean`, and what stands between
the two is bookkeeping: the polygon estimate hands over a matched pair as a
*value* relation `X = y · x · z` between the elements two block letters carry,
with `y` and `z` short, and the rigidity wants it as an equation between a power
and the inverse of a power.

`exponent_eq_of_mirroredPair` is that step, for one pair.  It reads the exponent
of each of the two letters off its position -- forwards on the relator, backwards
on the formal inverse -- turns the value relation into
`y · a_b^e · z = (a_b^f)⁻¹`, and applies
`HullSC.exponent_eq_of_mirroredBlockMatch₂`.  The conclusion is packaged as the
two letters in the shape the gap lemma consumes, together with `e = f`.

`not_mixedMatch` applies it twice and closes the case.  The hypotheses are
exactly the polygon estimate's output: two matched pairs at ordered offsets,
with the second gap within `gapSlack` of the first, `gapSlack` being the
estimate's `2(ε+1)`; and the design's inequality `2g + gapSlack < |R|`, which is
met by taking the number of exponents large.  Nothing else about the geometry
enters -- the connectors are used only through their norms.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Mixed

variable {G : Type u} [Group G]

omit [Group G] in
/-- The two elements of the family, selected by index. -/
theorem ite_apply_eq (a : Bool → G) (b : Bool) :
    (if b then a true else a false) = a b := by
  cases b <;> rfl

/-- **One matched pair in the mixed case: the exponents agree.**

The letter of the relator carries `a_b^e` and the letter of the formal inverse
carries `(a_b^f)⁻¹`; the value relation with short connectors is exactly the
equation the mirrored rigidity forbids for `e ≠ f`. -/
theorem exponent_eq_of_mirroredPair {D : GGT.RelGenSet G Bool}
    (hbase : IsSymmetricGeneratingSet D.base) {a : Bool → G} {eps rho : ℕ}
    {ms : List ℕ}
    (hgeoInv : ∀ (t : Bool) (i j : ℕ) (x x' : G), wordNorm D.base x ≤ eps →
      wordNorm D.base x' ≤ eps → a t ^ i ∉ D.relBall t rho →
        (a t ^ j)⁻¹ ∉ D.relBall t rho → x * a t ^ i * x' = (a t ^ j)⁻¹ →
          x ∈ D.fam t ∧ x' ∈ D.fam t)
    (hdeep : ∀ m ∈ ms, ∀ t : Bool, a t ^ m ∉ D.relBall t rho ∧
      (a t ^ m)⁻¹ ∉ D.relBall t rho)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {p : List G} {c c' i j : ℕ}
    (hi : i < (relatorWord₂ p (a false) (a true) ms).length)
    (hj : j < (relatorWord₂ p (a false) (a true) ms).length)
    {b : Bool} {x X y z : G}
    (hx : ((relatorWord₂ p (a false) (a true) ms).rotate c)[i]?
      = some (GGT.RelLetter.comp b x))
    (hX : ((RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).rotate c')[j]?
      = some (GGT.RelLetter.comp b X))
    (hy : wordNorm D.base y ≤ eps) (hz : wordNorm D.base z ≤ eps)
    (hval : X = y * x * z) :
    ∃ e f : ℕ,
      ((relatorWord₂ p (a false) (a true) ms).rotate c)[i]?
          = some (GGT.RelLetter.comp b ((if b then a true else a false) ^ e)) ∧
        ((RelWord.revInv
              (relatorWord₂ p (a false) (a true) ms)).rotate c')[j]?
            = some (GGT.RelLetter.comp b
              (((if b then a true else a false) ^ f)⁻¹)) ∧
          e = f := by
  have hrev : (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length
      = (relatorWord₂ p (a false) (a true) ms).length := RelWord.length_revInv _
  have h1 := getElem?_of_rotate hi hx
  have hj' : j < (RelWord.revInv (relatorWord₂ p (a false) (a true) ms)).length := by
    rw [hrev]
    exact hj
  have h2 := getElem?_of_rotate hj' hX
  rw [hrev] at h2
  obtain ⟨k, -, -, hkb⟩ := blockIndex_of_relatorWord₂ h1
  obtain ⟨htlt, htb⟩ := blockIndex_of_revInv_relatorWord₂ h2
  obtain ⟨e, hme, hxe⟩ :=
    blockWord_getElem?_exponent (a false) (a true) false ms k b _ hkb
  obtain ⟨f, hmf, hXf⟩ :=
    revInv_blockWord_getElem?_exponent (a false) (a true) false ms
      (q := ms.length - 1
        - (c' + j) % (relatorWord₂ p (a false) (a true) ms).length)
      (by omega) htb
  have heq : y * a b ^ e * z = (a b ^ f)⁻¹ := by
    rw [← ite_apply_eq a b, ← hxe, ← hXf]
    exact hval.symm
  have hef : e = f :=
    exponent_eq_of_mirroredBlockMatch₂ hbase (hgeoInv b) hdeep hsep
      (List.mem_of_getElem? hme) (List.mem_of_getElem? hmf) hy hz heq
  refine ⟨e, f, ?_, ?_, hef⟩
  · rw [← hxe]
    exact hx
  · rw [← hXf]
    exact hX

/-- **The mixed case of step (c), from the polygon estimate.**

Two matched pairs, ordered, with the two gaps close and the first gap small
against the length of the relator: impossible.  This is the case in which one
member of the symmetrized closure is a rotation of the relator and the other a
rotation of its formal inverse; the other mixed case is this one with the two
members exchanged. -/
theorem not_mixedMatch {D : GGT.RelGenSet G Bool}
    (hbase : IsSymmetricGeneratingSet D.base) {a : Bool → G}
    (hinj : ∀ b : Bool, Function.Injective (fun n : ℕ => a b ^ n))
    {eps rho : ℕ} {ms : List ℕ} (hnodup : ms.Nodup)
    (hgeoInv : ∀ (t : Bool) (i j : ℕ) (x x' : G), wordNorm D.base x ≤ eps →
      wordNorm D.base x' ≤ eps → a t ^ i ∉ D.relBall t rho →
        (a t ^ j)⁻¹ ∉ D.relBall t rho → x * a t ^ i * x' = (a t ^ j)⁻¹ →
          x ∈ D.fam t ∧ x' ∈ D.fam t)
    (hdeep : ∀ m ∈ ms, ∀ t : Bool, a t ^ m ∉ D.relBall t rho ∧
      (a t ^ m)⁻¹ ∉ D.relBall t rho)
    (hsep : ∀ i ∈ ms, ∀ j ∈ ms, i ≠ j → ∀ t : Bool, ∀ x ∈ D.relBall t eps,
      ∀ x' ∈ D.relBall t eps,
        x * a t ^ i * x' ≠ a t ^ j ∧ x * a t ^ i * x' ≠ (a t ^ j)⁻¹)
    {p : List G} {c c' i₁ i₂ j₁ j₂ gapSlack : ℕ}
    (hi₂ : i₂ < (relatorWord₂ p (a false) (a true) ms).length)
    (hj₂ : j₂ < (relatorWord₂ p (a false) (a true) ms).length)
    (hii : i₁ < i₂) (hjj : j₁ < j₂)
    {b₁ b₂ : Bool} {x₁ X₁ y₁ z₁ x₂ X₂ y₂ z₂ : G}
    (hx₁ : ((relatorWord₂ p (a false) (a true) ms).rotate c)[i₁]?
      = some (GGT.RelLetter.comp b₁ x₁))
    (hX₁ : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c')[j₁]?
      = some (GGT.RelLetter.comp b₁ X₁))
    (hy₁ : wordNorm D.base y₁ ≤ eps) (hz₁ : wordNorm D.base z₁ ≤ eps)
    (hval₁ : X₁ = y₁ * x₁ * z₁)
    (hx₂ : ((relatorWord₂ p (a false) (a true) ms).rotate c)[i₂]?
      = some (GGT.RelLetter.comp b₂ x₂))
    (hX₂ : ((RelWord.revInv
        (relatorWord₂ p (a false) (a true) ms)).rotate c')[j₂]?
      = some (GGT.RelLetter.comp b₂ X₂))
    (hy₂ : wordNorm D.base y₂ ≤ eps) (hz₂ : wordNorm D.base z₂ ≤ eps)
    (hval₂ : X₂ = y₂ * x₂ * z₂)
    (hclose : j₂ - j₁ ≤ i₂ - i₁ + gapSlack)
    (hsmall : 2 * (i₂ - i₁) + gapSlack
      < (relatorWord₂ p (a false) (a true) ms).length) : False := by
  have hinj' : ∀ b : Bool,
      Function.Injective (fun n : ℕ => (if b then a true else a false) ^ n) := by
    intro b
    rw [ite_apply_eq a b]
    exact hinj b
  obtain ⟨e₁, f₁, hxe₁, hXf₁, hef₁⟩ :=
    exponent_eq_of_mirroredPair hbase hgeoInv hdeep hsep (by omega) (by omega)
      hx₁ hX₁ hy₁ hz₁ hval₁
  obtain ⟨e₂, f₂, hxe₂, hXf₂, hef₂⟩ :=
    exponent_eq_of_mirroredPair hbase hgeoInv hdeep hsep hi₂ hj₂
      hx₂ hX₂ hy₂ hz₂ hval₂
  exact not_mirroredMatch_of_gap hinj' hnodup hi₂ hj₂ hii hjj hef₁ hef₂
    hxe₁ hXf₁ hxe₂ hXf₂ hclose hsmall

end Mixed

end HullSC
end GroupApproximation

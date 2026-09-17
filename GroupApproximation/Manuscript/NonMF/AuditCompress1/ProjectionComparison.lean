import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import GroupApproximation.Meta.AxiomGuard

/-!
# Equivalent dominated projections in a finite algebra are equal

`non_mf_groups_exist.tex`, proof of Lemma `lem:stable-finite`, lines 454--456:

> Finally, if $p\le q$ are equivalent projections in a finite algebra
> $B$ and $w$ is a partial isometry with $w^*w=q$ and $ww^*=p$, then
> $w=qwq$, so $w+(1-q)$ is an isometry of $B$ and hence unitary; therefore
> $p+(1-q)=(w+(1-q))(w+(1-q))^*=1$ and $p=q$.

The endpoint takes a unital C*-algebra `B` that is finite (every isometry is
a unitary), projections `p`, `q` with `p ≤ q`, and `w` with `w*w = q` and
`ww* = p`. Its conclusion lists every printed step:
* `w = qwq`;
* `w + (1 - q)` is an isometry;
* `w + (1 - q)` is a unitary;
* `p + (1 - q) = (w + (1 - q))(w + (1 - q))*`;
* that product is `1`;
* `p = q`.

For projections, `p ≤ q` is written `q p = p`, the same convention as the
corpus sentence `OneSidedMFRadical.sentence_70c4de929477`.

Proof route (the printed one).
* `(w - wq)*(w - wq) = q - q - q + q = 0`, so the C*-identity gives `wq = w`.
* `ww* = p ≤ q` gives `pw = w` and then `qw = q(pw) = pw = w`. So `w = qwq`,
  and taking adjoints gives `w*q = w*` and `qw* = w*`.
* Expanding `(w + (1-q))*(w + (1-q))` with these identities gives `1`.
  Finiteness makes `w + (1-q)` a unitary.
* Expanding `(w + (1-q))(w + (1-q))*` gives `p + (1 - q)`, which is therefore
  `1`, so `p = q`.
-/

namespace GroupApproximation.Manuscript.NonMF.AuditCompress1

/-- tex 454--456: in a finite C*-algebra, let `p ≤ q` be projections (`qp = p`)
and `w` a partial isometry with `w*w = q` and `ww* = p`. Then `w = qwq`,
`w + (1-q)` is an isometry and hence a unitary, and
`p + (1-q) = (w + (1-q))(w + (1-q))* = 1`, so `p = q`. -/
theorem manuscriptSentence_equivalentDominatedProjectionsEqual
    {B : Type*} [CStarAlgebra B]
    (hfinite : ∀ x : B, star x * x = 1 → x * star x = 1) {p q : B}
    (_hp : IsStarProjection p) (hq : IsStarProjection q) (hle : q * p = p)
    {w : B} (hw1 : star w * w = q) (hw2 : w * star w = p) :
    w = q * w * q ∧
      star (w + (1 - q)) * (w + (1 - q)) = 1 ∧
      (w + (1 - q)) * star (w + (1 - q)) = 1 ∧
      p + (1 - q) = (w + (1 - q)) * star (w + (1 - q)) ∧
      p + (1 - q) = 1 ∧
      p = q := by
  have hqq : q * q = q := hq.isIdempotentElem
  have hqs : star q = q := hq.isSelfAdjoint.star_eq
  -- `w q = w`, from `(w - wq)*(w - wq) = 0`
  have hd : star (w - w * q) * (w - w * q) = 0 := by
    have hexp : star (w - w * q) * (w - w * q)
        = star w * w - star w * w * q - q * (star w * w)
          + q * (star w * w) * q := by
      rw [star_sub, star_mul, hqs]
      noncomm_ring
    rw [hexp, hw1, hqq, hqq]
    abel
  have hwq : w * q = w :=
    (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp hd)).symm
  -- `p w = w` and `q w = w`
  have hpw : p * w = w := by
    rw [← hw2, mul_assoc, hw1, hwq]
  have hqw : q * w = w := by
    calc q * w = q * (p * w) := by rw [hpw]
      _ = q * p * w := by rw [mul_assoc]
      _ = p * w := by rw [hle]
      _ = w := hpw
  have hwqq : w = q * w * q := by
    rw [hqw, hwq]
  -- the adjoint identities
  have hsw : star w * q = star w := by
    have h := congrArg star hqw
    rwa [star_mul, hqs] at h
  have hqsw : q * star w = star w := by
    have h := congrArg star hwq
    rwa [star_mul, hqs] at h
  -- `w + (1 - q)` is an isometry
  have hiso : star (w + (1 - q)) * (w + (1 - q)) = 1 := by
    have hexp : star (w + (1 - q)) * (w + (1 - q))
        = star w * w + star w - star w * q + w - q * w + 1 - q - q + q * q := by
      rw [star_add, star_sub, star_one, hqs]
      noncomm_ring
    rw [hexp, hw1, hsw, hqw, hqq]
    abel
  -- hence unitary, by finiteness
  have hunit : (w + (1 - q)) * star (w + (1 - q)) = 1 := hfinite _ hiso
  -- `p + (1 - q) = (w + (1 - q))(w + (1 - q))*`
  have hpq : p + (1 - q) = (w + (1 - q)) * star (w + (1 - q)) := by
    have hexp : (w + (1 - q)) * star (w + (1 - q))
        = w * star w + w - w * q + star w - q * star w + 1 - q - q + q * q := by
      rw [star_add, star_sub, star_one, hqs]
      noncomm_ring
    rw [hexp, hw2, hwq, hqsw, hqq]
    abel
  have hone : p + (1 - q) = 1 := hpq.trans hunit
  have hpeq : p = q := by
    calc p = p + (1 - q) + q - 1 := by abel
      _ = q := by
        rw [hone]
        abel
  exact ⟨hwqq, hiso, hunit, hpq, hone, hpeq⟩

#audit_axioms manuscriptSentence_equivalentDominatedProjectionsEqual

end GroupApproximation.Manuscript.NonMF.AuditCompress1

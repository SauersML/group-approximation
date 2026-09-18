import GroupApproximation.GGT.VanKampen.RelativeGreendlinger
import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet

/-!
# GL06h2: a short word is never a conjugate of a relator value, statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

A relator of an `OsinCCondition` family is a long `(λ, c)`-quasi-geodesic word whose cyclic
rotations are again relators.  Its value then has linear progress along its powers, so no conjugate
of it is the value of a word of length at most `ε + ε` once `ρ` is large.

* `ShortWordNeConjRelatorStatement`: the exact statement proved as
  `Full.GL06h2.shortWord_ne_conj_relator` (in `Full/GL06h2/ShortConjugate`).

This is not a literature statement; it is a clause of the induction step of Lemma 9.7(b).
-/

namespace GroupApproximation.Full.GL06h2

universe u w

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

/-- **A short word is not a conjugate of a relator value, beyond thresholds** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  The hypotheses match
`Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement`. -/
def ShortWordNeConjRelatorStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ word ∈ W, RelLetter.listVal word ≠ 1 →
                ∀ (g : G) (u : List (RelLetter G Lambda)),
                  (∀ x ∈ u, (symmetricLabelAlphabet D).IsLetter x) →
                  u.length ≤ eps + eps →
                    RelLetter.listVal u ≠ g * RelLetter.listVal word * g⁻¹

end GroupApproximation.Full.GL06h2

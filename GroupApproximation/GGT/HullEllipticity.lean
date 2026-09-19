import GroupApproximation.GGT.HullYiAlphabetTransfer

/-!
# Ellipticity, and the one direction in which it transfers

Hull, *Small cancellation in acylindrically hyperbolic groups* (arXiv:1308.4345),
Lemma `ee`, concludes that finitely many prescribed elements are *elliptic* with
respect to the action of `G` on an enlarged relative Cayley graph.  The
repository had no vocabulary for that: `HullGeometry.IsLoxodromic` is the linear
lower bound on the orbit map, and nothing named the bounded-orbit condition
opposite to it.  This module supplies it, together with the two transfer facts
Lemma `ee` reads.

`IsElliptic g x` says the `⟨g⟩`-orbit of `x` is bounded --- the quantifier is
over `ℤ`, not `ℕ`, because Hull's conclusion is about the cyclic *subgroup*.  For
an isometric action the two ranges agree, but the `ℤ` form is the honest one and
is what the consumer below produces anyway, so no equivalence lemma is stated:
`isElliptic_base_of_mem_subgroup` gets every power at once out of
`Subgroup.zpow_mem`, and an `ℕ`-to-`ℤ` bridge would be vocabulary before need.

## The two transfer facts, and why their directions are opposite

**Ellipticity transfers UP to a larger alphabet** (`isElliptic_base_of_subset`),
and this is the step that opens Hull's proof: *"since enlarging the generating
set does not decrease the set of elliptic elements, it suffices to prove the case
`m = 1`"*.  Over a larger alphabet distances are smaller, so a bound stays a
bound with the same constant.

**Loxodromy transfers DOWN to a smaller alphabet**, which is Hull's Lemma A.1 and
already lives in `GGT/HullYiAlphabetTransfer.lean`.  The two directions are
opposite for the same reason --- a linear lower bound over the larger alphabet is
the stronger statement --- and both are the single inequality
`HullSC.dist_base_le_of_subset`, read once from each side.  Getting them
backwards is easy and would be invisible at the statement, so they are stated
adjacently and proved from the same lemma.

## Model tests

The predicate is neither vacuous nor everywhere true, and both witnesses are
proved rather than asserted: `isElliptic_one` puts the identity in it, and
`IsLoxodromic.not_isElliptic` keeps every loxodromic element out.  The second is
also the consistency check against Bowditch's dichotomy
(`GGT.ElementaryBowditchProof`), which asserts that under an acylindrical action
these two classes exhaust the group; that they are disjoint is proved here and is
not part of the citation.
-/

namespace GroupApproximation

universe u v

namespace HullGeometry

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## The predicate -/

/-- **`g` is elliptic at `x`**: the `⟨g⟩`-orbit of `x` is bounded.

Stated over `ℤ` because Hull's conclusion is about the cyclic subgroup generated
by the element, not about its forward powers alone. -/
def IsElliptic (g : G) (x : X) : Prop :=
  ∃ C : ℝ, ∀ n : ℤ, dist x ((g ^ n) • x) ≤ C

/-- **The identity is elliptic**, with bound `0`: every power is the identity and
fixes the basepoint.  This is the non-vacuity half of the model test. -/
theorem isElliptic_one (x : X) : IsElliptic (1 : G) x :=
  ⟨0, fun n => by
    rw [one_zpow, one_smul]
    exact le_of_eq (dist_self x)⟩

/-- **A loxodromic element is not elliptic.**  The linear lower bound on the
orbit map outgrows any constant, so the two classes are disjoint.

This is the second half of the model test, and it is what makes Bowditch's
dichotomy a genuine dichotomy rather than a covering: that the two classes
*exhaust* an acylindrical action is the citation, that they do not *overlap* is
this proof. -/
theorem IsLoxodromic.not_isElliptic {g : G} {x : X} (hlox : IsLoxodromic g x) :
    ¬ IsElliptic g x := by
  rintro ⟨C, hC⟩
  obtain ⟨l, hl, B, _hB, hle⟩ := hlox
  obtain ⟨N, hN⟩ := exists_nat_gt ((C + B) / l)
  have hlin : C + B < l * (N : ℝ) := by
    rw [div_lt_iff₀ hl] at hN
    linarith
  have hnat : dist x ((g ^ (N : ℕ)) • x) ≤ C := by
    have h := hC (N : ℤ)
    rwa [zpow_natCast] at h
  have hlow := hle N
  linarith

end HullGeometry

namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## Producing ellipticity: a letter has a bounded orbit -/

/-- **An element all of whose powers are letters is elliptic at the basepoint**,
with bound `1`: each power is a single letter, so it moves the identity vertex a
distance at most one. -/
theorem isElliptic_base_of_zpow_mem {G : Type u} [Group G] {A : Alphabet G}
    {g : G} (h : ∀ n : ℤ, g ^ n ∈ A.carrier) :
    IsElliptic g (Cayley.base A) := by
  refine ⟨1, fun n => ?_⟩
  simp only [Cayley.dist_eq, Cayley.val_base, Cayley.val_smul, mul_one,
    wordDist_one_left]
  exact_mod_cast wordNorm_le_one_of_mem (h n)

/-- **An element of a subgroup swallowed by the alphabet is elliptic.**  This is
the form Hull's Lemma `ee` delivers its conclusion in: the enlargement puts the
whole elementary closure `E(a)` into the alphabet, and `a` lies in it, so every
power of `a` is a letter.

The subgroup hypothesis is what makes the `ℤ` range free --- `Subgroup.zpow_mem`
gives negative powers along with positive ones, so no isometry argument is
needed to close the orbit under inversion. -/
theorem isElliptic_base_of_mem_subgroup {G : Type u} [Group G] {A : Alphabet G}
    {H : Subgroup G} (hHA : (H : Set G) ⊆ A.carrier) {g : G} (hg : g ∈ H) :
    IsElliptic g (Cayley.base A) :=
  isElliptic_base_of_zpow_mem (fun n => hHA (SetLike.mem_coe.mpr (zpow_mem hg n)))

/-! ## Transfer: ellipticity goes UP -/

/-- **Enlarging the alphabet preserves ellipticity**, with the same constant.

This is the sentence Hull's proof of Lemma `ee` opens with --- *"since enlarging
the generating set does not decrease the set of elliptic elements, it suffices to
prove the case `m = 1`"* --- and it is what licenses the induction on the number
of prescribed elements: an element made elliptic at one stage stays elliptic
through every later enlargement.

Contrast `isLoxodromic_base_of_subset`, which runs the other way for the same
reason: both are `dist_base_le_of_subset`, which bounds the displacement over the
larger alphabet by the displacement over the smaller one. -/
theorem isElliptic_base_of_subset {G : Type u} [Group G] {A A₁ : Alphabet G}
    (hAA : A.carrier ⊆ A₁.carrier) {g : G}
    (hell : IsElliptic g (Cayley.base A)) : IsElliptic g (Cayley.base A₁) := by
  obtain ⟨C, hC⟩ := hell
  exact ⟨C, fun n => le_trans (dist_base_le_of_subset hAA (g ^ n)) (hC n)⟩

/-- The family form, which is how the induction in Lemma `ee` consumes it: the
elements made elliptic at earlier stages are still elliptic at the last one. -/
theorem isElliptic_base_of_subset_family {G : Type u} [Group G]
    {A A₁ : Alphabet G} (hAA : A.carrier ⊆ A₁.carrier) {ι : Type*} {g : ι → G}
    (hell : ∀ i, IsElliptic (g i) (Cayley.base A)) :
    ∀ i, IsElliptic (g i) (Cayley.base A₁) :=
  fun i => isElliptic_base_of_subset hAA (hell i)

end HullSC
end GroupApproximation

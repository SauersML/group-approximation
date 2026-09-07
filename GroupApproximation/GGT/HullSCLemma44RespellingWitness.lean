import GroupApproximation.GGT.HullSCLemma44JointRelabel
import GroupApproximation.Meta.AxiomGuard

/-!
# `HullRelatorRespellingStatement` is too strong as printed

`HullRelatorRespellingStatement` used to quantify over an **arbitrary**
hyperbolically embedded `original`, with no relation to Hull's alphabet `A`,
while its own reduction carried `original.alphabet.carrier ⊆ A.alphabet.carrier`
throughout.  This file is the evidence that the missing containment was not
bookkeeping, and the commit that lands it threads the containment back in.

The containment was never a new hypothesis.
`HullLemma44CanonicalQuotientFamilyInclusionJointStatement` -- the statement the
Theorem C assembly actually consumes -- has carried it all along;
`hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_canonical_of_controls`
binds it and uses it, and simply did not pass it down to
`FamilyInclusionRelativeControlStatement`, which in turn did not pass it to the
re-spelling statement.  A hypothesis dropped twice on the way down.

Because the repair lands with this file, the collapse below is stated against
`HullRelatorRespellingStatementUnguarded`, a named copy of the statement as it
stood before.  The witness was built to exhibit an `original` that no re-spelling
can survive; the repaired statement excludes precisely that `original` and
nothing else that could be found; so the collapse no longer follows from it.  A
repair that left the witness still going through would have been the worrying
outcome, because it would have meant the added hypothesis did not bite on the
pathology it was chosen for.

## Two tooling hazards this chain is exposed to

Both were hit while making the repair, and both belong here rather than in a
commit message, because this is where the next person editing the chain will be.

`git grep PAT -- '*.lean'` searches the LOCAL INDEX, and under this repository's
plumbing-push protocol the local HEAD lags `origin/main`, so files landed since
then are untracked locally and invisible to it.  Asking it which files consume
`FamilyInclusionRelativeControlStatement` returned one; the answer is two.  The
one it hid, `GGT/HullSCLemma44QuasiGeodesicBridge`, holds
`familyInclusionRelativeControlStatement_of_quasiGeodesic_of_respelling` -- the
producer the Theorem C assembly actually routes through.  Ask
`git grep PAT origin/main -- '*.lean'` for what is landed, or `grep -r` for the
tree you are about to build; the bare form answers neither question.

The working tree is shared with other live sessions, and an in-flight edit can be
replaced by `origin/main`'s copy without warning.  That happened here to
`HullSCLemma44QuasiGeodesicBridge` -- the file on the live path -- while the edits
to `HullSCLemma44FamilyAssembly`, holding the route nothing consumes, survived.
The failure mode was therefore: statements edited, unused producer threaded, used
producer silently reverted.  It surfaced only because both producers prove the
same `Prop`.  Re-verify that your edits are still present immediately before
building, not only after making them.

The witness is `coneEverythingRelGenSet`: everything in the base, and **no
peripheral family at all**.  Its relative Cayley graph is the complete graph on
`G`, so it is hyperbolic; and its local-finiteness clause is quantified over
`Empty`, so it holds vacuously.  That second point is the whole construction.
A degenerate family put in `fam` is killed by
`not_isHyperbolicallyEmbedded_of_fam_subset_base`; moving the degeneracy into
the base and deleting the families removes the only clause that was checking
anything.

Over such an alphabet a Lemma 4.4 input has no nonempty member.  Its relators
must have length at least `rho`, and `RelatorRespellingAt` separately forces
`20 * (eps + 1) ≤ rho`, so at least `20`; but the quasi-geodesic clause measures
the relator in a graph of diameter one, which caps its length at `8`.  So the
family is empty, and a re-spelling over this `original` forces the source
relators to have trivial normal closure.

## What this does and does not establish

It does **not** refute `HullRelatorRespellingStatement` outright, and no
declaration here claims to.  What it proves is that the statement collapses:
whatever thresholds it returns, every Lemma 4.4 input over the selected
auxiliary family at those thresholds is normally trivial.  Turning that into a
refutation needs one nonempty such input with nontrivial normal closure, and
none is constructed in this development -- indeed
`SimultaneousAuxiliaryPeripheralSelection` is itself still an unproved input, so
no `AuxiliaryPeripheralFamily` is constructed either.  Both gaps are real and
neither is closed here.

## A pointer the corpus does not otherwise carry

`HullSCLemma44JointRelabel`'s "What is left" section says the original half
"stays an input ... It is named next", and stops there.  It goes considerably
further than that: `GGT/HullSCLemma44OriginalExpansion` reduces the original
half to `OriginalRelatorExpansion`, five metric clauses for a single word, with
the symmetrization, strong boundedness and normal-closure bookkeeping already
discharged.  Nothing pointed from the statement to that file, so the open
mathematics reads as larger than it is.

The repair does not depend on that question.  Adding
`original.alphabet.carrier ⊆ A.alphabet.carrier` to the statement kills this
witness outright, because `HullGeneratingSet.nonElementary` needs two
independent loxodromics and a bounded graph has none, so `A.alphabet.carrier`
is never all of `G`.  That is exactly the hypothesis the reduction already
demands.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Witness

variable (G : Type u) [Group G]

/-- **Everything in the base, no peripheral family.**  A legal relative
generating set: the alphabet is all of `G`, which is symmetric and generating,
and there are no components to cone off. -/
def coneEverythingRelGenSet : GGT.RelGenSet G Empty where
  base := Set.univ
  fam := fun l => l.elim
  symmetricGenerating := by
    refine ⟨fun x _ => Set.mem_union_left _ (Set.mem_univ _), ?_⟩
    rw [eq_top_iff, ← Subgroup.closure_univ]
    exact Subgroup.closure_mono Set.subset_union_left

/-- The alphabet of the witness is the whole group. -/
theorem coneEverythingRelGenSet_alphabet_carrier :
    (coneEverythingRelGenSet G).alphabet.carrier = (Set.univ : Set G) :=
  Set.univ_union _

/-- Every pair of group elements is one letter apart. -/
theorem wordDist_coneEverythingRelGenSet_le_one (x y : G) :
    wordDist (coneEverythingRelGenSet G).alphabet.carrier x y ≤ 1 := by
  rw [coneEverythingRelGenSet_alphabet_carrier]
  exact wordNorm_le_one_of_mem (Set.mem_univ _)

/-- The relative Cayley graph of the witness has diameter at most one. -/
theorem dist_coneEverythingRelGenSet_le_one
    (x y : Cayley (coneEverythingRelGenSet G).alphabet) : dist x y ≤ 1 := by
  have h := wordDist_coneEverythingRelGenSet_le_one G (Cayley.val x) (Cayley.val y)
  show ((wordDist (coneEverythingRelGenSet G).alphabet.carrier
    (Cayley.val x) (Cayley.val y) : ℕ) : ℝ) ≤ 1
  exact_mod_cast h

/-- **The witness is hyperbolically embedded.**  Hyperbolicity is the
four-point condition at `δ = 1`, which a space of diameter one satisfies because
every Gromov product lies in `[0, 1]`; local finiteness is quantified over
`Empty`. -/
theorem isHyperbolicallyEmbedded_coneEverything :
    (coneEverythingRelGenSet G).IsHyperbolicallyEmbedded := by
  refine ⟨⟨1, ?_⟩, fun l => l.elim⟩
  intro w x y z
  have hnonneg : 0 ≤ gromovProduct x z w := by
    have htri : dist x z ≤ dist x w + dist w z := dist_triangle x w z
    have hcomm : dist w z = dist z w := dist_comm w z
    unfold gromovProduct
    linarith
  have hxy : gromovProduct x y w ≤ 1 := by
    have h1 := dist_coneEverythingRelGenSet_le_one G x w
    have h2 := dist_coneEverythingRelGenSet_le_one G y w
    have h3 : 0 ≤ dist x y := dist_nonneg
    unfold gromovProduct
    linarith
  have hmin : min (gromovProduct x y w) (gromovProduct y z w)
      ≤ gromovProduct x y w := min_le_left _ _
  linarith

end Witness

section Collapse

variable {G : Type u} [Group G]

/-- **A Lemma 4.4 input over the witness is empty.**  `long` forces a relator to
have at least `rho ≥ 20` letters; the quasi-geodesic clause, read at the two
ends of the relator, caps it at `8` because the alphabet is the whole group. -/
theorem eq_empty_of_isLemma44Input_coneEverything
    {W : Set (List (GGT.RelLetter G Empty))} {eps rho : ℕ} {mu : ℝ}
    (h20 : 20 * (eps + 1) ≤ rho)
    (h : RelWord.IsLemma44Input (coneEverythingRelGenSet G) W eps mu rho) :
    W = ∅ := by
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hv
  have hlong : rho ≤ v.length := h.toIsSmallCancellation.long v hv
  have hlow := (h.quasiGeodesic v hv 0 v.length (Nat.zero_le _) le_rfl).1
  simp only [List.take_zero, List.take_length, Nat.sub_zero,
    GGT.RelLetter.listVal_nil] at hlow
  have hcap : wordDist (coneEverythingRelGenSet G).alphabet.carrier
      1 (GGT.RelLetter.listVal v) ≤ 1 :=
    wordDist_coneEverythingRelGenSet_le_one G _ _
  have hcapR : ((wordDist (coneEverythingRelGenSet G).alphabet.carrier
      1 (GGT.RelLetter.listVal v) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hcap
  have hlenR : ((v.length : ℕ) : ℝ) ≤ 8 := by
    push_cast at hlow ⊢
    linarith
  have hlen : v.length ≤ 8 := by exact_mod_cast hlenR
  omega

/-- **A re-spelling over the witness forces trivial normal closure.**  The
re-spelled family is empty, and the re-spelling clause says its normal closure
is the source one. -/
theorem normalClosure_eq_bot_of_relatorRespellingAt_coneEverything
    {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
    {eps0 rho0 : ℕ} {mu : ℝ}
    (h : RelatorRespellingAt (coneEverythingRelGenSet G) W eps0 rho0 mu) :
    Subgroup.normalClosure (GGT.RelLetter.listVal '' W) = ⊥ := by
  obtain ⟨W', eps, rho, _, _, h20, hclosure, hinput⟩ := h
  have hW' : W' = ∅ := eq_empty_of_isLemma44Input_coneEverything h20 hinput
  subst hW'
  rw [← hclosure, Set.image_empty]
  simp

end Collapse

section Statement

/-- The witness's joint family: the selected auxiliary family read along
`Empty ⊕ AuxiliaryPeripheralIndex k ≃ AuxiliaryPeripheralIndex k`.  Its
hyperbolic embeddedness is the selected family's own, transported by
`relGenSetReindex_isHyperbolicallyEmbedded`. -/
def emptyJointIndexEquiv (k : ℕ) :
    Sum Empty (AuxiliaryPeripheralIndex k) ≃ AuxiliaryPeripheralIndex k :=
  Equiv.emptySum Empty (AuxiliaryPeripheralIndex k)

noncomputable def coneEverythingJoint {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S) :
    GGT.RelGenSet G (Sum Empty (AuxiliaryPeripheralIndex k)) :=
  relGenSetReindex selected.rel (emptyJointIndexEquiv k)

/-- The joint family's components at the auxiliary indices are the selected
ones.  Stated as its own `rfl` lemma: discovering this defeq while unifying the
whole application of the statement is what times out. -/
theorem coneEverythingJoint_fam_inr {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    (i : AuxiliaryPeripheralIndex k) :
    (coneEverythingJoint selected).fam (Sum.inr i) = selected.rel.fam i := rfl

/-- The joint family is hyperbolically embedded, by the selected family's own
embedding read along the index equivalence. -/
theorem coneEverythingJoint_isHyperbolicallyEmbedded {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S) :
    (coneEverythingJoint selected).IsHyperbolicallyEmbedded :=
  relGenSetReindex_isHyperbolicallyEmbedded selected.rel (emptyJointIndexEquiv k)
    selected.embedded

/-- **The re-spelling statement as it stood before the containment was threaded
in.**  This is `HullRelatorRespellingStatement` verbatim at `026b80ae`, minus
nothing: at that revision it carried no relation between `original` and Hull's
alphabet `A`.

It is kept as a named copy for one reason.  The repair landed with this file
adds `original.alphabet.carrier ⊆ A.alphabet.carrier` to the live statement, and
the witness below does not satisfy it -- `A.alphabet.carrier` is never all of
`G`, because `HullGeneratingSet.nonElementary` needs two independent loxodromics
and a bounded graph has none.  So the collapse can no longer be stated against
the live statement, which is exactly the point of the repair.  Stating it
against this copy keeps the defect on the record instead of deleting the
evidence along with the bug.

**The live statement is `HullRelatorRespellingStatement`, in
`GGT/HullSCLemma44FamilyAssembly`.**  Use that one.  This copy is retained
history: nothing proves it, and NOTHING SHOULD CONSUME IT.  A declaration taking
`HullRelatorRespellingStatementUnguarded` as a hypothesis would be assuming the
form that the witness below refutes, which is a defect rather than a weakening;
if one ever appears, it is a bug and not a convenience. -/
def HullRelatorRespellingStatementUnguarded : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k))),
    original.IsHyperbolicallyEmbedded →
    joint.IsHyperbolicallyEmbedded →
    (∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam) →
    (∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i) →
    ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 1000 →
      ∀ eps0 rho0 : ℕ,
        ∃ eps rho : ℕ,
          ∀ W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))),
            RelWord.IsLemma44Input selected.rel W eps mu rho →
              RelatorRespellingAt original W eps0 rho0 mu ∧
                RelatorRespellingAt joint W eps0 rho0 mu

/-- **The unguarded re-spelling statement collapses.**  Whatever thresholds it
returns, every Lemma 4.4 input over the selected auxiliary family at those
thresholds has trivial normal closure.

This is a collapse, not a refutation: it is decisive exactly when one nonempty
such input with nontrivial normal closure is exhibited, and none is constructed
in this development.  What it does show is that the statement's `original` is
unguarded -- the printed form admits an `original` no re-spelling can survive,
and the containment its own reduction carries is what excludes it. -/
theorem normalClosure_eq_bot_of_hullRelatorRespellingUnguarded
    (h : HullRelatorRespellingStatementUnguarded.{u, 0})
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} (selected : AuxiliaryPeripheralFamily A N S)
    (mu : ℝ) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 1000) :
    ∃ eps rho : ℕ,
      ∀ W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))),
        RelWord.IsLemma44Input selected.rel W eps mu rho →
          Subgroup.normalClosure (GGT.RelLetter.listVal '' W) = ⊥ := by
  obtain ⟨eps, rho, hres⟩ :=
    @h G ‹Group G› A N k S selected Empty (coneEverythingRelGenSet G)
      (coneEverythingJoint selected)
      (isHyperbolicallyEmbedded_coneEverything G)
      (coneEverythingJoint_isHyperbolicallyEmbedded selected)
      (fun l => l.elim)
      (fun i => (coneEverythingJoint_fam_inr selected i).trans (selected.fam_eq i))
      mu hmu hmuUpper 0 0
  refine ⟨eps, rho, fun W hW => ?_⟩
  exact normalClosure_eq_bot_of_relatorRespellingAt_coneEverything (hres W hW).1

/-- **The refutation, with its hypothesis written out.**  If one selected
auxiliary family admits, at every pair of thresholds, a Lemma 4.4 input whose
normal closure is nontrivial, then `HullRelatorRespellingStatement` is false.

The hypothesis is exactly what this development does not supply, which is why
the refutation is stated conditionally rather than asserted.  It is stated at
all so that anyone who later builds such a family gets the refutation by
application rather than by repeating the argument. -/
theorem not_hullRelatorRespellingStatementUnguarded_of_nontrivialInput
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} (selected : AuxiliaryPeripheralFamily A N S)
    (mu : ℝ) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 1000)
    (hinput : ∀ eps rho : ℕ,
      ∃ W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))),
        RelWord.IsLemma44Input selected.rel W eps mu rho ∧
          Subgroup.normalClosure (GGT.RelLetter.listVal '' W) ≠ ⊥) :
    ¬ HullRelatorRespellingStatementUnguarded.{u, 0} := by
  intro h
  obtain ⟨eps, rho, hcollapse⟩ :=
    normalClosure_eq_bot_of_hullRelatorRespellingUnguarded h selected mu hmu hmuUpper
  obtain ⟨W, hW, hne⟩ := hinput eps rho
  exact hne (hcollapse W hW)

end Statement

#audit_axioms isHyperbolicallyEmbedded_coneEverything
#audit_axioms eq_empty_of_isLemma44Input_coneEverything
#audit_axioms normalClosure_eq_bot_of_hullRelatorRespellingUnguarded
#audit_axioms not_hullRelatorRespellingStatementUnguarded_of_nontrivialInput

end HullSC
end GroupApproximation

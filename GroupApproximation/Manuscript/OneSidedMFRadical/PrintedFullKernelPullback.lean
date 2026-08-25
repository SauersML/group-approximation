import GroupApproximation.Sofic.FullMFRadicalVisibleLocalization
import GroupApproximation.Manuscript.OneSidedMFRadical.LiteralMFClosure

/-!
# The printed full-kernel pullback proposition, sentence by sentence

`non_mf_groups_exist.tex`, `\section{MF-visible quotients}`: the opening
sentence, `\begin{proposition}[full-kernel pullback]\label{prop:full-kernel-pullback}`
with its three displays, and the three sentences that close the paragraph
(the mutually inverse correspondences, the isomorphism of largest MF-visible
quotients, and compatibility with composition).

`Sofic/FullMFRadicalClosurePullback.lean`,
`Sofic/FullMFRadicalQuotientLattice.lean` and
`Sofic/FullMFRadicalVisibleLocalization.lean` prove these statements in the
general form, with the group, the surjection and the normal subgroup as
caller-supplied binders.  A declaration of that shape is rejected by
`#audit_closed_axioms`, which throws on any leading binder, so this module
restates each printed sentence as a named `Prop` whose quantifiers live
*inside* the statement and proves it.  Nothing is assumed: every hypothesis
the manuscript prints is a hypothesis of the printed sentence, and it appears
inside the named proposition rather than in front of it.

No theorem from the literature is an input.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

noncomputable section

/-- The quotient of a countable group is countable.  The same local instance
carries the corresponding statements in `Sofic/ActualCoronaMFRadical.lean` and
`Sofic/FullMFRadicalClosurePullback.lean`. -/
local instance quotientGroupCountable {G : Type*} [Group G] (N : Subgroup G)
    [hN : N.Normal] [Countable G] :
    Countable (G ⧸ N) :=
  Function.Surjective.countable (@QuotientGroup.mk'_surjective G _ N hN)

/-- **`prop:full-kernel-pullback`, the three printed displays.**  For a
surjection `f : G → Q` of countable groups whose kernel is already inside the
MF radical of `G`:

* `Rad_MF(G) = f⁻¹(Rad_MF(Q))`;
* `cl_MF^G(N) = f⁻¹(cl_MF^Q(f(N)))` for every normal `N`;
* `G/N` is MF exactly when `ker f ≤ N` and `Q/f(N)` is MF.
-/
def PrintedFullKernelPullback : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (Q : Type) [Group Q] [Countable Q]
    (f : G →* Q) (hf : Function.Surjective f)
    (_hker : f.ker ≤ actualCoronaMFResidual G),
      actualCoronaMFResidual G = (actualCoronaMFResidual Q).comap f ∧
      (∀ (N : Subgroup G) (hN : N.Normal),
          @actualCoronaMFClosure G _ N hN =
            (@actualCoronaMFClosure Q _ (N.map f)
              (Subgroup.Normal.map hN f hf)).comap f) ∧
      (∀ (N : Subgroup G) (hN : N.Normal),
          letI := hN
          letI : (N.map f).Normal := Subgroup.Normal.map hN f hf
          (IsCDEOperatorMF (G ⧸ N) ↔
            f.ker ≤ N ∧ IsCDEOperatorMF (Q ⧸ (N.map f : Subgroup Q))))

/-- Closed proof of the three printed displays of `prop:full-kernel-pullback`. -/
theorem manuscriptPrintedFullKernelPullback : PrintedFullKernelPullback := by
  intro G _ _ Q _ _ f hf hker
  refine ⟨actualCoronaMFResidual_eq_comap_of_surjective_of_ker_le f hf hker,
    ?_, ?_⟩
  · intro N hN
    letI := hN
    exact actualCoronaMFClosure_eq_comap_map_of_surjective_of_ker_le f hf hker N
  · intro N hN
    letI := hN
    letI : (N.map f).Normal := Subgroup.Normal.map hN f hf
    exact isCDEOperatorMF_quotient_iff_map_of_surjective_of_ker_le f hf hker N

/-- **"In particular, the conclusion holds whenever `Rad_MF(ker f) = ker f`."**
Intrinsic fullness of the kernel is a sufficient hypothesis for the pullback
formula. -/
def PrintedFullKernelPullbackFromFullKernel : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (Q : Type) [Group Q] [Countable Q]
    (f : G →* Q), Function.Surjective f →
      actualCoronaMFResidual f.ker = ⊤ →
        actualCoronaMFResidual G = (actualCoronaMFResidual Q).comap f

/-- Closed proof of the "in particular" sentence. -/
theorem manuscriptPrintedFullKernelPullbackFromFullKernel :
    PrintedFullKernelPullbackFromFullKernel := by
  intro G _ _ Q _ _ f hf hfull
  exact actualCoronaMFResidual_eq_comap_of_surjective_of_kernel_eq_top f hf hfull

/-- **"Thus image under `f` and inverse image under `f` give mutually inverse,
inclusion-preserving correspondences between the normal subgroups that define
MF quotients of `G` and of `Q`."**  The two operations assemble into an order
isomorphism of the two lattices of MF-closed normal subgroups.  The statement
names the two maps explicitly -- image and inverse image along `f` -- and says
that each undoes the other, because "mutually inverse" is what the sentence
printed; asserting only that *some* order isomorphism exists would be weaker
than the printed claim.  Countability is required because `MFClosedNormalSubgroup`
is the lattice of closure-fixed normal subgroups, and it is exactly for
countable groups that those are the kernels with MF quotient. -/
def PrintedMFQuotientCorrespondence : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (Q : Type) [Group Q] [Countable Q]
    (f : G →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ actualCoronaMFResidual G),
      (∀ N : MFClosedNormalSubgroup G,
          MFClosedNormalSubgroup.comapOfInvisibleKernel f hf hker
            (MFClosedNormalSubgroup.mapOfInvisibleKernel f hf hker N) = N) ∧
        (∀ M : MFClosedNormalSubgroup Q,
          MFClosedNormalSubgroup.mapOfInvisibleKernel f hf hker
            (MFClosedNormalSubgroup.comapOfInvisibleKernel f hf hker M) = M) ∧
        (∀ N M : MFClosedNormalSubgroup G,
          (N.carrier.map f ≤ M.carrier.map f ↔ N.carrier ≤ M.carrier))

/-- Closed proof of the correspondence sentence. -/
theorem manuscriptPrintedMFQuotientCorrespondence :
    PrintedMFQuotientCorrespondence := by
  intro G _ _ Q _ _ f hf hker
  refine ⟨fun N => ?_, fun M => ?_, fun N M =>
    MFClosedNormalSubgroup.map_le_map_iff_of_invisibleKernel f hf hker N M⟩
  · exact (MFClosedNormalSubgroup.orderIsoOfInvisibleKernel f hf hker).left_inv N
  · exact (MFClosedNormalSubgroup.orderIsoOfInvisibleKernel f hf hker).right_inv M

/-- **"The map induced by `f` on the largest MF-visible quotients is an
isomorphism: `G/Rad_MF(G) ≅ Q/Rad_MF(Q)`."** -/
def PrintedVisibleQuotientIsomorphism : Prop :=
  ∀ (G : Type) [Group G] (Q : Type) [Group Q]
    (f : G →* Q) (_hf : Function.Surjective f)
    (_hker : f.ker ≤ actualCoronaMFResidual G),
      Function.Bijective (actualCoronaMFVisibleQuotientMap f) ∧
      Nonempty ((G ⧸ actualCoronaMFResidual G) ≃*
        (Q ⧸ actualCoronaMFResidual Q))

/-- Closed proof of the isomorphism sentence. -/
theorem manuscriptPrintedVisibleQuotientIsomorphism :
    PrintedVisibleQuotientIsomorphism := by
  intro G _ Q _ f hf hker
  exact ⟨actualCoronaMFVisibleQuotientMap_bijective_of_invisibleKernel f hf hker,
    ⟨actualCoronaMFVisibleQuotientEquivOfInvisibleKernel f hf hker⟩⟩

/-- **"These correspondences respect composition of surjective homomorphisms
with MF-invisible kernels."**  Composing two such surjections again gives one,
and both the lattice correspondence and the induced map on the largest
MF-visible quotients are functorial. -/
def PrintedCorrespondenceRespectsComposition : Prop :=
  ∀ (G : Type) [Group G] (Q : Type) [Group Q] (K : Type) [Group K]
    (f : G →* Q) (g : Q →* K)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hkerF : f.ker ≤ actualCoronaMFResidual G)
    (hkerG : g.ker ≤ actualCoronaMFResidual Q),
      Function.Surjective (g.comp f) ∧
      (g.comp f).ker ≤ actualCoronaMFResidual G ∧
      (∀ N : MFClosedNormalSubgroup G,
        MFClosedNormalSubgroup.mapOfInvisibleKernel (g.comp f)
            (surjective_monoidHom_comp f g hf hg)
            (ker_comp_le_actualCoronaMFResidual f g hf hkerF hkerG) N =
          MFClosedNormalSubgroup.mapOfInvisibleKernel g hg hkerG
            (MFClosedNormalSubgroup.mapOfInvisibleKernel f hf hkerF N)) ∧
      actualCoronaMFVisibleQuotientMap (g.comp f) =
        (actualCoronaMFVisibleQuotientMap g).comp
          (actualCoronaMFVisibleQuotientMap f)

/-- Closed proof of the composition sentence. -/
theorem manuscriptPrintedCorrespondenceRespectsComposition :
    PrintedCorrespondenceRespectsComposition := by
  intro G _ Q _ K _ f g hf hg hkerF hkerG
  exact ⟨surjective_monoidHom_comp f g hf hg,
    ker_comp_le_actualCoronaMFResidual f g hf hkerF hkerG,
    fun N =>
      MFClosedNormalSubgroup.mapOfInvisibleKernel_comp f g hf hg hkerF hkerG N,
    actualCoronaMFVisibleQuotientMap_comp f g⟩

/-- **The first two printed displays at the manuscript's own objects.**  The
statements above are phrased with the basis-free radical and closure; the
manuscript prints the natural-dimension radical `Rad_MF` and the closure
`cl_MF^G` of Section 1.  The two radicals are equal
(`manuscriptCoronaMFResidual_eq_actualCoronaMFResidual`) and so are the two
closures on countable groups (`literalMFClosure_eq_actualCoronaMFClosure`), so
this is the same mathematics said about the printed objects -- which is what a
referee checking the paper against the Lean needs to see. -/
def PrintedFullKernelPullbackAtPrintedObjects : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (Q : Type) [Group Q] [Countable Q]
    (f : G →* Q) (_hf : Function.Surjective f)
    (_hker : f.ker ≤ manuscriptCoronaMFResidual G),
      manuscriptCoronaMFResidual G = (manuscriptCoronaMFResidual Q).comap f ∧
      ∀ (N : Subgroup G) (_hN : N.Normal),
        literalMFClosure G N = (literalMFClosure Q (N.map f)).comap f

/-- Closed proof of the two printed displays at the printed radical and the
printed closure. -/
theorem manuscriptPrintedFullKernelPullbackAtPrintedObjects :
    PrintedFullKernelPullbackAtPrintedObjects := by
  intro G _ _ Q _ _ f hf hker
  have hkerA : f.ker ≤ actualCoronaMFResidual G := by
    rw [← manuscriptCoronaMFResidual_eq_actualCoronaMFResidual (G := G)]
    exact hker
  refine ⟨?_, ?_⟩
  · rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual (G := G),
      manuscriptCoronaMFResidual_eq_actualCoronaMFResidual (G := Q)]
    exact actualCoronaMFResidual_eq_comap_of_surjective_of_ker_le f hf hkerA
  · intro N hN
    letI := hN
    letI : (N.map f).Normal := Subgroup.Normal.map hN f hf
    rw [literalMFClosure_eq_actualCoronaMFClosure (G := G) N,
      literalMFClosure_eq_actualCoronaMFClosure (G := Q) (N.map f)]
    exact actualCoronaMFClosure_eq_comap_map_of_surjective_of_ker_le f hf hkerA N

/-- Every printed sentence of the full-kernel-pullback paragraph, in printed
order, as one closed proposition. -/
def PrintedFullKernelPullbackParagraph : Prop :=
  PrintedFullKernelPullback ∧
    PrintedFullKernelPullbackAtPrintedObjects ∧
    PrintedFullKernelPullbackFromFullKernel ∧
    PrintedMFQuotientCorrespondence ∧
    PrintedVisibleQuotientIsomorphism ∧
    PrintedCorrespondenceRespectsComposition

/-- Closed proof of the complete printed paragraph. -/
theorem manuscriptPrintedFullKernelPullbackParagraph :
    PrintedFullKernelPullbackParagraph :=
  ⟨manuscriptPrintedFullKernelPullback,
    manuscriptPrintedFullKernelPullbackAtPrintedObjects,
    manuscriptPrintedFullKernelPullbackFromFullKernel,
    manuscriptPrintedMFQuotientCorrespondence,
    manuscriptPrintedVisibleQuotientIsomorphism,
    manuscriptPrintedCorrespondenceRespectsComposition⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation

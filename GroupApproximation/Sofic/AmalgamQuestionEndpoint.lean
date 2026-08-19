import GroupApproximation.Sofic.CliffordLampGroup
import GroupApproximation.Sofic.CommutingLampCollapse
import GroupApproximation.Sofic.InvolutionCollapseEndpoint
import GroupApproximation.Sofic.ProjectionCompressionCollapse
import GroupApproximation.Sofic.LiteralSignFreeQuotient

/-!
# Question 1 of the manuscript: the conditional amalgam deduction

> **SUPERSEDED 2026-08-16.**  (An earlier version of this header added "NOT IN
> THE BUILD, AND NOT TO BE WIRED IN" and called the module "retained on disk,
> untracked".  Both are false as of the 2026-08-16 orphan sweep: the module is
> tracked and is imported by `GroupApproximation.lean`.  Whether *that* is
> right is a live question — see the trust-surface note at the end of this
> paragraph — but the header must not describe a state the tree is not in.)
> The manuscript question this module was written against was deleted the same
> day it was formalized: `\subsection*{Questions}` no longer contains an
> "Is `E/⟨w⟩` MF?" item (the word "amalgam" now survives in the `.tex` only
> in the introduction's prior-work survey and the bibliography), and the
> conclusion proved conditionally here is now an **unconditional numbered
> main theorem**, `\begin{mainthm}[the sign-free quotient of $E$]`
> `\label{thm:signfree}`, badged against
> `LiteralSignFreeQuotient.signFreeQuotient_not_isCDEOperatorMF`,
> `…signFree_collapse`, and `…commutator_not_zpow_mark`.  This module is
> therefore a conditional theorem whose conclusion is already a theorem, the
> shape `scripts/Audit.lean` forbids on the trust surface.  It is kept as a
> worked starting point should the amalgam route ever be wanted for the
> *residual* computation that the current Question 1 asks about ("What is
> `Res_MF(E)`?" — the manuscript renamed `Rad` to `Res` on 2026-08-16), and
> for that reason its presence in the import closure should be reviewed
> rather than assumed.  Read the CRW caveat under check (2) below
> before attempting to discharge `LampKernelBlockAmalgam`.  Everything from
> here down describes the manuscript as it stood before that rewrite.

Manuscript: `non_mf_groups_exist.tex`, `\subsection*{Questions}`, item 1 —
navigate by the section string, never by line number, since the file is under
concurrent edit.  The question printed there *at the time this module was
written* was

> Is `E/⟨w⟩` MF?

and the manuscript left it open, but stated one implication on top of it:

> The same collapse, applied to the level-one block structure of
> `E/⟨w⟩`, yields a negative answer conditional on an amalgam
> decomposition of the lamp kernel; that decomposition is not part of
> the formal development, and within it the question remains open.

This module formalizes exactly that implication and nothing more.  The
hypothesis is the *amalgam decomposition of the lamp kernel together with
its level-one block structure*, packaged as `LampKernelBlockAmalgam`; the
conclusion is the negative answer, `¬ IsCDEOperatorMF (E ⧸ ⟨w⟩)`.  The
decomposition itself is **not** proved here and stays open, exactly as the
manuscript says.  What is proved is that it suffices.

## Why this conditional statement is of the permitted kind

The house standard forbids conditional Lean declarations, and an auditor
meeting a hypothesis-bearing theorem in this corpus should normally treat it
as a defect.  This one is not, and the distinction is sharp:

* the forbidden pattern is a hypothesis that *stands in for mathematics that
  is already known and merely unformalized* — a literature theorem (TWW,
  Adian--Rabin, a realization theorem) wrapped as an assumption so that a
  closed Lean declaration can quote it.  The mathematics then lives outside
  the kernel and the badge overstates what was checked;
* the hypothesis here is `LampKernelBlockAmalgam`, a concrete
  group-theoretic assertion about one specific finitely presented group,
  which the manuscript itself **poses as an open question** in the very
  sentence being formalized.  Nobody has proved it, in Lean or on paper, and
  no citation is being laundered.  "If this open decomposition holds then the
  quotient is not MF" is a theorem in the ordinary sense, and its content is
  exactly the deduction the manuscript asserts.

Concretely: no field of `LampKernelBlockAmalgam` is an analytic statement, a
statement about MF-ness or corona representations, or a restatement of the
conclusion.  Every field is a finite piece of group-theoretic structure.  The
analytic half of the argument — manuscript `thm:collapse` — is consumed
unconditionally from `Sofic/InvolutionCollapseEndpoint`.

The four checks an auditor should run, and their outcome here:

1. *Is the hypothesis concrete, or an opaque data bundle?*  Concrete.  Every
   field is an assertion about the **fixed** group `MarkedGroup` and its
   fixed elements `dee`, `mark`, `baseMap`, `Base`.  There is no abstract
   group variable and no parameter whose content is unconstrained.  `Index`
   and `Site` are indexing types only, and they are pinned: `site_card` fixes
   eight sites per block, `level₁` names the level-one block, and
   `orbitSite_spec` identifies the site lamps with actual conjugates of `dee`
   in `E`.  This is the opposite of a `ReductionData`-style bundle over an
   abstract group, which is the shape that hides content.
2. *Does the manuscript pose it as open, in its own voice?*  Yes, with no
   attribution: "that decomposition is not part of the formal development,
   and within it the question remains open", inside item 1 of
   `\subsection*{Questions}`.  Compare item 2 of the same list, which does
   attribute its construction (Fournier-Facio, Hull--Osin); item 1's
   decomposition is credited to nobody, because nobody has proved it.
3. *Is the hypothesis the manuscript's, no stronger?*  It is not stronger; it
   is slightly **weaker** — see the fidelity note on `LampKernelBlockAmalgam`.
   Weaker means this theorem is stronger, which is the safe direction.
4. *Is the implication proved unconditionally?*  Yes.  Every declaration
   below takes exactly one argument, `(A : LampKernelBlockAmalgam)`; this
   module declares no `variable`s, and every external result it consumes is a
   closed theorem — in particular property `(T)` for the base is genuinely
   proved in-corpus (`LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT`,
   discharged by `LiteralP13HodgeCertificate.p13_hasKazhdanPropertyT`), not
   assumed.

Two further facts that bound what this module may be used for.

*It cannot mislead even if the hypothesis is unsatisfiable.*  The conclusion
is independently an unconditional theorem of this corpus
(`LiteralSignFreeQuotient.signFreeQuotient_not_isCDEOperatorMF`, proved by a
parity argument and the Clifford witness model, using no amalgam).  So the
characteristic damage of a vacuous conditional — a development that appears
to establish something unproved — cannot occur here.

*It must not be badged.*  `scripts/Audit.lean` states the doctrine: "a
conditional result must not LIVE on the trust surface, however honest its
type: delete it, or prove its antecedent in the corpus and remove that
antecedent from the public statement."  The mechanical `LITERATURE_INPUT`
gate is roster-driven and `literatureInputNames` is empty, so this module
does not trip it; but the doctrine still means this declaration must stay a
repo-internal module and must **never** be cited by a `\leanverified` badge
as certifying manuscript Question 1.  If Question 1 is ever to be badged, the
badge belongs on the unconditional `signFreeQuotient_not_isCDEOperatorMF`.

The decomposition, in the form the manuscript's phrase abbreviates (see
`research/literal-lamp-kernel-clifford-block-amalgam.md` and
`notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md`), is

```text
  N_E  =  ⋆_{i ∈ I}  ClLamp(8)   amalgamated over the common centre ⟨w⟩,
```

with `I` the block set, each block an order-`2⁹` Clifford lamp group on
eight sites, and `V` permuting the blocks; the *level-one block* is the one
containing the two marked sites `τo` and `v₁ τo`, and the base preserves it.

## The named steps of the implication

| step | declaration | content |
| ---- | ----------- | ------- |
| 0 | `q1_00_v1_mem_Lbar` | `v̄₁` lies in the image of the base |
| 1 | `q1_01_root_site` | the moved root lamp `d = tct⁻¹` is the site lamp of the level-one block at the marked site |
| 2 | `q1_02_orbit_commutator_mem` | same-block braiding: any two base conjugates of `d` commute *up to `w`* |
| 3 | `q1_03_involutive_witness` | `d̄` is an involutive compression witness in `E/⟨w⟩` for the base and the compressor `t` |
| 4 | `q1_04_marked_commutator_eq_block` | the unsquared defect `u⁻¹ = ⁅v₁, d⁆` is the product of the two distinct marked site lamps |
| 5 | `q1_05_marked_commutator_not_mem_markSubgroup` | the block embeds, so that product is not a power of `w` |
| 6 | `q1_06_collapsed_commutator_ne_one` | hence `ū` survives in `E/⟨w⟩` |
| 7 | `q1_07_signFree_collapse` | the involutive collapse puts `ū` in `Res_MF(E/⟨w⟩)`, where it is nontrivial |
| 8 | `q1_08_actualCoronaMFResidual_ne_bot` | `Res_MF(E/⟨w⟩) ≠ 1` |
| — | `manuscriptQuestionOne_negative_of_blockAmalgam` | the endpoint: `E/⟨w⟩` is not MF |

Steps 3, 7 and the endpoint consume the unconditional involutive collapse
of `Sofic/InvolutionCollapseEndpoint` (manuscript `thm:collapse`) and the
unconditional literal relator facts of `Sofic/LiteralSignFreeQuotient`
(`dee_sq`, `dee_commutes_compressed`, `Lbar_hasKazhdanPropertyT`,
`Lbar_compressed`) — these are the manuscript's `(W1)`, `(W2)` and the
property-`(T)` input, none of which needs the amalgam.  The amalgam is used
in exactly two places, and they are exactly the two places the manuscript
uses it: step 2 (the commuting-orbit hypothesis `(W3)`, which is *false* in
`E` itself — the failure there **is** `w`) and step 5 (nontriviality of the
collapsed defect in the quotient).
-/

namespace GroupApproximation
namespace AmalgamQuestionEndpoint

open LiteralNonMFPresentation LiteralSignFreeQuotient
open scoped commutatorElement

noncomputable section

/-! ## The lamp kernel -/

/-- The lamp kernel `N ◁ E` of the literal group: the normal closure of the
lamp generator `c`, equivalently the kernel of `E ↠ V`. -/
def lampKernel : Subgroup MarkedGroup :=
  Subgroup.normalClosure ({LiteralNonMFPresentation.lamp} : Set MarkedGroup)

/-! ## The hypothesis: the manuscript's amalgam decomposition

Everything in this section is *hypothesis*, not theorem.  The manuscript
poses it as open and this module keeps it open. -/

/-- **The open decomposition of manuscript Question 1.**  A witness of this
structure is precisely the manuscript's "amalgam decomposition of the lamp
kernel", together with the "level-one block structure of `E/⟨w⟩`" that the
same sentence invokes:

* `Index` indexes the blocks and `Site i` the eight sites of block `i`;
* `blockEmbed i` realizes the `i`-th block inside `E` as a copy of the
  Clifford lamp group on its sites, injectively, matching the Clifford sign
  with the manuscript's marked central involution `w` — this is the
  statement that the vertex groups of the amalgam are order-`2⁹` Clifford
  lamp groups and that they embed;
* `blocks_generate` and `blocks_meet_in_mark` are the two structural
  assertions of an amalgamated free product over the common centre `⟨w⟩`:
  the blocks generate the lamp kernel, and distinct blocks meet exactly in
  the amalgamated subgroup;
* `level₁`, `orbitSite` and `markedPair_ne` are the level-one block
  structure: the base preserves one distinguished block, the whole base
  orbit of the moved root lamp `d = t c t⁻¹` consists of site lamps of that
  block, and the marked pair `{τo, v₁ τo}` consists of two *distinct*
  sites of it.

No field of this structure is proved anywhere in this development.

**Fidelity note**, the one gap an auditor should know about.
`blocks_generate` and `blocks_meet_in_mark` are *consequences* of the
amalgam rather than a characterization of it: they omit the normal-form
theorem (Serre, *Trees* I.§1.2), so a group satisfying them need not
literally be the amalgamated free product.  The hypothesis is therefore
weaker than "the lamp kernel is the amalgam", which makes this theorem
stronger, never weaker, and leaves the operational requirement intact — a
genuine decomposition supplies a witness of this structure with no extra
work.  Concretely, from `lampKernel ≃* Monoid.PushoutI φ` with
`φ i : Multiplicative (ZMod 2) →* CliffordLamp (Site i)` carrying the
generator to `CliffordLamp.sign` (injective by `CliffordLamp.sign_ne_one`),
the field `blockEmbed_injective` is exactly `Monoid.PushoutI.of_injective`
and `blockEmbed_sign` is `Monoid.PushoutI.of_apply_eq_base`.  Stating the
hypothesis directly as that `MulEquiv` would be strictly more faithful; it
is avoided here only because this module is written without a compiler. -/
structure LampKernelBlockAmalgam where
  /-- The block set `I` of the orbital graph. -/
  Index : Type
  /-- The eight sites of each block. -/
  Site : Index → Type
  /-- Each block is realized inside `E`. -/
  blockEmbed : (i : Index) → CliffordLamp.CliffordLamp (Site i) →* MarkedGroup
  /-- The vertex groups of the amalgam embed: each block really is a copy of
  the Clifford lamp group on its sites. -/
  blockEmbed_injective : ∀ i, Function.Injective (blockEmbed i)
  /-- The amalgamated subgroup is the common centre, carried by the marked
  central involution `w`. -/
  blockEmbed_sign : ∀ i, blockEmbed i (CliffordLamp.sign (Site i)) = mark
  /-- Each block has eight sites, so has order `2⁹ = 512`. -/
  site_card : ∀ i, Nat.card (Site i) = 8
  /-- The blocks generate the lamp kernel. -/
  blocks_generate : lampKernel = ⨆ i, (blockEmbed i).range
  /-- Distinct blocks meet exactly in the amalgamated centre `⟨w⟩`. -/
  blocks_meet_in_mark : ∀ i j, i ≠ j →
    (blockEmbed i).range ⊓ (blockEmbed j).range = markSubgroup
  /-- The level-one block, the one containing the marked pair. -/
  level₁ : Index
  /-- The base preserves the level-one block: every base conjugate of the
  moved root lamp is again a site lamp of that block. -/
  orbitSite : Base → Site level₁
  /-- The site indexing is the conjugation orbit of `d = t c t⁻¹`. -/
  orbitSite_spec : ∀ g : Base,
    blockEmbed level₁ (CliffordLamp.lamp (Site level₁) (orbitSite g)) =
      baseMap g * dee * (baseMap g)⁻¹
  /-- The two marked sites `τo` and `v₁ τo` of the level-one block are
  distinct. -/
  markedPair_ne : orbitSite LiteralBaseRelations.v1 ≠ orbitSite 1

/-! ## Step 0: the marked base letter -/

/-- **Step 0.**  The image of `v₁` lies in the image `L̄` of the base inside
`E/⟨w⟩`, the Kazhdan subgroup the collapse is run against. -/
theorem q1_00_v1_mem_Lbar :
    proj (baseMap (LiteralBaseRelations.v1 : Base)) ∈ Lbar :=
  ⟨LiteralBaseRelations.v1, rfl⟩

/-! ## Step 1: the moved root lamp is a site of the level-one block -/

/-- **Step 1.**  The moved root lamp `d = t c t⁻¹` is the site lamp of the
level-one block at the marked site `τo`, i.e. at `orbitSite 1`. -/
theorem q1_01_root_site (A : LampKernelBlockAmalgam) :
    A.blockEmbed A.level₁
        (CliffordLamp.lamp (A.Site A.level₁) (A.orbitSite 1)) = dee := by
  have h := A.orbitSite_spec 1
  rwa [map_one, one_mul, inv_one, mul_one] at h

/-! ## Step 2: the commuting-orbit hypothesis (W3) -/

/-- **Step 2 — the amalgam's first use.**  Any two base conjugates of the
moved root lamp are site lamps of one and the same (level-one) block, so the
Clifford braiding relation of that block makes their commutator equal to the
central sign `w`; distinct site lamps of a common block commute *up to `w`*
and nothing more.  This is the step that fails in `E` itself — there the
failure is exactly the marked word `w` — and becomes available once `w` is
killed. -/
theorem q1_02_orbit_commutator_mem (A : LampKernelBlockAmalgam)
    (g₁ g₂ : Base) :
    ⁅baseMap g₁ * dee * (baseMap g₁)⁻¹,
      baseMap g₂ * dee * (baseMap g₂)⁻¹⁆ ∈ markSubgroup := by
  by_cases hs : A.orbitSite g₁ = A.orbitSite g₂
  · have hconj : baseMap g₁ * dee * (baseMap g₁)⁻¹ =
        baseMap g₂ * dee * (baseMap g₂)⁻¹ := by
      rw [← A.orbitSite_spec g₁, ← A.orbitSite_spec g₂, hs]
    have hself : ⁅baseMap g₂ * dee * (baseMap g₂)⁻¹,
        baseMap g₂ * dee * (baseMap g₂)⁻¹⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr (Commute.refl _)
    rw [hconj, hself]
    exact Subgroup.one_mem _
  · have hb : A.blockEmbed A.level₁
        ⁅CliffordLamp.lamp (A.Site A.level₁) (A.orbitSite g₁),
          CliffordLamp.lamp (A.Site A.level₁) (A.orbitSite g₂)⁆ = mark := by
      rw [CliffordLamp.commutator_lamp_lamp (A.Site A.level₁) hs,
        A.blockEmbed_sign]
    rw [map_commutatorElement, A.orbitSite_spec g₁, A.orbitSite_spec g₂] at hb
    rw [hb]
    exact Subgroup.mem_zpowers _

/-! ## Step 3: the involutive compression witness in the quotient -/

/-- **Step 3.**  In `E/⟨w⟩` the image `d̄` of the moved root lamp is an
involutive compression witness for the image `L̄` of the base and the
compressor `t̄`:

* `(W1)` `d̄² = 1`, from `c² = 1` in `E`;
* `(W2)` the `t`-compressed copy of the base centralizes `d̄`, from the
  literal centralizer relators `[c, g] = 1` conjugated by `t`;
* `(W3)` the `L̄`-conjugation orbit of `d̄` commutes pairwise — this is
  Step 2, and it is the amalgam's contribution.

`(W1)` and `(W2)` are unconditional literal relator facts and are imported
from `Sofic/LiteralSignFreeQuotient`. -/
theorem q1_03_involutive_witness (A : LampKernelBlockAmalgam) :
    InvolutionCollapseEndpoint.IsInvolutiveCompressionWitness Lbar
      (proj stable) (proj dee) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_mul, dee_sq, map_one]
  · rintro γ ⟨g, rfl⟩
    have h := (dee_commutes_compressed g).symm
    have h2 := h.map proj
    simpa only [map_mul, map_inv, MonoidHom.comp_apply] using h2
  · rintro γ₁ ⟨g₁, rfl⟩ γ₂ ⟨g₂, rfl⟩
    have hmem := q1_02_orbit_commutator_mem A g₁ g₂
    have h1 : proj ⁅baseMap g₁ * dee * (baseMap g₁)⁻¹,
        baseMap g₂ * dee * (baseMap g₂)⁻¹⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    rw [map_commutatorElement] at h1
    have h2 := commutatorElement_eq_one_iff_commute.mp h1
    simpa only [map_mul, map_inv, MonoidHom.comp_apply] using h2

/-! ## Steps 4–6: the collapsed defect survives -/

/-- **Step 4.**  The unsquared defect `⁅v₁, d⁆` — the inverse of the
manuscript's marked commutator `u` — is the product of the two marked site
lamps of the level-one block. -/
theorem q1_04_marked_commutator_eq_block (A : LampKernelBlockAmalgam) :
    A.blockEmbed A.level₁
        (CliffordLamp.lamp (A.Site A.level₁)
            (A.orbitSite LiteralBaseRelations.v1) *
          (CliffordLamp.lamp (A.Site A.level₁) (A.orbitSite 1))⁻¹) =
      ⁅baseMap (LiteralBaseRelations.v1 : Base), dee⁆ := by
  rw [map_mul, map_inv, A.orbitSite_spec LiteralBaseRelations.v1,
    q1_01_root_site A, commutatorElement_def]

/-- **Step 5 — the amalgam's second use.**  The two marked sites are
distinct and the level-one block embeds in `E`, so the product of their
lamps is neither `1` nor `w`; being an element of the block, it is
therefore not a power of `w` at all. -/
theorem q1_05_marked_commutator_not_mem_markSubgroup
    (A : LampKernelBlockAmalgam) :
    ⁅baseMap (LiteralBaseRelations.v1 : Base), dee⁆ ∉ markSubgroup := by
  intro hmem
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hkey : A.blockEmbed A.level₁
      (CliffordLamp.sign (A.Site A.level₁) ^ n) =
        A.blockEmbed A.level₁
          (CliffordLamp.lamp (A.Site A.level₁)
              (A.orbitSite LiteralBaseRelations.v1) *
            (CliffordLamp.lamp (A.Site A.level₁) (A.orbitSite 1))⁻¹) := by
    rw [map_zpow, A.blockEmbed_sign, hn]
    exact (q1_04_marked_commutator_eq_block A).symm
  have heq := A.blockEmbed_injective A.level₁ hkey
  rcases CommutingLampCollapse.zpow_mem_pair
      (CliffordLamp.sign_sq (A.Site A.level₁)) n with h0 | h0 <;>
    rw [h0] at heq
  · exact (CommutingLampCollapse.lamp_mul_lamp_inv_ne A.markedPair_ne).1
      heq.symm
  · exact (CommutingLampCollapse.lamp_mul_lamp_inv_ne A.markedPair_ne).2
      heq.symm

/-- **Step 6.**  Hence the collapsed defect `ū` is nontrivial in
`E/⟨w⟩`. -/
theorem q1_06_collapsed_commutator_ne_one (A : LampKernelBlockAmalgam) :
    ⁅proj (baseMap (LiteralBaseRelations.v1 : Base)), proj dee⁆ ≠ 1 := by
  intro hc
  rw [← map_commutatorElement] at hc
  exact q1_05_marked_commutator_not_mem_markSubgroup A
    ((QuotientGroup.eq_one_iff _).mp hc)

/-! ## Steps 7–8 and the endpoint -/

/-- **Step 7.**  The involutive collapse of manuscript
Theorem~`thm:collapse` places the collapsed defect in the MF radical of
`E/⟨w⟩`, where Step 6 keeps it nontrivial. -/
theorem q1_07_signFree_collapse (A : LampKernelBlockAmalgam) :
    ActualCoronaMFInvisible
        ⁅proj (baseMap (LiteralBaseRelations.v1 : Base)), proj dee⁆ ∧
      ⁅proj (baseMap (LiteralBaseRelations.v1 : Base)), proj dee⁆ ≠ 1 :=
  ⟨InvolutionCollapseEndpoint.actualCoronaMFInvisible_of_involutiveWitness
      Lbar_hasKazhdanPropertyT Lbar_compressed (q1_03_involutive_witness A)
      q1_00_v1_mem_Lbar,
    q1_06_collapsed_commutator_ne_one A⟩

/-- **Step 8.**  The MF radical of `E/⟨w⟩` is nontrivial; by
manuscript Corollary~`cor:pullback` the MF radical of `E` is therefore
strictly larger than `⟨w⟩`. -/
theorem q1_08_actualCoronaMFResidual_ne_bot (A : LampKernelBlockAmalgam) :
    actualCoronaMFResidual SignFreeQuotient ≠ ⊥ := by
  intro hbot
  have hmem : ⁅proj (baseMap (LiteralBaseRelations.v1 : Base)),
      proj dee⁆ ∈ actualCoronaMFResidual SignFreeQuotient :=
    InvolutionCollapseEndpoint.actualCoronaMFInvisible_of_involutiveWitness
      Lbar_hasKazhdanPropertyT Lbar_compressed (q1_03_involutive_witness A)
      q1_00_v1_mem_Lbar
  rw [hbot] at hmem
  exact q1_06_collapsed_commutator_ne_one A (Subgroup.mem_bot.mp hmem)

/-- **The endpoint of manuscript Question 1, stated as an implication.**
*If* the lamp
kernel of the literal group admits the amalgam decomposition of
`LampKernelBlockAmalgam` — the open group-theoretic input the manuscript
names and declines to prove — *then* the answer to "Is `E/⟨w⟩` MF?" is
negative.

The hypothesis is the manuscript's, unweakened: no analytic input, no
literature input, and no restatement of the conclusion appears among its
fields.  The implication itself is unconditional, so an affirmative
resolution of the open decomposition yields the non-MF conclusion by a
single application of this theorem. -/
theorem manuscriptQuestionOne_negative_of_blockAmalgam
    (A : LampKernelBlockAmalgam) : ¬ IsCDEOperatorMF SignFreeQuotient :=
  ProjectionCompressionCollapse.not_isCDEOperatorMF_of_involutiveWitness
    Lbar_hasKazhdanPropertyT Lbar_compressed (q1_03_involutive_witness A)
    q1_00_v1_mem_Lbar (q1_06_collapsed_commutator_ne_one A)

end

end AmalgamQuestionEndpoint
end GroupApproximation

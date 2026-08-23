import GroupApproximation.Sofic.AvatarWordFamily
import GroupApproximation.Sofic.GreendlingerSharpResidualWiring

/-!
# The avatar family, instantiated against the metric check

`Sofic.AvatarMetricCheck` proves `C'(1/8)`, the absence of block powers and the
protected ball from a bundle of checkable facts; `Sofic.AvatarWordFamily` builds
the explicit family and derives every structural field of the router's design
from it.  Neither can import the other's conclusion — the family imports the
check — so the two meet here, in the only module that can see both.

## The three numbers

The instantiation turns on three quantities, and stating them separately is what
makes the margin provable rather than assumed.

* `avatarLen` — a common lower bound on avatar lengths.  Under a **length-balanced**
  code, where each avatar carries `L` blocks whose globally distinct exponents sum
  to a constant, every avatar has exactly this length and the bound is tight.
* `runCeil` — the ceiling on `y₂`-runs.  Since the family is positive no junction
  cancels, so every run is a code run.
* `sharedBound` — the caller's **small-cancellation datum**: the longest common
  cyclic subword of two distinct source relators, measured in generators.

The common floor is imposed directly on the expanded router relators.  This is
the invariant the metric proof consumes.  In particular a singleton abstract
tie is intentionally allowed to expand to one long defect or partner avatar;
no unrelated lower bound is imposed on its pre-substitution length.

From these, `pieceCeil = sharedBound·avatarLen + 2·runCeil + 2`.  That shape is
forced: a piece covers `sharedBound` complete shared avatars plus a partial
avatar at each end, and each flank is at most `runCeil + 1` because two different
avatars agree only on `y₁·y₂^{min(e,e')}` before their exponents diverge.

## Why the margin needs balancing

`metric_margin` is proved here from two inputs, `8·(2·runCeil + 2) ≤ avatarLen`
and `8·sharedBound + 1 ≤ wordFloor`, giving

    8·pieceCeil = 8·c·S + 8·(2A+2) ≤ 8·c·S + S = (8c+1)·S ≤ wordFloor·S.

The second input is a floor *constant in the alphabet size*.  It is constant only
because `avatarLen` is a genuine common length.  With the arithmetic-progression
code the avatar lengths spread by `R ≈ 4·V + 1`, `avatarLen` collapses to the
shortest avatar, and the requirement grows like `8·c·R ≈ 32·c·V`; padding each
relator with its own fresh generators then grows `V` like `m·n`, so `n ≳ 32·m·n`
has no solution and the design diverges.  A shared padding pool whose relators
pairwise share no two-letter subword escapes that at `n ≳ 4096·m` — recorded as
the alternative, not the design.

## What is not discharged

`piece_short` and `uniqueMark` are fields about the constructed router words.
`piece_short` is the
small-cancellation condition itself and is a fact about the caller's chosen
presentation; no lemma here can supply it, and the earlier attempt to derive it
from a pinning property was **false** — see `AvatarMetricCheck.piece_short`.
-/

namespace GroupApproximation
namespace AvatarRouterInstance

open SmallCancellationRouter
open BespokeRouter.AvatarWordFamily

variable {E : Type} [Group E] {N : Subgroup E} {s : E} {B : Type} [Group B]

/-! ## 1.  The instantiation inputs -/

/-- **What the caller owes** on top of a `Blueprint`: the three numbers, the
length floors, and the two combinatorial conditions the exponent code does not
by itself supply. -/
structure Inputs (D : BespokeRouter.AvatarWordFamily.Blueprint E N s B) where
  /-- A common lower bound on the length of every avatar; exact under a
  length-balanced code. -/
  avatarLen : ℕ
  /-- The ceiling on `y₂`-runs of the family. -/
  runCeil : ℕ
  /-- The caller's small-cancellation datum: the longest common cyclic subword of
  two distinct source relators, in generators. -/
  sharedBound : ℕ
  /-- The number of avatars used to state the common expanded-relator floor. -/
  wordFloor : ℕ
  /-- Source avatars meet the common length. -/
  src_avatar_long : ∀ i, avatarLen ≤ (D.srcAvatarWord i).length
  /-- Partner avatars meet the common length. -/
  par_avatar_long : ∀ k, avatarLen ≤ (D.parAvatarWord k).length
  /-- Every expanded source relator meets the common router-relator floor. -/
  src_floor : ∀ r ∈ D.srcPres.rel,
    wordFloor * avatarLen ≤ (avatarSubst D.srcAvatarWord r).length
  /-- Every expanded partner relator meets the common router-relator floor. -/
  par_floor : ∀ r ∈ D.parPres.rel,
    wordFloor * avatarLen ≤ (avatarSubst D.parAvatarWord r).length
  /-- Every *expanded* defect tie meets the common router-relator floor.

  This is deliberately stated after avatar substitution.  A singleton
  abstract tie is the useful multiplicity-free choice: its expansion contains
  one full defect avatar and can be arbitrarily long even though the abstract
  word has length one.  Requiring the pre-substitution word itself to meet
  `wordFloor` made that valid construction arithmetically impossible and was
  stronger than anything the metric argument consumes. -/
  defectTie_floor : ∀ i,
    wordFloor * avatarLen ≤ (D.defectTieWord i).length
  /-- Every expanded partner tie meets the same router-relator floor. -/
  partnerTie_floor : ∀ i,
    wordFloor * avatarLen ≤ (D.partnerTieWord i).length
  /-- The designated defect words are nonempty, so the defect avatars are at
  least one avatar long. -/
  basis_ne_nil : ∀ k, 1 ≤ (D.basisWord k).length
  /-- **The piece ceiling.**  A piece covers at most `sharedBound` complete shared
  avatars plus one partial avatar at each end.  This is the small-cancellation
  condition on the caller's presentation; it is not derivable from `Blueprint`,
  and the pinning derivation that once stood here is false. -/
  piece_short : ∀ p : List (Fin 2 × Bool),
    IsPiece (symmetrization D.relators) p →
      p.length < sharedBound * avatarLen + 2 * runCeil + 2
  /-- Occurrence-specific marks on the constructed router relators. -/
  occurrenceMarks : D.OccurrenceMarks
  /-- The flank term fits inside one avatar — eight times over.  This is where
  balancing is spent: it is a statement about the *common* avatar length. -/
  flank_small : 8 * (2 * runCeil + 2) ≤ avatarLen
  /-- The relators are long enough in avatars.  Constant in the alphabet size,
  because `avatarLen` is a genuine common length. -/
  floor_ge : 8 * sharedBound + 1 ≤ wordFloor
  /-- A ceiling on the protected element's reduced length. -/
  protectedLength : ℕ
  /-- It is a ceiling. -/
  protected_norm :
    FreeGroup.norm (FreeGroup.lift D.srcAvatar D.protectedWord) ≤ protectedLength
  /-- The protected ball margin. -/
  protected_margin : 2 * protectedLength ≤ wordFloor * avatarLen

namespace Inputs

variable {D : BespokeRouter.AvatarWordFamily.Blueprint E N s B} (I : Inputs D)

/-! ## 2.  The avatars have one length

Under the length-balanced code every avatar is exactly `D.avatarLength` letters
long — `L / 2` pairs whose exponents sum to `V·L + 1` apiece, independent of `ν`.
So the two avatar fields of `Inputs` are discharged by an *equality* rather than
estimated, and that is the whole reason the floor below is constant in the
alphabet size.

The superseded route is worth recording: before balancing, the only bound
available was the one the old stride code gave at `ν = 0`, namely `2·L`.  That is
the shortest avatar rather than a common one, and taking it as `avatarLen` is what
made the requirement grow like `8·c·R ≈ 32·c·V` and the design diverge. -/

/-- Source avatars have the common length. -/
theorem avatarLength_le_srcAvatarWord (i : Fin D.srcPres.card) :
    D.avatarLength ≤ (D.srcAvatarWord i).length :=
  le_of_eq (D.length_srcAvatarWord i).symm

/-- Partner avatars have the common length. -/
theorem avatarLength_le_parAvatarWord (k : Fin D.parPres.card) :
    D.avatarLength ≤ (D.parAvatarWord k).length :=
  le_of_eq (D.length_parAvatarWord k).symm

/-! ## 3.  The relator floor, one branch at a time -/

/-- Every defect avatar meets the common length, because the designated defect
words are nonempty. -/
theorem avatarLen_le_defectAvatarWord (k : Fin 2) :
    I.avatarLen ≤ (D.defectAvatarWord k).length := by
  have h1 := le_length_avatarSubst D.srcAvatarWord I.avatarLen
    I.src_avatar_long (D.basisWord k)
  have h2 : 1 * I.avatarLen ≤ (D.basisWord k).length * I.avatarLen :=
    Nat.mul_le_mul (I.basis_ne_nil k) (Nat.le_refl _)
  rw [Nat.one_mul] at h2
  exact le_trans h2 h1

/-- The floor, as a number: `wordFloor` avatars, each at least `avatarLen`. -/
def relatorFloor : ℕ := I.wordFloor * I.avatarLen

theorem floor_le_src {r : List (Fin D.srcPres.card × Bool)}
    (hr : r ∈ D.srcPres.rel) :
    I.relatorFloor ≤ (avatarSubst D.srcAvatarWord r).length := by
  exact I.src_floor r hr

theorem floor_le_par {r : List (Fin D.parPres.card × Bool)}
    (hr : r ∈ D.parPres.rel) :
    I.relatorFloor ≤ (avatarSubst D.parAvatarWord r).length := by
  exact I.par_floor r hr

theorem floor_le_defectTie (i : Fin 2) :
    I.relatorFloor ≤ (D.defectTieWord i).length := by
  exact I.defectTie_floor i

theorem floor_le_partnerTie (i : Fin 2) :
    I.relatorFloor ≤ (D.partnerTieWord i).length := by
  exact I.partnerTie_floor i

/-- **Every relator meets the floor.** -/
theorem relators_long : ∀ r ∈ D.relators, I.relatorFloor ≤ r.length := by
  intro r hr
  simp only [BespokeRouter.AvatarWordFamily.Blueprint.relators,
    BespokeRouter.AvatarWordFamily.Blueprint.srcRelators,
    BespokeRouter.AvatarWordFamily.Blueprint.parRelators,
    Set.mem_union, Set.mem_image, Set.mem_range] at hr
  rcases hr with (⟨ρ, hρ, rfl⟩ | ⟨ρ, hρ, rfl⟩) | (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact I.floor_le_src hρ
  · exact I.floor_le_par hρ
  · exact I.floor_le_defectTie i
  · exact I.floor_le_partnerTie i

/-! ## 4.  The two margins -/

/-- The piece ceiling, as a number. -/
def pieceCeil : ℕ := I.sharedBound * I.avatarLen + 2 * I.runCeil + 2

theorem two_le_pieceCeil : 2 ≤ I.pieceCeil := by
  simp only [pieceCeil]
  obtain ⟨P, hP⟩ : ∃ P, I.sharedBound * I.avatarLen = P := ⟨_, rfl⟩
  rw [hP]
  clear hP
  omega

/-- **The metric margin.**  Eight flank terms fit inside one avatar, and the
relator carries `8·sharedBound + 1` avatars, so eight piece ceilings fit inside
one relator floor.  The whole computation is linear once the two products are
named. -/
theorem metric_margin : 8 * I.pieceCeil ≤ I.relatorFloor := by
  have hflank := I.flank_small
  have hfloor := I.floor_ge
  have hgrow : (8 * I.sharedBound + 1) * I.avatarLen ≤ I.wordFloor * I.avatarLen :=
    Nat.mul_le_mul hfloor (Nat.le_refl _)
  have hexp : (8 * I.sharedBound + 1) * I.avatarLen
      = 8 * (I.sharedBound * I.avatarLen) + I.avatarLen := by ring
  rw [hexp] at hgrow
  obtain ⟨P, hP⟩ : ∃ P, I.sharedBound * I.avatarLen = P := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, I.wordFloor * I.avatarLen = T := ⟨_, rfl⟩
  rw [hP, hT] at hgrow
  simp only [pieceCeil, relatorFloor]
  rw [hP, hT]
  clear hP hT hexp
  omega

theorem protected_margin' : 2 * I.protectedLength ≤ I.relatorFloor :=
  I.protected_margin

/-! ## 5.  The bundle, and the endpoint -/

/-- **The check bundle at the explicit family.**  Its relator set is the
family's on the nose, so the bridge hypothesis downstream is `rfl`. -/
def metricData : AvatarMetricCheck.AvatarMetricData where
  relators := D.relators
  pieceCeil := I.pieceCeil
  two_le_pieceCeil := I.two_le_pieceCeil
  relatorFloor := I.relatorFloor
  protectedLength := I.protectedLength
  relators_long := I.relators_long
  piece_short := I.piece_short
  uniqueMark := I.occurrenceMarks.unique
  metric_margin := I.metric_margin
  protected_margin := I.protected_margin'

@[simp] theorem metricData_relators : (I.metricData).relators = D.relators := rfl

/-- **The family's four obligations**, from the bundle.  Only nontriviality of
the protected avatar is left, and it is not a metric-side fact. -/
include I in
theorem obligations
    (hne : FreeGroup.lift D.srcAvatar D.protectedWord ≠ 1) : D.Obligations :=
  D.obligations_of_metricData I.metricData rfl hne I.protected_norm

/-- **The router design**, fully assembled. -/
include I in
noncomputable def design
    (hne : FreeGroup.lift D.srcAvatar D.protectedWord ≠ 1) :
    BespokeRouter.RouterRelatorDesign E N s B :=
  D.design (I.obligations hne)

/-- **The router's word-combinatorial conclusions**, from the two residuals. -/
theorem routerConclusions
    (hne : FreeGroup.lift D.srcAvatar D.protectedWord ≠ 1)
    (h : SmallCancellationRouter.SharpResiduals (Fin 2)) :
    (I.design hne).RouterConclusions :=
  AvatarMetricCheck.routerConclusions_of_check_of_residuals
    (I.design hne) I.metricData rfl h

/-- **The endpoint.** -/
include I in
theorem nonempty_routingLemmaData [N.Normal]
    (hne : FreeGroup.lift D.srcAvatar D.protectedWord ≠ 1)
    (h : SmallCancellationRouter.SharpResiduals (Fin 2)) :
    Nonempty (SmallCancellationRouter.RoutingLemmaData E N s B) :=
  AvatarMetricCheck.nonempty_routingLemmaData_of_check_of_residuals
    (I.design hne) I.metricData rfl h

end Inputs

end AvatarRouterInstance
end GroupApproximation

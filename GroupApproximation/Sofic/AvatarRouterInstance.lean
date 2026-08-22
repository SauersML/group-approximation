import GroupApproximation.Sofic.AvatarWordFamily
import GroupApproximation.Sofic.GreendlingerSharpResidualWiring

/-!
# The avatar family, instantiated against the metric check

`Sofic.AvatarMetricCheck` proves `C'(1/8)`, the absence of block powers and the
protected ball from a bundle of checkable facts; `Sofic.AvatarWordFamily` builds
the explicit family and derives every structural field of the router's design
from it.  Neither can import the other's conclusion — the family imports the
check — so the two meet here, in the only module that can see both.

## What this module does

It builds an `AvatarMetricCheck.AvatarMetricData` whose relator set *is* the
family's, so that `hrel` is `rfl`, and threads it to the endpoint.  Four of the
six fields are discharged; three combinatorial conditions remain, carried as
fields of `Inputs` in the library's data-not-axiom style.  The split is not
arbitrary — see below.

## The two constants, and why the floor must grow with the alphabet

`maxExponent` is the ceiling on `y₂`-runs.  Because the family is *positive*,
no junction cancels: every run of a relator is a code run `K·ν + j + 1` with
`ν < V` and `j < L`, so `K·V + L` bounds them, and the `+1` here covers the
single generator letter that opens a tying relator, which the wrap of a rotation
can abut against a trailing run.

`relatorFloor` is `wordFloor · (2·L)`, where `2·L` is the shortest avatar length
that `le_length_avatarWord` delivers — at `ν = 0` that lemma gives `L·(K·0 + 2)`,
dropping the triangular term `L·(L−1)/2` that the avatar actually carries.  The
consequence is that `wordFloor` must be taken proportional to `V`, not constant:
`metric_margin` needs

    24·(K·V + L + 1) + 24  ≤  wordFloor · 2·L,

and with `L = 16·(V+1)`, `K = 2·L` this is `wordFloor ≥ 24·V + 14`.  A sharper
lower bound on `avatarWord` — one that keeps the triangular term — would bring
this back to a constant, and is the obvious optimisation if the padding ever
becomes expensive.  It is not needed: padding is free, and `Inputs.wordFloor_ge`
records the requirement rather than hiding it.

## What is *not* discharged, and why it cannot be

`pinned` and `uniqueMark` are **underdetermined by `Blueprint`.**  Both hold only
for a family whose relators are padded *per relator*, over a fresh generator pair
no other relator uses; `AvatarWordFamily`'s `SourceData` records that as a prose
convention on the caller and has no field asserting it, and the `WordPresentation.pad`
toolkit in that file is a common tail, which is exactly the shape that makes
`C'(1/8)` false.  So there is nothing in the blueprint's data from which either
could be derived, and stating them as fields here is not a deferral but the
honest location: they are conditions on *which words the caller chose*, and the
caller is the only one who knows.  The remedy, if they are to be discharged
rather than checked, is a field on `SourceData`/`PartnerData` asserting the
disjointness; that is a change to the family module.

`runs_short` is different: it *is* derivable from the block structure, by an
induction showing that a separator-free window of a concatenation of blocks
`y₁·y₂^e` is bounded by `max e`.  It is carried as a field here only because that
induction is not yet written; `AvatarMetricCheck.runs_short_of_doubled` already
reduces it from the symmetrization to two explicit words per relator, which is
the form the field takes.
-/

namespace GroupApproximation
namespace AvatarRouterInstance

open SmallCancellationRouter
open BespokeRouter.AvatarWordFamily

variable {E : Type} [Group E] {N : Subgroup E} {s : E} {B : Type} [Group B]

/-! ## 1.  The instantiation inputs -/

/-- **The run ceiling.**  Because the family is positive no junction cancels, so
every run of a relator is a code run `K·ν + j + 1` with `ν < V` and `j < L`; the
trailing `+ 1` covers the single generator letter that opens a tying relator,
which a rotation can bring against a trailing run. -/
def maxExponent (D : BespokeRouter.AvatarWordFamily.Blueprint E N s B) : ℕ :=
  D.codeK * D.avatarCount + D.codeL + 1

/-- **What the caller owes**, on top of a `Blueprint`: one length floor on the
source words, one ceiling on the protected word, and the three combinatorial
conditions the exponent code does not by itself supply. -/
structure Inputs (D : BespokeRouter.AvatarWordFamily.Blueprint E N s B) where
  /-- A common lower bound on the *source-alphabet* lengths of every relator and
  every tying word.  This is §1's padding floor, read before the rewrite. -/
  wordFloor : ℕ
  /-- The floor is large enough for the metric margin.  It grows with the
  alphabet because `le_length_avatarWord` is weak at `ν = 0`; see the module
  docstring. -/
  wordFloor_ge : 24 * D.avatarCount + 14 ≤ wordFloor
  /-- Every source relator meets the floor. -/
  src_long : ∀ r ∈ D.srcPres.rel, wordFloor ≤ r.length
  /-- Every partner relator meets the floor. -/
  par_long : ∀ r ∈ D.parPres.rel, wordFloor ≤ r.length
  /-- Every defect tying word meets the floor. -/
  defectTie_long : ∀ i, wordFloor ≤ (D.src.tieDefectWord i).length
  /-- Every partner tying word meets the floor. -/
  partnerTie_long : ∀ i, wordFloor ≤ (D.par.tiePartnerWord i).length
  /-- The two designated defect words are nonempty, so that the defect avatars
  are at least one avatar long. -/
  basis_ne_nil : ∀ k, 1 ≤ (D.basisWord k).length
  /-- A ceiling on the protected element's reduced length. -/
  protectedLength : ℕ
  /-- It is a ceiling. -/
  protected_norm :
    FreeGroup.norm (FreeGroup.lift D.srcAvatar D.protectedWord) ≤ protectedLength
  /-- The protected ball margin. -/
  protected_margin : 2 * protectedLength ≤ wordFloor * (2 * D.codeL)
  /-- **The run ceiling**, in the doubled form `runs_short_of_doubled` consumes:
  two explicit words per relator, no quantifier over rotations.  Derivable from
  the block structure; see the module docstring. -/
  runs_short : ∀ r ∈ D.relators, ∀ u : List (Fin 2 × Bool),
    (u <:+: (r ++ r) ∨
      u <:+: (FreeGroup.invRev r ++ FreeGroup.invRev r)) →
    (∀ c ∈ u, AvatarMetricCheck.isGenOne c = false) →
    u.length ≤ maxExponent D
  /-- **Piece pinning**, the honest small-cancellation condition: no two distinct
  symmetrized relators agree across two consecutive blocks.  Holds exactly when
  the padding is per relator; not derivable from `Blueprint`. -/
  pinned : ∀ p : List (Fin 2 × Bool), 3 ≤ p.countP AvatarMetricCheck.isGenOne →
    ∀ w₁ ∈ symmetrization D.relators, ∀ w₂ ∈ symmetrization D.relators,
      p <+: w₁ → p <+: w₂ → w₁ = w₂
  /-- **The unique cyclic mark**: each relator carries an exponent read at exactly
  one of its cyclic positions.  Needs an avatar occurring exactly once in that
  relator, which the per-relator padding generator supplies. -/
  uniqueMark : ∀ r ∈ D.relators, ∃ e p : ℕ, p < r.length ∧
    AvatarMetricCheck.leadCode (r.rotate p) = some e ∧
    ∀ q, q < r.length → AvatarMetricCheck.leadCode (r.rotate q) = some e → q = p

namespace Inputs

variable {D : BespokeRouter.AvatarWordFamily.Blueprint E N s B} (I : Inputs D)

/-! ## 2.  The avatar length floor

`le_length_avatarWord` at `ν = 0` gives `L·2`; every avatar is at least that
long, and every relator is a concatenation of at least `wordFloor` of them. -/

/-- The shortest avatar the code assigns is at least `2·L` letters. -/
theorem two_mul_codeL_le_avatarWord (ν : ℕ) :
    2 * D.codeL ≤ (avatarWord D.codeL D.codeK ν).length := by
  have h1 := le_length_avatarWord D.codeL D.codeK ν
  have h2 : D.codeL * 2 ≤ D.codeL * (D.codeK * ν + 2) :=
    Nat.mul_le_mul (Nat.le_refl _) (by omega)
  have h3 : 2 * D.codeL = D.codeL * 2 := Nat.mul_comm 2 D.codeL
  rw [h3]
  exact le_trans h2 h1

/-- Every source avatar is at least `2·L` letters. -/
theorem two_mul_codeL_le_srcAvatarWord (i : Fin D.srcPres.card) :
    2 * D.codeL ≤ (D.srcAvatarWord i).length :=
  two_mul_codeL_le_avatarWord (D := D) (i : ℕ)

/-- Every partner avatar is at least `2·L` letters. -/
theorem two_mul_codeL_le_parAvatarWord (k : Fin D.parPres.card) :
    2 * D.codeL ≤ (D.parAvatarWord k).length :=
  two_mul_codeL_le_avatarWord (D := D) (D.srcPres.card + (k : ℕ))

/-- Every defect avatar is at least `2·L` letters, because the designated defect
words are nonempty. -/
theorem two_mul_codeL_le_defectAvatarWord (k : Fin 2) :
    2 * D.codeL ≤ (D.defectAvatarWord k).length := by
  have h1 := le_length_avatarSubst D.srcAvatarWord (2 * D.codeL)
    (fun i => two_mul_codeL_le_srcAvatarWord i) (D.basisWord k)
  have h2 : 1 * (2 * D.codeL) ≤ (D.basisWord k).length * (2 * D.codeL) :=
    Nat.mul_le_mul (I.basis_ne_nil k) (Nat.le_refl _)
  rw [Nat.one_mul] at h2
  exact le_trans h2 h1

/-! ## 3.  The relator floor, one branch at a time -/

/-- The floor, as a number: `wordFloor` avatars, each at least `2·L` long. -/
def relatorFloor : ℕ := I.wordFloor * (2 * D.codeL)

/-- A rewritten source relator meets the floor. -/
theorem floor_le_src {r : List (Fin D.srcPres.card × Bool)}
    (hr : r ∈ D.srcPres.rel) :
    I.relatorFloor ≤ (avatarSubst D.srcAvatarWord r).length := by
  have h1 := le_length_avatarSubst D.srcAvatarWord (2 * D.codeL)
    (fun i => two_mul_codeL_le_srcAvatarWord i) r
  have h2 : I.wordFloor * (2 * D.codeL) ≤ r.length * (2 * D.codeL) :=
    Nat.mul_le_mul (I.src_long r hr) (Nat.le_refl _)
  exact le_trans h2 h1

/-- A rewritten partner relator meets the floor. -/
theorem floor_le_par {r : List (Fin D.parPres.card × Bool)}
    (hr : r ∈ D.parPres.rel) :
    I.relatorFloor ≤ (avatarSubst D.parAvatarWord r).length := by
  have h1 := le_length_avatarSubst D.parAvatarWord (2 * D.codeL)
    (fun k => two_mul_codeL_le_parAvatarWord k) r
  have h2 : I.wordFloor * (2 * D.codeL) ≤ r.length * (2 * D.codeL) :=
    Nat.mul_le_mul (I.par_long r hr) (Nat.le_refl _)
  exact le_trans h2 h1

/-- A defect tying relator meets the floor. -/
theorem floor_le_defectTie (i : Fin 2) :
    I.relatorFloor ≤ (D.defectTieWord i).length := by
  have h1 := le_length_avatarSubst D.defectAvatarWord (2 * D.codeL)
    (fun k => I.two_mul_codeL_le_defectAvatarWord k) (D.src.tieDefectWord i)
  have h2 : I.wordFloor * (2 * D.codeL)
      ≤ (D.src.tieDefectWord i).length * (2 * D.codeL) :=
    Nat.mul_le_mul (I.defectTie_long i) (Nat.le_refl _)
  have h3 : (D.defectTieWord i).length
      = 1 + (avatarSubst D.defectAvatarWord (D.src.tieDefectWord i)).length := by
    simp [BespokeRouter.AvatarWordFamily.Blueprint.defectTieWord]
  rw [h3]
  have h4 := le_trans h2 h1
  omega

/-- A partner tying relator meets the floor. -/
theorem floor_le_partnerTie (i : Fin 2) :
    I.relatorFloor ≤ (D.partnerTieWord i).length := by
  have h1 := le_length_avatarSubst D.parAvatarWord (2 * D.codeL)
    (fun k => two_mul_codeL_le_parAvatarWord k) (D.par.tiePartnerWord i)
  have h2 : I.wordFloor * (2 * D.codeL)
      ≤ (D.par.tiePartnerWord i).length * (2 * D.codeL) :=
    Nat.mul_le_mul (I.partnerTie_long i) (Nat.le_refl _)
  have h3 : (D.partnerTieWord i).length
      = 1 + (avatarSubst D.parAvatarWord (D.par.tiePartnerWord i)).length := by
    simp [BespokeRouter.AvatarWordFamily.Blueprint.partnerTieWord]
  rw [h3]
  have h4 := le_trans h2 h1
  omega

/-- **Every relator meets the floor.**  The four branches of the family, each by
its own length bound. -/
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

/-- **The metric margin holds at the design's constants.**  `L = 16·(V+1)` and
`K = 2·L` turn the requirement into `wordFloor ≥ 24·V + 14`, which is
`wordFloor_ge`.  The proof is inequality algebra: both sides are expanded in
`V` and compared, with the products of variables named first so that the
comparison is linear. -/
theorem metric_margin : 8 * (3 * maxExponent D + 3) ≤ I.relatorFloor := by
  have hL : D.codeL = 16 * (D.avatarCount + 1) := rfl
  have hK : D.codeK = 2 * D.codeL := rfl
  obtain ⟨V, hV⟩ : ∃ V, D.avatarCount = V := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, I.wordFloor = F := ⟨_, rfl⟩
  have hFge : 24 * V + 14 ≤ F := by
    have h := I.wordFloor_ge
    rw [hV, hF] at h
    exact h
  have hLV : D.codeL = 16 * (V + 1) := by rw [hL, hV]
  have hKV : D.codeK = 32 * (V + 1) := by rw [hK, hLV]; ring
  show 8 * (3 * (D.codeK * D.avatarCount + D.codeL + 1) + 3)
    ≤ I.wordFloor * (2 * D.codeL)
  rw [hV, hF, hLV, hKV]
  -- `768·V² + 1152·V + 432 ≤ (F)·32·(V+1)`, and `F ≥ 24·V + 14` gives
  -- `768·V² + 1216·V + 448` on the right.
  have hbase : (24 * V + 14) * (2 * (16 * (V + 1)))
      = 768 * (V * V) + 1216 * V + 448 := by ring
  have hgrow : (24 * V + 14) * (2 * (16 * (V + 1))) ≤ F * (2 * (16 * (V + 1))) :=
    Nat.mul_le_mul hFge (Nat.le_refl _)
  have hlhs : 8 * (3 * (32 * (V + 1) * V + 16 * (V + 1) + 1) + 3)
      = 768 * (V * V) + 1152 * V + 432 := by ring
  rw [hlhs]
  obtain ⟨S, hS⟩ : ∃ S, V * V = S := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, F * (2 * (16 * (V + 1))) = T := ⟨_, rfl⟩
  rw [hS] at hbase
  rw [hbase, hT] at hgrow
  rw [hS, hT]
  clear hbase hS hT hlhs
  omega

/-- The protected margin, as the check states it. -/
theorem protected_margin' : 2 * I.protectedLength ≤ I.relatorFloor :=
  I.protected_margin

/-! ## 5.  The bundle, and the endpoint -/

/-- **The check bundle at the explicit family.**  Its relator set is the
family's on the nose, so the bridge hypothesis downstream is `rfl`. -/
def metricData : AvatarMetricCheck.AvatarMetricData where
  relators := D.relators
  maxExponent := maxExponent D
  relatorFloor := I.relatorFloor
  protectedLength := I.protectedLength
  relators_long := I.relators_long
  runs_short :=
    AvatarMetricCheck.runs_short_of_doubled (A := maxExponent D) I.runs_short
  pinned := I.pinned
  uniqueMark := I.uniqueMark
  metric_margin := I.metric_margin
  protected_margin := I.protected_margin'

@[simp] theorem metricData_relators : (I.metricData).relators = D.relators := rfl

/-- **The family's four obligations**, from the bundle.  Only nontriviality of
the protected avatar is left, and it is not a metric-side fact. -/
theorem obligations
    (hne : FreeGroup.lift D.srcAvatar D.protectedWord ≠ 1) : D.Obligations :=
  D.obligations_of_metricData I.metricData rfl hne I.protected_norm

/-- **The router design**, fully assembled. -/
noncomputable def design
    (hne : FreeGroup.lift D.srcAvatar D.protectedWord ≠ 1) :
    BespokeRouter.RouterRelatorDesign E N s B :=
  D.design (I.obligations hne)

/-- **The router's word-combinatorial conclusions**, from the two residuals.
Everything metric-side is discharged; the binders are the residual bundle and
the protected avatar. -/
theorem routerConclusions
    (hne : FreeGroup.lift D.srcAvatar D.protectedWord ≠ 1)
    (h : SmallCancellationRouter.SharpResiduals (Fin 2)) :
    (I.design hne).RouterConclusions :=
  AvatarMetricCheck.routerConclusions_of_check_of_residuals
    (I.design hne) I.metricData rfl h

/-- **The endpoint.**  A blueprint, its inputs, a nontrivial protected avatar and
the residual bundle produce the frozen router output. -/
theorem nonempty_routingLemmaData [N.Normal]
    (hne : FreeGroup.lift D.srcAvatar D.protectedWord ≠ 1)
    (h : SmallCancellationRouter.SharpResiduals (Fin 2)) :
    Nonempty (SmallCancellationRouter.RoutingLemmaData E N s B) :=
  AvatarMetricCheck.nonempty_routingLemmaData_of_check_of_residuals
    (I.design hne) I.metricData rfl h

end Inputs

end AvatarRouterInstance
end GroupApproximation

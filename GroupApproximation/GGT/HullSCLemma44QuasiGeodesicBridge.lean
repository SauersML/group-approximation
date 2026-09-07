import GroupApproximation.GGT.HullSCLemma44FamilyAssembly
import GroupApproximation.GGT.HullSCRelativeGreendlingerGeodesicConsumers
import GroupApproximation.GGT.HullSCRelativeGreendlingerQuasiGeodesicSpelling

/-!
# Osin's Lemma 5.1 with its own case split, and Hull Lemma 4.4 above it

## The obligation was filed against the wrong lemma

`RelativeIsoperimetricBridgeStatement` is Osin, *Small cancellations over
relatively hyperbolic groups and embedding theorems*, arXiv:math/0411039v3,
Lemma 5.1.  Its certificate hypothesis is quantified over **every**
`RelativeReducedDiagram`, with no geometry on the designated boundary word, so
the only thing that can discharge it is `RelativeGreendlingerStatement` in its
equally unrestricted form.

That is not what the source does.  Osin's Lemma 4.4 reads "Let `Delta` be a
reduced van Kampen diagram over the presentation ... whose boundary is
`(lambda,c)`-quasi-geodesic"; the hypothesis is part of the lemma.  The proof
of Lemma 5.1 supplies it by a case split of its own: "Suppose first that `p` is
not `(1/2,0)`-quasi-geodesic" — that branch decomposes the word and recurses —
and only then "Now suppose that `p` is a `(1/2,0)`-quasi-geodesic path ...
Since `C(eps,mu,lambda,c,rho)`-condition implies `C(eps,mu,1/2,c,rho)` ... we
may assume that `p` is `(lambda,c)`-quasi-geodesic as well."

This repository moved that case split out of Lemma 5.1 and onto Lemma 4.4,
where it cannot be discharged, and everything above inherited an unprovable
leaf as a consequence.  `HullSCRelativeGreendlingerFromComponents` already
records half of the diagnosis — `RelativeReducedDiagram` imposes no geometry on
its boundary word, and the source theorem needs it — but the repair was applied
only to the ball-injectivity consumers
(`HullSCRelativeGreendlingerGeodesicConsumers`).  The bridge kept the
unrestricted hypothesis, because `exists_relativeDehnCut_of_kernelBoundary`
builds its diagram from an arbitrary word spelling a kernel element.  Osin's
answer to exactly that is the case split, and it belongs inside Lemma 5.1.

## This is a strengthening, not a weakening

The next reader will see a narrowed hypothesis and reach for the standing rule
against weakening a statement to make it provable.  It does not apply, and the
direction is proved here rather than asserted:
`relativeIsoperimetricBridgeStatement_of_quasiGeodesicBridge` derives the old
bridge from the new one.  A bridge is `certificates -> control`; restricting the
certificates to quasi-geodesic-boundary diagrams makes its **hypothesis weaker**
and therefore the bridge itself **stronger**.  Nothing downstream of the bridge
is weakened, and the new statement is harder to prove in precisely the way
Osin's Lemma 5.1 is harder than the repository's version of it: it has to carry
the non-quasi-geodesic branch.

What it buys is that `RelativeGreendlingerStatement` — the over-strong leaf — is
no longer needed above the bridge.  Its place is taken by
`RelativeGreendlingerQuasiGeodesicSpellingStatement`, which
`relativeGreendlingerQuasiGeodesicSpellingStatement_of_components` **proves**
from est's three construction propositions together with two theorems of this
repository, `relativeDiscRealizationSpellingStatement` and
`relativeExteriorArcConversionAtWordRotatedStatement`.

## What is NOT established here

`RelativeGreendlingerStatement` is **not refuted**, here or anywhere in this
repository, and nothing below should be read as saying it is false.  It is
stronger than its source and no route to it is known; that is all.  A
refutation would have to use `O`-cells — over a free group the classical
Greendlinger lemma holds for every reduced diagram with no boundary condition —
and would need a diagram with at least two cells together with a spelling of its
boundary avoiding every short-sided translate of a long piece of a rotated
relator.  That is an open problem, not a lemma waiting to be written down.

## A defect in the `mu` range of the certificate conclusion

`RelativeDiagramCertificate.largeCell`
(`GGT/HullSCRelativeGreendlingerStatement.lean`) asks for an exterior arc of
length at least `(1 - 23 * mu) * |cellLabel|`, while
`RelativeGreendlingerStatement` quantifies over `mu` in `(0, 1/16]`.  For
`mu` in `[1/23, 1/16]` the coefficient is not positive, and
`certificate_of_one_le_twentyThree_mu` below proves the conclusion outright at
every such `mu` from the empty-exterior contiguity: on that part of its own
declared range the statement says nothing.  Osin's own conclusion is the strict
`> 1 - 13 * mu`, so the range and the constant are both this repository's.
Every consumer takes `mu = 1/1000`, so nothing downstream is affected; the
record is here because a statement vacuous on part of its range is a defect of
the statement.

**So the whole mathematical content of `RelativeGreendlingerStatement` lives on
`mu < 1/23`**, and anyone attacking it should start there rather than at the
printed range `(0, 1/16]`, which is strictly larger than the range where
anything has to be proved.  That is a real reduction of the problem and it is
*not* where the difficulty is: the obstruction is the boundary hypothesis, not
the constant.  The only route to the unrestricted statement in this repository,
`hullSC_relativeGreendlingerStatement_of_components`, needs
`AllReducedDiagramsHaveBaseGeodesicBoundary`, and
`not_hasBaseGeodesicBoundary_of_not_mem_base` refutes that clause at a single
peripheral letter on a boundary word — which is exactly what the diagrams
reaching the consumers have, since they are built over `D.alphabet` and its
words range over `D.base ∪ ⋃ H λ`.  Narrowing `mu` does not touch that.

Every declaration below is a complete proof or a named proposition; no
placeholder of any kind is introduced here.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

/-! ## The `mu` range on which the certificate conclusion is free -/

/-- **At `1/23 ≤ mu` every reduced diagram carries a certificate.**  The degree
coefficient `1 - 23 * mu` is then not positive, and
`RelativeBoundaryContiguity.empty` — which every relator carries — has exterior
length zero, so the length clause reads `(non-positive) * |relator| ≤ 0`.  The
diagram's positive area supplies the cell index. -/
theorem certificate_of_one_le_twentyThree_mu
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) {R eps : ℕ} {mu : ℝ}
    (hmu : 1 / 23 ≤ mu) (Z : RelativeReducedDiagram D W R) :
    Nonempty (RelativeDiagramCertificate D W eps mu Z) := by
  have hcells : 0 < Z.cells.length := by
    rw [Z.cells_length]
    exact Z.area_pos
  let i : Fin Z.cells.length := ⟨0, hcells⟩
  refine ⟨RelativeDiagramCertificate.ofLargeCell i
    (RelativeBoundaryContiguity.empty D eps Z.boundaryWord
      (Z.cells.get i).relator) ?_⟩
  have hcoeff : (1 : ℝ) - 23 * mu ≤ 0 := by linarith
  have hlen : (0 : ℝ) ≤ (((Z.cells.get i).relator).length : ℝ) :=
    Nat.cast_nonneg _
  have hprod := mul_le_mul_of_nonneg_right hcoeff hlen
  rw [zero_mul] at hprod
  simpa only [RelativeBoundaryContiguity.empty_exterior_length,
    Nat.cast_zero] using hprod

/-- **The certificate half of `RelativeGreendlingerStatement` is free on part of
its own `mu` range.**  For `mu` in `[1/23, 1/16]` the whole conclusion holds at
`eps = rho0 = 0`, with no hypothesis on `D` and none on the relator family. -/
theorem relativeGreendlingerConclusion_of_one_le_twentyThree_mu
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) {mu : ℝ} (hmu : 1 / 23 ≤ mu) :
    ∃ eps rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
      ∀ (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ),
        RelWord.IsLemma44Input D W eps mu rho →
          ∀ Z : RelativeReducedDiagram D W R,
            Nonempty (RelativeDiagramCertificate D W eps mu Z) :=
  ⟨0, 0, fun _ _ W _ _ Z => certificate_of_one_le_twentyThree_mu D W hmu Z⟩

/-! ## The bridge at the boundary hypothesis Osin's Lemma 5.1 establishes -/

/-- **Osin Lemma 5.1, pointwise, with the certificate hypothesis at
quasi-geodesic-boundary diagrams only.**

Every clause other than the certificate hypothesis is
`RelativeIsoperimetricBridgeAt` verbatim.  The certificate is asked only at
diagrams satisfying `RelativeReducedDiagram.HasQuasiGeodesicSpelling`, which is
where Osin's Lemma 4.4 applies; the non-quasi-geodesic branch of his induction
is now inside this statement, where he put it. -/
def RelativeIsoperimetricBridgeQuasiGeodesicAt
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) : Prop :=
  ∀ (eps rho : ℕ) (mu : ℝ)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {Q : Type v} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q),
    0 < mu → mu ≤ 1 / 1000 →
      20 * (eps + 1) ≤ rho →
      RelWord.IsLemma44Input D W eps mu rho →
      q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
        (∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
          Z.HasQuasiGeodesicSpelling →
            Nonempty (RelativeDiagramCertificate D W eps mu Z)) →
            Nonempty (RelativeIsoperimetricControl D q hq)

/-- Uniform form over all source relative generating sets. -/
def RelativeIsoperimetricBridgeQuasiGeodesicStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded →
      RelativeIsoperimetricBridgeQuasiGeodesicAt.{u, v, w} D

/-- **The restricted bridge is the stronger statement.**  This is the proof, not
the assertion, that narrowing the certificate hypothesis strengthens rather
than weakens: the old bridge is derived from the new one by forgetting the
boundary clause. -/
theorem relativeIsoperimetricBridgeStatement_of_quasiGeodesicBridge
    (h : RelativeIsoperimetricBridgeQuasiGeodesicStatement.{u, v, w}) :
    RelativeIsoperimetricBridgeStatement.{u, v, w} := by
  intro G _ Lambda D hD eps rho mu W Q _ q hq hmu hmuUpper hrho hsc hker hcert
  exact h D hD eps rho mu W q hq hmu hmuUpper hrho hsc hker
    (fun R Z _ => hcert R Z)

/-! ### Model checks on the restricted hypothesis -/

/-- **The restricted certificate hypothesis is satisfiable.**  Over the empty
relator family it holds at every parameter, because no reduced diagram exists
there at all.  So the narrowing has not made the bridge vacuous by making its
hypothesis unreachable. -/
theorem quasiGeodesicCertificates_emptyFamilyModel
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ) (mu : ℝ) :
    ∀ (R : ℕ) (Z : RelativeReducedDiagram D
        (∅ : Set (List (GGT.RelLetter G Lambda))) R),
      Z.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D ∅ eps mu Z) := by
  intro R Z _
  exact relativeGreendlinger_emptyFamilyModel D R Z

/-- **The restriction costs the Lemma 4.4 consumers nothing.**  Every diagram
that reaches them is `Z.toRelativeReducedDiagram`, and its boundary word is
geodesic, which is stronger than having a quasi-geodesic spelling.  So the
hypothesis is not merely satisfiable in a degenerate model: it is discharged,
with no side condition, at the diagrams the proof actually produces. -/
theorem hasQuasiGeodesicSpelling_toRelativeReducedDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : Lemma44OrientedRelatorDiagram D.alphabet W R) :
    (Z.toRelativeReducedDiagram D).HasQuasiGeodesicSpelling :=
  hasQuasiGeodesicSpelling_of_hasGeodesicBoundaryLength _
    (hasGeodesicBoundaryLength_toRelativeReducedDiagram D Z)

/-! ## Ball injectivity at the restricted certificate family -/

/-- `injOn_relativeBall_of_relativeDiagramCertificates` with the certificate
family restricted to diagrams having a quasi-geodesic spelling.  The diagram the
proof produces is a Hull Lemma 4.4 diagram, so the hypothesis is discharged. -/
theorem injOn_relativeBall_of_quasiGeodesicCertificates
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 92)
    (hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    {Q : Type*} [Group Q] (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ Z : RelativeReducedDiagram D W R,
      Z.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D W eps mu Z)) :
    Set.InjOn q (cayleyBall D.alphabet R) :=
  injOn_relativeBall_of_geodesicLengthCertificates D hsc hmu hthreshold q hker
    (fun Z hZ =>
      hcert Z (hasQuasiGeodesicSpelling_of_hasGeodesicBoundaryLength Z hZ))

/-- **The missing half of the flip.**
`HullSCRelativeGreendlingerGeodesicConsumers` restricted
`injOn_relativeBall_of_relativeDiagramCertificates` but not its
ball-and-peripheral-union companion, which is the one Hull's canonical quotient
statement calls.  This is that companion at the restricted hypothesis; the proof
is the original one with the restricted ball theorem substituted. -/
theorem injOn_ball_and_peripheralUnion_of_quasiGeodesicCertificates
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (A : Alphabet G)
    (hA : A.carrier ⊆ D.alphabet.carrier)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 92)
    (hthreshold :
      4 * ((2 * max R 1 + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    {Q : Type*} [Group Q] (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ Z : RelativeReducedDiagram D W (max R 1),
      Z.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D W eps mu Z)) :
    Set.InjOn q (cayleyBall A R) ∧
      Set.InjOn q (⋃ i : Lambda, (D.fam i : Set G)) := by
  have hinj : Set.InjOn q (cayleyBall D.alphabet (max R 1)) :=
    injOn_relativeBall_of_quasiGeodesicCertificates D hsc hmu hthreshold q hker
      hcert
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    apply hinj
    · apply cayleyBall_subset_of_le_radius D.alphabet
        (Nat.le_max_left R 1)
      exact cayleyBall_subset_of_alphabet_subset A D.alphabet hA R hx
    · apply cayleyBall_subset_of_le_radius D.alphabet
        (Nat.le_max_left R 1)
      exact cayleyBall_subset_of_alphabet_subset A D.alphabet hA R hy
    · exact hxy
  · apply injOn_peripheralUnion_of_injOn_cayleyBall_one D q
    intro x hx y hy hxy
    apply hinj
    · apply cayleyBall_subset_of_le_radius D.alphabet
        (Nat.le_max_right R 1)
      exact hx
    · apply cayleyBall_subset_of_le_radius D.alphabet
        (Nat.le_max_right R 1)
      exact hy
    · exact hxy

/-- `quotientPeripheralPreservation_of_relativeDiagramCertificates` against the
restricted bridge. -/
theorem quotientPeripheralPreservation_of_quasiGeodesicCertificates
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicStatement.{u, u, 0})
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (D : AuxiliaryPeripheralFamily A N S)
    {eps rho : ℕ} {mu : ℝ}
    {W : Set (List
      (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 1000)
    (hrho : 20 * (eps + 1) ≤ rho)
    (hsc : RelWord.IsLemma44Input D.rel W eps mu rho)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (r : ℕ) (Z : RelativeReducedDiagram D.rel W r),
      Z.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D.rel W eps mu Z))
    (hinj : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (D.cores.peripheral i : Set G))) :
    Nonempty (QuotientPeripheralPreservation q D) := by
  obtain ⟨C⟩ := hbridge D.rel D.embedded eps rho mu W q hq
    hmu hmuUpper hrho hsc hker hcert
  exact quotientPeripheralPreservation_of_isoperimetricControl D q hq C hinj

/-! ## Hull Lemma 4.4 above the restricted bridge -/

/-- **Hull's canonical quotient statement from the two source-faithful
inputs.**  This is
`hullLemma44CanonicalQuotientStatement_of_greendlinger_of_isoperimetric` with
both hypotheses replaced by the forms that carry their source's boundary
condition: the certificate at diagrams with a quasi-geodesic spelling, and the
bridge that asks for no more than that.  Every numerical choice is the
original's. -/
theorem hullLemma44CanonicalQuotientStatement_of_quasiGeodesic
    (hgeom : RelativeGreendlingerQuasiGeodesicSpellingStatement.{u, 0})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicStatement.{u, u, 0}) :
    HullLemma44CanonicalQuotientStatement.{u} := by
  intro G _ A N k S D R
  let mu : ℝ := 1 / 1000
  have hmuPos : 0 < mu := by
    dsimp [mu]
    norm_num
  have hmuSixteen : mu ≤ 1 / 16 := by
    dsimp [mu]
    norm_num
  have hmuNinetyTwo : mu ≤ 1 / 92 := by
    dsimp [mu]
    norm_num
  have hmuThousand : mu ≤ 1 / 1000 := le_rfl
  obtain ⟨eps, rho₀, hcertificate⟩ :=
    hgeom D.rel D.embedded mu hmuPos hmuSixteen
  let fullRadius : ℕ := max R 1
  let boundaryScale : ℕ := 2 * fullRadius + 2 * eps + 1
  let rho : ℕ := max rho₀ (max (8 * boundaryScale) (20 * (eps + 1)))
  have hrho₀ : rho₀ ≤ rho := Nat.le_max_left _ _
  have hrhoScale : 8 * boundaryScale ≤ rho :=
    le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hrhoDehn : 20 * (eps + 1) ≤ rho :=
    le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hscalePos : (0 : ℝ) < (boundaryScale : ℝ) := by
    dsimp [boundaryScale, fullRadius]
    positivity
  have hrhoScaleReal :
      (8 : ℝ) * (boundaryScale : ℝ) ≤ (rho : ℝ) := by
    exact_mod_cast hrhoScale
  have hthreshold :
      4 * ((2 * max R 1 + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ) := by
    change 4 * (boundaryScale : ℝ) < (3 / 4 : ℝ) * (rho : ℝ)
    nlinarith
  refine ⟨eps, rho, mu, hmuPos, ?_⟩
  intro W Q _ q hsc hsurj hker
  have hcert : ∀ (r : ℕ) (Z : RelativeReducedDiagram D.rel W r),
      Z.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D.rel W eps mu Z) := by
    intro r Z hZ
    exact hcertificate rho hrho₀ W r hsc Z hZ
  have hAlphabet : A.alphabet.carrier ⊆ D.rel.alphabet.carrier := by
    intro x hx
    exact Set.mem_union_left _ (D.base_le hx)
  have hinject :=
    injOn_ball_and_peripheralUnion_of_quasiGeodesicCertificates
      D.rel A.alphabet hAlphabet hsc hmuNinetyTwo hthreshold q hker
        (hcert (max R 1))
  have hinjectCores : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (D.cores.peripheral i : Set G)) := by
    intro x hx y hy hxy
    apply hinject.2
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rw [D.fam_eq i]
      exact hi
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rw [D.fam_eq i]
      exact hi
    · exact hxy
  refine ⟨hinject.1, ?_⟩
  exact quotientPeripheralPreservation_of_quasiGeodesicCertificates
    hbridge D q hsurj hmuPos hmuThousand hrhoDehn hsc hker hcert hinjectCores

/-- **The two residual controls above the restricted bridge.**  This is
`familyInclusionRelativeControlStatement_of_greendlinger_of_isoperimetric_of_respelling`
with the same two substitutions.  The re-spelling input is unchanged: it is
combinatorial and mentions no diagram. -/
theorem familyInclusionRelativeControlStatement_of_quasiGeodesic_of_respelling
    (hgeom : RelativeGreendlingerQuasiGeodesicSpellingStatement.{u, w})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicStatement.{u, u, w})
    (hrespell : HullRelatorRespellingStatement.{u, w}) :
    FamilyInclusionRelativeControlStatement.{u, w} := by
  intro G _ A N k S selected Lambda original joint horiginal hjoint hinl hinr
  let mu : ℝ := 1 / 1000
  have hmuPos : 0 < mu := by
    dsimp [mu]
    norm_num
  have hmuSixteen : mu ≤ 1 / 16 := by
    dsimp [mu]
    norm_num
  have hmuThousand : mu ≤ 1 / 1000 := le_rfl
  obtain ⟨epsO, rho0O, hcertO⟩ :=
    hgeom original horiginal mu hmuPos hmuSixteen
  obtain ⟨epsJ, rho0J, hcertJ⟩ := hgeom joint hjoint mu hmuPos hmuSixteen
  obtain ⟨epsS, rhoS, hres⟩ :=
    hrespell selected original joint horiginal hjoint hinl hinr mu hmuPos
      hmuThousand (max epsO epsJ) (max rho0O rho0J)
  refine ⟨epsS, rhoS, mu, hmuPos, ?_⟩
  intro W Q _ q hq hsc hker
  obtain ⟨hrespO, hrespJ⟩ := hres W hsc
  constructor
  · obtain ⟨W', eps', rho', heps', hrho', h20', hlist', hsc'⟩ := hrespO
    have hepsO : epsO ≤ eps' := le_trans (Nat.le_max_left _ _) heps'
    have hrhoO : rho0O ≤ rho' := le_trans (Nat.le_max_left _ _) hrho'
    have hscO : RelWord.IsLemma44Input original W' epsO mu rho' :=
      hsc'.mono_parameters hepsO le_rfl le_rfl
    have hkerO : q.ker =
        Subgroup.normalClosure (GGT.RelLetter.listVal '' W') := by
      rw [hker, hlist']
    have hstep : 20 * (epsO + 1) ≤ 20 * (eps' + 1) := by omega
    have h20 : 20 * (epsO + 1) ≤ rho' := le_trans hstep h20'
    have hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram original W' R),
        Z.HasQuasiGeodesicSpelling →
          Nonempty (RelativeDiagramCertificate original W' epsO mu Z) := by
      intro R Z hZ
      exact hcertO rho' hrhoO W' R hscO Z hZ
    exact hbridge original horiginal epsO rho' mu W' q hq hmuPos hmuThousand
      h20 hscO hkerO hcert
  · obtain ⟨W', eps', rho', heps', hrho', h20', hlist', hsc'⟩ := hrespJ
    have hepsJ : epsJ ≤ eps' := le_trans (Nat.le_max_right _ _) heps'
    have hrhoJ : rho0J ≤ rho' := le_trans (Nat.le_max_right _ _) hrho'
    have hscJ : RelWord.IsLemma44Input joint W' epsJ mu rho' :=
      hsc'.mono_parameters hepsJ le_rfl le_rfl
    have hkerJ : q.ker =
        Subgroup.normalClosure (GGT.RelLetter.listVal '' W') := by
      rw [hker, hlist']
    have hstep : 20 * (epsJ + 1) ≤ 20 * (eps' + 1) := by omega
    have h20 : 20 * (epsJ + 1) ≤ rho' := le_trans hstep h20'
    have hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram joint W' R),
        Z.HasQuasiGeodesicSpelling →
          Nonempty (RelativeDiagramCertificate joint W' epsJ mu Z) := by
      intro R Z hZ
      exact hcertJ rho' hrhoJ W' R hscJ Z hZ
    exact hbridge joint hjoint epsJ rho' mu W' q hq hmuPos hmuThousand
      h20 hscJ hkerJ hcert

/-- **Leaf B from three source-faithful inputs.**  The replacement for
`hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_controls`:
the certificate is asked only where Osin's Lemma 4.4 applies, and the bridge
carries Lemma 5.1's own case split.  The assembly above the two controls is
unchanged and is reused verbatim. -/
theorem hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_quasiGeodesicControls
    (hgeom : RelativeGreendlingerQuasiGeodesicSpellingStatement.{u, 0})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicStatement.{u, u, 0})
    (hrespell : HullRelatorRespellingStatement.{u, 0}) :
    HullLemma44CanonicalQuotientFamilyInclusionJointStatement.{u, 0} :=
  hullLemma44CanonicalQuotientFamilyInclusionJointStatement_of_canonical_of_controls
    (hullLemma44CanonicalQuotientStatement_of_quasiGeodesic hgeom hbridge)
    (familyInclusionRelativeControlStatement_of_quasiGeodesic_of_respelling
      hgeom hbridge hrespell)

/-! ## A recorded gap in the joint-family binder

`HullRelatorRespellingStatement` is left exactly as it stands; it is not touched
by this repair.  One observation about it belongs on the record here, because it
was found while tracing this chain and will otherwise be rediscovered.

`jointRelatorRespellingStatement_proved`
(`GGT/HullSCLemma44JointRelabel.lean`) is a theorem: the joint half of the
re-spelling is pure index relabelling.  It needs, among other structural
hypotheses, `joint.base ⊆ selected.rel.base`.  What
`HullLemma44CanonicalQuotientFamilyInclusionJointStatement` binds instead is
`∃ T, T.Finite ∧ T ⊆ selected.rel.alphabet.carrier ∧ joint.base ⊆ original.base ∪ T`,
and `alphabet.carrier` is `base ∪ ⋃ fam`, so `T` may contain peripheral
elements that are not base letters.  The theorem below shows the containment
does follow once `T` is asked to land in the base — so the gap is exactly that
one word in the binder, and nothing more. -/

/-- **The joint base is contained in the selected base once the adjoined
letters are base letters.**  `original.alphabet.carrier ⊆ A.alphabet.carrier`
is the binder the family form already carries, and
`AuxiliaryPeripheralFamily.base_le` carries `A.alphabet.carrier` into
`selected.rel.base`. -/
theorem jointBase_subset_selectedBase_of_baseAdjoined
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hA : original.alphabet.carrier ⊆ A.alphabet.carrier)
    (hsub : ∃ T : Set G, T ⊆ selected.rel.base ∧
      joint.base ⊆ original.base ∪ T) :
    joint.base ⊆ selected.rel.base := by
  obtain ⟨T, hT, hjoint⟩ := hsub
  intro x hx
  rcases hjoint hx with hbase | hadjoined
  · exact selected.base_le (hA (Set.mem_union_left _ hbase))
  · exact hT hadjoined

end HullSC
end GroupApproximation

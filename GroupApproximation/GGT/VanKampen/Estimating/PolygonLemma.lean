import GroupApproximation.GGT.DGOProposition414GapCompletionCounts
import GroupApproximation.GGT.VanKampen.Estimating.Unbound

/-!
# The uniform polygon input for unbound arcs

This file connects the polygon obtained in Osin's Appendix Lemma 62 with
Dahmani--Guirardel--Osin Proposition 4.14.  After cutting a complementary
diagram to a disc, every non-distinguished side has one of three sources:

* a geodesic replacement of an unbound arc or cutting path;
* a side of an `epsilon`-contiguity region, whose length is at most `epsilon`;
* an outer-boundary side already certified as a `(1,epsilon)` chain.

All three sources give the off-target clause of `SumBoundInput`.  The
distinguished sides are the isolated peripheral components.  Thus the uniform
constant in Proposition 4.14 bounds their total relative radii and, for deep
components, their number.  The last theorem applies the current dgo414
balanced-surgery interface, so its only remaining inputs are the child
component configurations and the distributed factor placement.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace UnboundEstimate

open DGOPolygonCut
open DGOProposition414
open OsinComponents
open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Lambda : Type w}

/-! ## The three kinds of sides after cutting the diagram -/

/-- A non-distinguished side of the disc cut used in Appendix Lemma 62.

The first constructor is used for geodesic replacements of unbound arcs,
outer-boundary arcs, and cutting paths.  The second is used for side arcs of
contiguity regions; their shortness alone gives the `(1,epsilon)` lower bound.
The third permits an outer-boundary segment for which the required additive
chain estimate has already been proved. -/
inductive CutDiscSideSource (D : RelGenSet G Lambda) (epsilon : Nat)
    (basepoint : G) (word : List (RelLetter G Lambda))
    (cut : Nat -> Nat) (side : Nat) : Prop
  | geodesicReplacement
      (chain : IsGeodesicChain D.alphabet.carrier
        (fun i => vertex basepoint word (cut side + i))
        (cut (side + 1) - cut side))
  | contiguitySide
      (length_le : cut (side + 1) - cut side <= epsilon)
  | outerBoundary
      (chain : IsQuasiGeodesicChain D.alphabet.carrier epsilon
        (fun i => vertex basepoint word (cut side + i))
        (cut (side + 1) - cut side))

namespace CutDiscSideSource

/-- The vertex sequence of a geodesic word is a geodesic chain.  This is the
word-to-chain conversion used for every replacement path in the cut disc. -/
theorem isGeodesicChain_of_isGeodesicWord (D : RelGenSet G Lambda)
    {first last : G} {replacement : List (RelLetter G Lambda)}
    (hword : IsGeodesicWord D first last replacement) :
    IsGeodesicChain D.alphabet.carrier
      (fun i => vertex first replacement i) replacement.length := by
  intro i j hij hj
  have hsegment := isGeodesicWord_segment D hword hij hj
  have hlength : ((replacement.drop i).take (j - i)).length = j - i := by
    rw [List.length_take, List.length_drop]
    omega
  exact hsegment.2.2.symm.trans hlength

/-- A side coming from a geodesic replacement satisfies the source
classification with no additive loss. -/
theorem of_geodesicChain (D : RelGenSet G Lambda) (epsilon : Nat)
    (basepoint : G) (word : List (RelLetter G Lambda))
    (cut : Nat -> Nat) (side : Nat)
    (chain : IsGeodesicChain D.alphabet.carrier
      (fun i => vertex basepoint word (cut side + i))
      (cut (side + 1) - cut side)) :
    CutDiscSideSource D epsilon basepoint word cut side :=
  .geodesicReplacement chain

/-- An `IsGeodesicWord` on the exact side segment gives the geodesic
replacement constructor.  `vertex_segment` identifies its local vertices
with the corresponding vertices of the full cut-disc boundary word. -/
theorem of_geodesicWord (D : RelGenSet G Lambda) (epsilon : Nat)
    (basepoint : G) (word : List (RelLetter G Lambda))
    (cut : Nat -> Nat) (side : Nat)
    (hmono : cut side <= cut (side + 1))
    (hend : cut (side + 1) <= word.length)
    (replacementGeodesic : IsGeodesicWord D
      (vertex basepoint word (cut side))
      (vertex basepoint word (cut (side + 1)))
      ((word.drop (cut side)).take (cut (side + 1) - cut side))) :
    CutDiscSideSource D epsilon basepoint word cut side := by
  apply CutDiscSideSource.geodesicReplacement
  have hchain := isGeodesicChain_of_isGeodesicWord D replacementGeodesic
  intro i j hij hj
  have hlength :
      ((word.drop (cut side)).take (cut (side + 1) - cut side)).length =
        cut (side + 1) - cut side := by
    rw [List.length_take, List.length_drop]
    omega
  have hjReplacement : j <=
      ((word.drop (cut side)).take (cut (side + 1) - cut side)).length := by
    rw [hlength]
    exact hj
  have hiReplacement : i <=
      ((word.drop (cut side)).take (cut (side + 1) - cut side)).length :=
    hij.trans hjReplacement
  have hlocal := hchain i j hij hjReplacement
  rw [vertex_segment word basepoint (cut side)
      (cut (side + 1) - cut side) i hiReplacement,
    vertex_segment word basepoint (cut side)
      (cut (side + 1) - cut side) j hjReplacement] at hlocal
  exact hlocal

/-- An `epsilon`-contiguity side satisfies the source classification using
only its length bound. -/
theorem of_contiguitySide (D : RelGenSet G Lambda) (epsilon : Nat)
    (basepoint : G) (word : List (RelLetter G Lambda))
    (cut : Nat -> Nat) (side : Nat)
    (length_le : cut (side + 1) - cut side <= epsilon) :
    CutDiscSideSource D epsilon basepoint word cut side :=
  .contiguitySide length_le

/-- Each of the three side sources gives the real `(1,epsilon)` inequality
required away from the distinguished components by `SumBound`. -/
theorem quasi {D : RelGenSet G Lambda} {epsilon : Nat}
    {basepoint : G} {word : List (RelLetter G Lambda)}
    {cut : Nat -> Nat} {side p q : Nat}
    (source : CutDiscSideSource D epsilon basepoint word cut side)
    (hmono : cut side <= cut (side + 1))
    (hp : cut side <= p) (hpq : p <= q) (hq : q <= cut (side + 1)) :
    ((q - p : Nat) : Real) - (epsilon : Real) <=
      ((wordDist D.alphabet.carrier
        (vertex basepoint word p) (vertex basepoint word q) : Nat) : Real) := by
  have hp_eq : cut side + (p - cut side) = p := by omega
  have hq_eq : cut side + (q - cut side) = q := by omega
  have hdiff : (q - cut side) - (p - cut side) = q - p := by omega
  have hlocal_order : p - cut side <= q - cut side := by omega
  have hlocal_end : q - cut side <= cut (side + 1) - cut side := by omega
  cases source with
  | geodesicReplacement chain =>
      have hchain := chain (p - cut side) (q - cut side)
        hlocal_order hlocal_end
      change wordDist D.alphabet.carrier
          (vertex basepoint word (cut side + (p - cut side)))
          (vertex basepoint word (cut side + (q - cut side))) =
        (q - cut side) - (p - cut side) at hchain
      rw [hp_eq, hq_eq, hdiff] at hchain
      rw [hchain]
      exact sub_le_self _ (by positivity)
  | contiguitySide length_le =>
      have hlength : q - p <= epsilon := by omega
      have hlengthReal : ((q - p : Nat) : Real) <= (epsilon : Real) := by
        exact_mod_cast hlength
      have hdist : 0 <= ((wordDist D.alphabet.carrier
          (vertex basepoint word p) (vertex basepoint word q) : Nat) : Real) := by
        positivity
      linarith
  | outerBoundary chain =>
      have hchain := chain (p - cut side) (q - cut side)
        hlocal_order hlocal_end
      change (q - cut side - (p - cut side)) - epsilon <=
            wordDist D.alphabet.carrier
              (vertex basepoint word (cut side + (p - cut side)))
              (vertex basepoint word (cut side + (q - cut side))) /\
          wordDist D.alphabet.carrier
              (vertex basepoint word (cut side + (p - cut side)))
              (vertex basepoint word (cut side + (q - cut side))) <=
            q - cut side - (p - cut side) at hchain
      rw [hp_eq, hq_eq, hdiff] at hchain
      have hcast : (((q - p) - epsilon : Nat) : Real) <=
          ((wordDist D.alphabet.carrier
            (vertex basepoint word p) (vertex basepoint word q) : Nat) : Real) := by
        exact_mod_cast hchain.1
      by_cases hepsilon : epsilon <= q - p
      · rw [Nat.cast_sub hepsilon] at hcast
        exact hcast
      · have hsmall : ((q - p : Nat) : Real) <= (epsilon : Real) := by
          exact_mod_cast (Nat.le_of_not_ge hepsilon)
        have hdist : 0 <= ((wordDist D.alphabet.carrier
            (vertex basepoint word p) (vertex basepoint word q) : Nat) : Real) := by
          positivity
        linarith

end CutDiscSideSource

/-! ## A cut complementary disc as a `SumBoundInput` -/

/-- The polygonal boundary produced after a complementary component is cut
to a disc in Appendix Lemma 62.

`target` consists of isolated peripheral component sides.  Every other side
is classified by `sideSource`; this is the precise interface between the
diagram boundary (unbound arcs, short contiguity sides, and outer arcs) and
the polygon vocabulary of DGO Proposition 4.14. -/
structure CutDiscPolygon (D : RelGenSet G Lambda) (epsilon n : Nat) where
  basepoint : G
  word : List (RelLetter G Lambda)
  cut : Nat -> Nat
  target : Finset Nat
  label : Nat -> Lambda
  letters : forall a, a ∈ word -> D.IsLetter a
  closed : RelLetter.listVal word = 1
  polygonCut : IsPolygonCut n word cut
  target_lt : forall s, s ∈ target -> s < n
  target_edge : forall s, s ∈ target -> cut (s + 1) = cut s + 1
  target_component : forall s, s ∈ target ->
    IsComp (label s) word (cut s) (cut (s + 1))
  target_isolated : forall s, s ∈ target ->
    IsIsolated D.fam (label s) basepoint word (cut s)
  sideSource : forall s, s < n -> s ∉ target ->
    CutDiscSideSource D epsilon basepoint word cut s

namespace CutDiscPolygon

/-- The cut-disc boundary is an admissible input to DGO Proposition 4.14.
Geodesic replacements and outer chains supply long-side quasigeodesicity;
the length bound on each contiguity side supplies the same estimate there. -/
def toSumBoundInput {D : RelGenSet G Lambda} {epsilon n : Nat}
    (P : CutDiscPolygon D epsilon n) :
    SumBoundInput D (epsilon : Real) n where
  basepoint := P.basepoint
  word := P.word
  cut := P.cut
  target := P.target
  label := P.label
  letters := P.letters
  closed := P.closed
  polygonCut := P.polygonCut
  target_lt := P.target_lt
  target_edge := P.target_edge
  target_component := P.target_component
  target_isolated := P.target_isolated
  quasi := by
    intro s hs htarget p q hp hpq hq
    exact (P.sideSource s hs htarget).quasi
      (P.polygonCut.mono s) hp hpq hq

/-- A uniform `SumBound` gives the total relative-length estimate for all
isolated components on one cut complementary-disc boundary.  This is the
uniform polygon estimate used after the arc count in Appendix Lemma 62. -/
theorem hasRadiusWitnessAtMost_of_sumBound
    {D : RelGenSet G Lambda} {epsilon n K : Nat}
    (P : CutDiscPolygon D epsilon n)
    (hK : SumBound D (epsilon : Real) n K) :
    P.toSumBoundInput.HasRadiusWitnessAtMost K :=
  P.toSumBoundInput.hasRadiusWitnessAtMost_of_sumBound hK

/-- If every isolated component lies outside the relative ball of radius
`M`, the uniform polygon sum also bounds the number of those components. -/
theorem target_card_mul_le_of_sumBound
    {D : RelGenSet G Lambda} {epsilon n K M : Nat}
    (P : CutDiscPolygon D epsilon n)
    (hK : SumBound D (epsilon : Real) n K)
    (hdeep : forall s, s ∈ P.target ->
      (vertex P.basepoint P.word (P.cut s))⁻¹ *
          vertex P.basepoint P.word (P.cut (s + 1)) ∉
        D.relBall (P.label s) M) :
    P.target.card * (M + 1) <= K := by
  exact card_le_of_sumBound hK P.basepoint P.word P.cut P.target P.label
    P.letters P.closed P.polygonCut P.target_lt P.target_edge
    P.target_component P.target_isolated
    P.toSumBoundInput.quasi hdeep

end CutDiscPolygon

/-! ## Uniform bounds and the dgo414 frontier -/

/-- DGO Proposition 4.14 gives one constant, chosen before the complementary
disc and its number of sides, which bounds every isolated-component radius
sum arising in Appendix Lemma 62. -/
theorem unboundArcBound_of_uniform414
    (D : RelGenSet G Lambda) (epsilon : Nat)
    (h414 : UniformProposition414Statement D epsilon)
    (hsymm : forall x, x ∈ D.base -> x⁻¹ ∈ D.base)
    (delta : Nat)
    (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) :
    ∃ L : Nat, forall n : Nat, 1 <= n ->
      forall P : CutDiscPolygon D epsilon n,
        P.toSumBoundInput.HasRadiusWitnessAtMost (L * n) := by
  obtain ⟨L, hL⟩ := h414 hsymm delta hdelta
  refine ⟨L, ?_⟩
  intro n hn P
  exact P.hasRadiusWitnessAtMost_of_sumBound (hL n hn)

/-- The same uniform constant gives the deep-component count needed when the
estimating argument converts a relative-length lower bound into an arc-count
bound. -/
theorem unboundArcCountBound_of_uniform414
    (D : RelGenSet G Lambda) (epsilon : Nat)
    (h414 : UniformProposition414Statement D epsilon)
    (hsymm : forall x, x ∈ D.base -> x⁻¹ ∈ D.base)
    (delta : Nat)
    (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) :
    ∃ L : Nat, forall n : Nat, 1 <= n ->
      forall (P : CutDiscPolygon D epsilon n) (M : Nat),
        (forall s, s ∈ P.target ->
          (vertex P.basepoint P.word (P.cut s))⁻¹ *
              vertex P.basepoint P.word (P.cut (s + 1)) ∉
            D.relBall (P.label s) M) ->
        P.target.card * (M + 1) <= L * n := by
  obtain ⟨L, hL⟩ := h414 hsymm delta hdelta
  refine ⟨L, ?_⟩
  intro n hn P M hdeep
  exact P.target_card_mul_le_of_sumBound (hL n hn) hdeep

/-- The current dgo414 balanced-surgery result supplies exactly the uniform
statement consumed by `Unbound.lean` once the two remaining geometric fields
are produced on every balanced split. -/
theorem uniformProposition414_of_gapGeometry
    (D : RelGenSet G Lambda) (epsilon : Nat)
    (geometry : forall
      (hsymm : forall x, x ∈ D.base -> x⁻¹ ∈ D.base)
      (delta : Nat)
      (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
      {n k R : Nat} (P : SumBoundInput D (epsilon : Real) n)
      (B : BalancedSplitData D hsymm epsilon hdelta P k R),
        ∃ components : BalancedSplitData.GapComponentConfigurations
            hsymm hdelta P B,
          Nonempty (TwoHalfDistributedFactorPlacement D hsymm epsilon hdelta
            (B.gapIntervalsOfConfigurations components).toPathInput.family
            P.target P.label P.span)) :
    UniformProposition414Statement D epsilon := by
  intro hsymm delta hdelta
  exact sumBound_linear_of_gapGeometry D hsymm epsilon hdelta
    (geometry hsymm delta hdelta)

/-! ## Model checks -/

/-- The empty one-sided polygon realizes the cut-disc interface.  Its sole
side is a length-zero contiguity side, so the classification is not vacuous. -/
def emptyCutDiscPolygonModel (D : RelGenSet PUnit PUnit) (epsilon : Nat) :
    CutDiscPolygon D epsilon 1 where
  basepoint := PUnit.unit
  word := []
  cut := fun _ => 0
  target := ∅
  label := fun _ => PUnit.unit
  letters := by
    intro a ha
    simp at ha
  closed := by simp
  polygonCut := by
    refine ⟨rfl, ?_, ?_⟩
    · simp
    · intro s
      exact Nat.le_refl 0
  target_lt := by simp
  target_edge := by simp
  target_component := by simp
  target_isolated := by simp
  sideSource := by
    intro s hs htarget
    exact CutDiscSideSource.contiguitySide (by simp)

/-- In the one-element group, the uniform bound specializes to the concrete
cut-disc model with the sharp constant zero. -/
theorem unboundArcBound_pUnit_model
    (D : RelGenSet PUnit PUnit) (epsilon delta : Nat)
    (hsymm : forall x, x ∈ D.base -> x⁻¹ ∈ D.base)
    (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) :
    ∃ L : Nat, forall n : Nat, 1 <= n ->
      forall P : CutDiscPolygon D epsilon n,
        P.toSumBoundInput.HasRadiusWitnessAtMost (L * n) :=
  unboundArcBound_of_uniform414 D epsilon
    (uniformProposition414_pUnit_model D epsilon) hsymm delta hdelta

end UnboundEstimate
end VanKampen
end GGT
end GroupApproximation

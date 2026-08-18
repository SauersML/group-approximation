import GroupApproximation.Sofic.GeneralModelKazhdanTransport
import GroupApproximation.Sofic.TransportShapeBridges

/-!
# Forward transport by the printed route, at the consumers' own signature

Proof-ledger rows `FN.03` and `ID.05` ask the consumers of Kazhdan transport to
invoke the literal Section-3 theorem rather than the Appendix-B surrogate.
`transport_literal` below is that: the statement of
`KazhdanAsymptoticCommutant.transport`, character for character, proved from
`GeneralModelTransport.generalModelKazhdanTransport` — hence from
`manuscriptKazhdanTransport`, hence from the printed norm-ultraproduct
argument.

## Why this is a new declaration and not an edit to `transport`

`KazhdanAsymptoticCommutant.transport` cannot simply be repointed, because it
is not only a consumer of the route — it is the *engine of the second printed
proof*.  `ManuscriptKazhdanTransport.finiteStageKazhdanTransport` is built on
`transport` (search that module for `have hy_sq := transport B C x hx_sq`).
Rewiring `transport` onto the
ultraproduct route would therefore leave the corpus with one proof of
`\ref{thm:kazhdan-transport}` wearing two names.  That is the exact defect
class this audit exists to catch, so the finite-stage engine is left alone and
the literal route is added beside it.

Historical note: the manuscript used to announce the finite-stage proof in a
remark and print it as an appendix, and both are gone -- commit `3a45fa60` cut
them once the ultraproduct reading of the collapse step became their only
consumer.  So the "two independent printed proofs" the paragraph above guards
against is now a Lean-side fact only: what is printed is the single
ultraproduct proof inside `\ref{sec:transport}`.

The two are deliberately interchangeable: identical statement, identical
hypotheses, different proof.  A consumer picks its route by picking its name.

## The two shape changes, and why neither costs anything

The consumers state the asymptotic-commutant condition as the *conjugation
defect* `x − u x u*` in squared form; the manuscript's theorem states it as the
*commutator* `x u − u x` in unsquared form.  Both gaps are closed exactly, by
`TransportShapeBridges`: `hsNormSq_conjugation_defect` because
`x − u x u* = (x u − u x) u*` and right multiplication by a unitary is an
isometry for the normalized Hilbert--Schmidt norm, and the `ε` versus `ε²`
pairing because the two quantifications are the same convergence.  No estimate
is introduced and no constant is lost.  `finiteStageKazhdanTransport` performs
these same two conversions inline, in the opposite direction, which is the
in-repo precedent for both.
-/

namespace GroupApproximation
namespace KazhdanAsymptoticCommutant

-- Mirrors the `open` block of `Sofic/KazhdanAsymptoticCommutant.lean`, whose
-- namespace this file re-enters: the adjoint postfix and the matrix operator
-- norm are both scoped notation.
open Matrix
open scoped Matrix.Norms.L2Operator
open GroupApproximation.GeneralModelTransport

universe u

/-- **Forward Kazhdan transport, by the printed route.**  Statement-identical
to `KazhdanAsymptoticCommutant.transport`, proved from the literal Section-3
theorem instead of the finite-stage machinery. -/
theorem transport_literal
    {Γ : Type} [Group Γ] {E : Type u} [Group E]
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x) :
    IsAsymptoticCommutant B C (fun n ↦
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  -- The representation universe of property `(T)` is pinned to `0` rather than
  -- left to unification: it occurs only in this hypothesis, so an unpinned `w`
  -- becomes a universe parameter of the theorem and leaves a metavariable in
  -- every consumer's proof term.  `UltraproductRigidityRoute` records the same
  -- pin for the same reason; `manuscriptKazhdanTransport` is polymorphic here,
  -- so any instantiation is available.
  have hT : HasKazhdanPropertyTComplex.{0, 0} Γ :=
    hasKazhdanPropertyT_iff_textbook.mp C.kazhdan
  have hY : ∀ n, 0 < Fintype.card (B.model n) := B.modelNonempty
  -- The hypothesis, moved from the conjugation defect onto the commutator.
  have hxgen : ∀ γ : Γ,
      GeneralHSCommutatorVanishing B.model B.map x (C.iota γ) := by
    intro γ ε hε
    obtain ⟨N, hN⟩ := hx γ (ε ^ 2) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hu : (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
        ∈ Matrix.unitaryGroup (B.model n) ℂ := (B.map n (C.iota γ)).2
    -- Ascribing the type here beta-reduces `(fun n ↦ …) n` by `exact`.
    have hdef : hsNormSq (B.model n)
        (x n - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ)
        ≤ ε ^ 2 := hN n hn
    rw [TransportShapeBridges.hsNormSq_conjugation_defect (B.model n) hu (x n)]
      at hdef
    exact TransportShapeBridges.sqrt_hsNormSq_le_of_le_sq (B.model n) _
      hε.le hdef
  -- The printed theorem, over the consumer's own model family.
  have hmain := generalModelKazhdanTransport hT C.iota C.t C.compresses
    B.model hY B.map B.asymptoticallyMultiplicative x hbound hxgen
  -- The conclusion, moved back onto the conjugation defect.
  intro γ ε hε
  obtain ⟨N, hN⟩ := hmain γ (Real.sqrt ε) (Real.sqrt_pos.2 hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hu : (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
      ∈ Matrix.unitaryGroup (B.model n) ℂ := (B.map n (C.iota γ)).2
  have hcomm : Real.sqrt (hsNormSq (B.model n)
      (((B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
          (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) *
          ((B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
            (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ)))
      ≤ Real.sqrt ε := hN n hn
  have hsq := TransportShapeBridges.hsNormSq_le_sq_of_sqrt_le (B.model n) _
    (Real.sqrt_nonneg ε) hcomm
  rw [Real.sq_sqrt hε.le] at hsq
  show hsNormSq (B.model n)
      (((B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) -
        (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) *
          ((B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
            (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
          (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ) ≤ ε
  rw [TransportShapeBridges.hsNormSq_conjugation_defect (B.model n) hu _]
  exact hsq

/-! ## The `cor:generaltransport` chain, on the literal route

Counterparts of `transport_both`, `compressionSet_transport_both` and
`compressionGroup_transport_both`, differing from them in exactly one place:
the forward half is `transport_literal` rather than `transport`.  The
finite-stage chain is left standing beside this one, so the two routes remain
two developments and a reader can tell which one a declaration traverses from
its name.  (Only the first is printed; see the historical note above.)

The reverse half is still `transport_star`, which reverses the *approximate*
leakage bound.  That is deliberate and is the honest state: the printed reverse
step of `cor:generaltransport` is the exact identity `P = VPV* ⟹ V*PV = P`,
formalized abstractly in `Analysis/PrintedReverseTransport`, but not yet wired
to the finite-stage reverse transport.  Row `ID.05` is the forward direction and
is closed by this chain; row `ID.06` is the reverse and is not. -/

/-- **Two-sided transport, forward half on the printed route.** -/
theorem transport_both_literal
    {Γ : Type} [Group Γ] {E : Type u} [Group E]
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x) :
    IsAsymptoticCommutant B C (fun n ↦
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) ∧
      IsAsymptoticCommutant B C (fun n ↦
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) :=
  ⟨transport_literal B C x hx hbound, transport_star B C x hx hbound⟩

/-- **Every one-sided compressor transports, forward half on the printed
route.** -/
theorem compressionSet_transport_both_literal
    {Γ : Type} [Group Γ] {E : Type u} [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : ∀ gamma : Γ, HSSqVanishing B (fun n ↦
      x n - (B.map n (iota gamma) : Matrix (B.model n) (B.model n) ℂ) *
        x n * (B.map n (iota gamma) : Matrix (B.model n) (B.model n) ℂ)ᴴ))
    (hbound : IsUniformlyBounded B x)
    {s : E} (hs : s ∈ compressionSet iota.range) :
    IsAsymptoticCommutantOf B iota (adjointSequence B s x) ∧
      IsAsymptoticCommutantOf B iota (coadjointSequence B s x) := by
  let C := coreOfCompressor iota hkazhdan s hs
  have hxC : IsAsymptoticCommutant B C x := by
    change IsAsymptoticCommutantOf B iota x
    exact hx
  have htransport := transport_both_literal B C x hxC hbound
  change IsAsymptoticCommutantOf B C.iota (adjointSequence B C.t x) ∧
    IsAsymptoticCommutantOf B C.iota (coadjointSequence B C.t x) at htransport
  change IsAsymptoticCommutantOf B iota (adjointSequence B s x) ∧
    IsAsymptoticCommutantOf B iota (coadjointSequence B s x)
  exact htransport

/-- Membership in the stabilizer, established on the printed route.  The
stabilizer itself is route-agnostic: it is a property of an element, so the two
chains prove membership in the same subgroup by different arguments. -/
theorem compressionSet_subset_asymptoticCommutantStabilizer_literal
    {Γ : Type} [Group Γ] {E : Type u} [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ) :
    compressionSet iota.range ⊆ asymptoticCommutantStabilizer B iota := by
  intro s hs x hbound hx
  exact compressionSet_transport_both_literal B iota hkazhdan x hx hbound hs

theorem compressionGroup_le_asymptoticCommutantStabilizer_literal
    {Γ : Type} [Group Γ] {E : Type u} [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ) :
    compressionGroup iota.range ≤ asymptoticCommutantStabilizer B iota := by
  rw [compressionGroup, Subgroup.closure_le]
  exact compressionSet_subset_asymptoticCommutantStabilizer_literal B iota
    hkazhdan

/-- **`cor:generaltransport`, forward half on the printed route.**  Pointwise
form, ambient group arbitrary, matching `compressionGroup_transport_both`
statement for statement.  This is the declaration the manuscript badge should
cite if the corollary is to traverse the route its proof names. -/
theorem compressionGroup_transport_both_literal :
    ∀ {Γ₀ : Type} {E₀ : Type u} [Group Γ₀] [Group E₀]
    (B : OpAlmostRepresentation E₀) (iota : Γ₀ →* E₀)
    (_hkazhdan : HasKazhdanPropertyT.{0, 0} Γ₀)
    {g : E₀} (_hg : g ∈ compressionGroup iota.range)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (_hbound : IsUniformlyBounded B x)
    (_hx : IsAsymptoticCommutantOf B iota x),
    IsAsymptoticCommutantOf B iota (adjointSequence B g x) ∧
      IsAsymptoticCommutantOf B iota (coadjointSequence B g x) := by
  intro Γ₀ E₀ _ _ B iota hkazhdan g hg x hbound hx
  exact compressionGroup_le_asymptoticCommutantStabilizer_literal B iota
    hkazhdan hg x hbound hx

end KazhdanAsymptoticCommutant
end GroupApproximation

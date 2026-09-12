# hull-euler: the Euler count input of Osin's Lemma 9.7

Lane scope: H1, the producer of `EulerCountInput`
(`GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixSectionInduction.lean`), used at the
least-area Greendlinger waist.

## Modules

| Module | State |
|---|---|
| `OsinAppendixEulerSubdivided` | compiled (probe 0912-102329-28786) |
| `OsinAppendixEulerRegionFaces` | compiled (probe 0912-102329-28786) |
| `OsinAppendixEulerPhi` | compiled (probe 0912-102329-28786) |
| `OsinAppendixEulerPhiCount` | compiled (probe 0912-102329-28786) |
| `OsinAppendixEulerPhiBound` | compiled (probe 0912-102329-28786) |
| `OsinAppendixEulerHereditary` | one projection fixed after probe 0912-102329-28786; re-probe pending |
| `OsinAppendixEulerCount` | landed unverified; first elaboration pending |

## Landings

- 44c6bab14, e4cb2d641, 864fdf3d2: Subdivided and RegionFaces fixes.
- f7a0fc32e: Phi fixes from probe 3.
- 1777a684a: `card_le_of_linked` uses `Finset.card_pair_eq_two_iff`.
- cdd4b82df: `OsinAppendixEulerCount` (unverified).

## Statements

```lean
theorem PhiData.card_le_of_linked (P : PhiData family E) (V : Finset (Fin Delta.rCellCount))
    (hV : ∀ a ∈ E, ∀ s, sideCell a s ∈ V) (hne : E.Nonempty) (hlinked : ...) :
    E.card ≤ 3 * (V.card - 1)

theorem RegionCandidate.hasEndpointClosedPlanarEdgeBound_of_phiData
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible family)
    (hcell : ∀ a ∈ family, ∀ i : Fin Delta.rCellCount, (cell Delta i).face ∉ a.1)
    (hnondeg : ∀ a ∈ family, 0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length)
    (hloop : ∀ a ∈ family, a.2.target ≠ some a.2.source)
    (hmulti : ∀ a ∈ family, ∀ b ∈ family, a ≠ b → ∀ i j : Fin Delta.rCellCount,
      ((a.2.source = i ∧ a.2.target = some j) ∨ (a.2.source = j ∧ a.2.target = some i)) →
      ((b.2.source = i ∧ b.2.target = some j) ∨ (b.2.source = j ∧ b.2.target = some i)) → False)
    [DecidableEq (Fin Delta.rCellCount)] [DecidableEq (InteriorEdge family)]
    [DecidableRel (InteriorEdge.Incident (selected := family))] :
    HasEndpointClosedPlanarEdgeBound (InteriorEdge.Incident (selected := family))

theorem GloballyDistinguishedSectionFamily.hasEndpointClosedPlanarEdgeBound
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) (hlea : Delta.LeastArea)
    (hloops : S.NoLoops) (hmulti : S.NoMultipleEdges)
    [DecidableEq (RegionCandidate.InteriorEdge S.family)]
    [DecidableRel (RegionCandidate.InteriorEdge.Incident (selected := S.family))] :
    HasEndpointClosedPlanarEdgeBound
      (RegionCandidate.InteriorEdge.Incident (selected := S.family))

def PhiPrimeCountInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea → 0 < Delta.rCellCount →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        S.NoLoops → S.NoMultipleEdges →
          S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1)

theorem eulerCountInput_of_phiPrimeCount
    (hcount : PhiPrimeCountInput.{u, w, v} D lambda c eps W) :
    EulerCountInput.{u, w, v} D lambda c eps W
```

## Residual

`PhiPrimeCountInput`, the Euler count `|M| ≤ 3(n + r − 1)` of `Φ'_M` (vertices are the cells and
the sections, edges are the selected regions). A producer needs the two-gon half of Osin's `(∗)`:
two regions from one cell to one section merge when no relator cell lies between them, against
`card_minimal`. There is no producer on main; `ExteriorMergeAvailable` (`Incidence.lean`) is
stated on the historical `Candidate` type and is stronger than needed.

## Next

Re-probe `OsinAppendixEulerHereditary` and `OsinAppendixEulerCount`, then land both normally.

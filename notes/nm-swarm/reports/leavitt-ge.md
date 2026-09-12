# leavitt-ge: Tits' lemma and the GHB(7) coset complex (CCKW T2)

Target T2 is `Systolic.SimplyConnected KMSGroup.CCKW.cosetComplex`, where the coset complex is the
Tits complex of `GHB(7)` with vertex groups `⟨a, b⟩`, `⟨c, b⟩` and `⟨c, a⟩`. It is proved, with
no literature inputs.

## Modules

All four compiled in probe 0912-094055-42831 (PROBE GREEN, BUILT `GroupApproximation.Kazhdan.CCKWTitsGHB`,
base 8836fadca). Their bytes on main equal the compiled bytes. None is wired into the root.

| module | content |
|---|---|
| `Kazhdan/CCKWTitsMoves.lean` | `titsComplex G H`, the relation `Rep`, adjacency and triangles through a common representative, destuttering, and `simplyConnected_of_moves` |
| `Kazhdan/CCKWTitsTypedWords.lean` | typed letters `Letter H`, `val`, `BaseMove` (merge, drop, retype), `TypedMove`, `simplyConnected_of_typedWordProblem`, `connected_of_generated` |
| `Kazhdan/CCKWTitsPresentation.lean` | `VertexPresentation`, the letter-by-letter lift of free-group words, `typedWordProblem`, `simplyConnected_of_vertexPresentation`, `connected_of_vertexPresentation` |
| `Kazhdan/CCKWTitsGHB.lean` | `ghbVertexPresentation` (every relator lies in one vertex group) and the two endpoints |

## Endpoints

```lean
theorem GroupApproximation.CCKWTits.cckwCosetComplex_simplyConnected :
    Systolic.SimplyConnected KMSGroup.CCKW.cosetComplex
theorem GroupApproximation.CCKWTits.cckwCosetComplex_connected :
    KMSGroup.CCKW.cosetComplex.G.Connected
```

Both pass `#audit_closed_axioms` with `[propext, Classical.choice, Quot.sound]`. They come from the
general statements:

```lean
theorem simplyConnected_of_vertexPresentation (V : VertexPresentation R H) [DecidableEq S] :
    SimplyConnected (titsComplex (PresentedGroup R) H)
theorem connected_of_vertexPresentation (V : VertexPresentation R H) [DecidableEq S] :
    (titsComplex (PresentedGroup R) H).G.Connected
```

A `VertexPresentation R H` gives, for each `i`, a set `Stype i` of generators such that
`H i = (closure (of '' Stype i)).map (PresentedGroup.mk R)`. It also gives a type `τ s` with
`s ∈ Stype (τ s)` for every generator, and puts every relator in `closure (of '' Stype j)` for
some `j`.

## Census

`non_mf_groups_exist.tex` never mentions the coset complex, Tits' lemma or simple connectivity. T2
feeds kh-cckw's discharge of `hsc`/`hconn`, so this lane adds no census rows.

## Probe history

- 0912-004542-21107: CCKWTitsMoves and CCKWTitsTypedWords compiled. CCKWTitsPresentation was red with
  - an unused `DecidableEq S` on `memH` and `mk_eq_one_of_mem`;
  - the reverted hypothesis in `tw_of_red`;
  - "Unknown identifier `V`" in `typedWordProblem`, `generated` and both endpoints;
  - the `mk (x :: L)` split in `val_liftT`.

  All four were fixed in 5bef74495.
- 0912-093840-19657: CCKWTitsPresentation compiled. CCKWTitsGHB was red only on
  `Subgroup.map_closure`, which is `MonoidHom.map_closure` at the pin; fixed in 8836fadca.
- 0912-094055-42831: PROBE GREEN; CCKWTitsGHB BUILT.

# T6, graph-theoretic half: finite intersections of balls are dismantlable

Split agreed with sec4-sentences and kh-cckw:
- sec4-sentences owns `GGT/SystolicGraphConditions` (the four Props), `GGT/SystolicProjection` and
  `GGT/SystolicInvariantClique`;
- kh-cckw owns `GGT/SystolicDismantlable`;
- this lane owns `GGT/SystolicBallDismantlable.lean`.

The lead names kh-cckw's `CCKW.cckwFiniteOrderConjugateIntoVertex_of_systolicLeaves` as the consumer.

## Module

`GGT/SystolicBallDismantlable.lean` landed NM_UNVERIFIED in two steps: 6e2564b25 (the ranking) and
7db678817 (the `Dismantlable` wrapper). It is an orphan, not wired into the root. It imports
`GGT/SystolicGraphConditions`, `GGT/SystolicDismantlable`, `Meta/AxiomGuard` and Mathlib.

## Endpoints

```lean
theorem GroupApproximation.Systolic.dismantlable_of_forall_dist_le {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (hconn : G.Connected) (hF1 : ProjectionClique G)
    (hF2 : TriangleCondition G) (hC4 : NoInducedFourCycle G) (hC5 : NoInducedFiveCycle G)
    {S : Finset V} {R : ℕ} {H : Finset V} (hH : ∀ x, x ∈ H ↔ ∀ s ∈ S, G.dist s x ≤ R)
    (hne : H.Nonempty) : Dismantlable G H
theorem GroupApproximation.Systolic.exists_dismantlingRank_of_forall_dist_le
    -- same hypotheses, without DecidableEq
    : ∃ ρ : V → ℕ, (∀ x ∈ H, ∀ y ∈ H, ρ x = ρ y → x = y) ∧
        ∀ u ∈ H, (∃ y ∈ H, ρ y < ρ u) →
          ∃ w ∈ H, ρ w < ρ u ∧ ∀ x ∈ H, ρ x ≤ ρ u → (x = u ∨ G.Adj u x) → x = w ∨ G.Adj w x
```

Both carry `#audit_axioms`.

## Proof

The helpers live in `Systolic.BFS`.
1. `dist_le_of_geodesicPredecessor`: balls are closed under geodesic predecessors. Suppose `o` and
   `x` lie in `B_r(s)` and `c` is a neighbour of `x` one step closer to `o`. Then `c ∈ B_r(s)`. The
   proof is by induction on `dist o c` and uses only `ProjectionClique` and `TriangleCondition`.
2. `exists_isBFSRank`: fix `o ∈ H`. Rank `H` breadth-first, level by level. Within level `k + 1`,
   order first by the rank of a parent, then by a fixed injective index. A parent is a least-ranked
   neighbour in `H` one level down.
3. `adj_parent_of_same_level` (Chepoi): the parent of `u` is adjacent to every earlier neighbour of
   `u` on the same level. A counterexample gives an induced four-cycle or an induced five-cycle.
4. `dominated_by_parent`: among the vertices ranked no later than `u`, the parent of `u` dominates
   `u`. The wrapper deletes vertices from the top rank down, by induction on the size of an initial
   segment of the ranking.

## Probe history

- 0912-102720-64127: PROBE GREEN on the stage-1 bytes (6e2564b25); BUILT
  `GroupApproximation.GGT.SystolicBallDismantlable`, base c1a21c29d. The whole ranking compiled on
  the first probe.
- Stage 2 (7db678817, the `Dismantlable` wrapper; bytes on main) is being probed.

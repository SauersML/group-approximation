# audit-nm-4 (simple Kazhdan note): the host's unsolvable word problem, and SL₃(ℤ) in no G_X

This lane was the non-MF audit lane of session nonsofic-existence-49 (ledger `notes/nm-swarm/reports/audit-nm-4.md`).
New item from main (RESUME 08:4x): building the two paragraphs of "LEF groups" in `simple_kazhdan_sofic_group.tex` at
696c4b602 (md5 0648e5f876e467e21ebf475e08b8ee92) that follow the Osajda remark and the topological full group paragraph:

- (A) "Every group as in the last statement of Corollary cor:host has unsolvable word problem: …" [KMS Theorem 4.21; Rauzy].
- (B) "The groups G_X do not suffice here: SL₃(ℤ) lies in no G_X. …" The route is the faithful action on
  ⊕_{x,t} F₂^m, the u-degree bound, the dimension count at one site, a polynomial annihilator, finite order, and the
  Heisenberg identity [a,b]^{n²} = [aⁿ,bⁿ].

## CLAIM

CLAIM (B) SL₃(ℤ) lies in no G_X, in new modules under `GroupApproximation/Manuscript/SimpleKazhdanSofic/`:
`CrossedProductSiteAction.lean` (the faithful action of M_m(LC(X,F₂)⋊ℤ) on sites), `SiteDegreeFiniteOrder.lean`
(distorted elements with bounded u-degrees have finite order), and `SLThreeIntNoEmbedding.lean` (the Heisenberg identity
and the printed endpoint).
CLAIM (A) host unsolvable word problem: `HostUnsolvableWordProblem.lean`. The route is being ruled by main; see the log.

Interfaces: skf-degrees' `wordProblemOracle` and `wordProblemOracle_comp_injective`; sk-lef-assembly's `IsLEFHost` and
`PrintedRecursivelyPresentedLEFHost`; `Setting.G`, `ClopenCrossedProduct`.

## Log

- 08:5x: claim.

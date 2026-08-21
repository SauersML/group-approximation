# Torsion-free non-MF: full Lean formalization plan (2026-08-21)

## EXECUTION STATE v2 (evening, main @ b39ba97a) — supersedes the
## workstream statuses below; the architecture sections remain valid.

CLOSED TODAY, on main, axiom-clean: **W2 entirely** (Γ(3) certified
countable + torsion-free + f.p. + Kazhdan, hypothesis-free;
SL₃(ℤ) (T) and f.p. both proved — the P13 descent had already closed
completeness); the periodic-overlap library with the two-occurrence
dichotomy and symmetrization closure; the factor-embedding obstruction
(machine-checked); the slimmed source interface, degeneracy theorem,
Minkowski, parametric router; four documentation corrections at source.

THE COMPLETE REMAINING GAP LIST for the headline theorem:
  A. `greendlingerConclusion_of_metric` — the n ≥ 3 count.  THE deep
     math.  Sub-split: (α)-case is dischargeable NOW from the
     orientation lemma + piece/coincidence lemmas (no verdict needed);
     (β)-case (conjugator overrun, i_c > 0) awaits either a refutation
     or the spectator-reduction argument (coordinator's 4a).
  B. `isPowerTorsionFree_of_metricSmallCancellation` — the arc-inside-
     one-period case, routed through the landed dichotomy.
  C. W6 base: six operation closures + HigmanTheoremThree +
     TransportSectionFive + BridgeRecursive; then W6b (peripheral
     variant, coordinator designs) and W6c (pattern assembly).
  D. W3 instantiation: padded presentations + the exponent-code family
     of notes/W3_AVATAR_WORD_DESIGN_2026-08-21.md + a finite-family
     C'(1/6) decision toolkit (engineering, gate-independent).
  E. Assembly: BespokeRouterGateAssembly (restructure in flight) →
     discharge `bespoke_routing_exists` → endpoint lands sorry-free.
  F. W5 gates: Audit.lean wave, cairn FRONTIER regen, manuscript
     wiring, remote-build root-refresh guard (ops).

WAVE-2 FLEET (assignments of record):
  w1b-relative   → A(α): orientation lemma + CascadeLanding (α)-case
  coordinator    → A(β) mathematics; W6b design
  adversary-2    → bounded exhaustive (β)-search, interim-output duty
  w1-finewilf    → B (they own the dichotomy)
  w6a-closures-1/2, w2d → C (closures; TheoremThree)
  w0-interface   → C: BridgeRecursive (bookkeeping)
  w2a-certificate→ D (decision toolkit + padded presentations)
  w4-assembly    → E custody (verify + land when the chain closes)
  w2b-minkowski  → Hilbert-hotel cover presentation (parallel track)
  w3-router      → finish the path restore + gate assembly file

SAVE DOCTRINE (user standing order, 2026-08-21 night, after a peer
tree-reset destroyed every unlanded scaffold locally and on the MSI
mirror): save = commit AND push to main, every green increment, within
its work cycle. Scaffolds land SORRY-FREE with open leaves as explicit
hypotheses at use sites (or hypothesis structures in the
OperationClosures residual style); the unconditional form is a
one-line corollary when the hypothesis discharges. Nothing stays
unlanded. Supersedes "scaffolds stay off main".

Protocol addenda now binding: transitive-closure-clean root imports;
Audit.lean is the gate of record (sorryAx spreads silently); pristine-
origin snapshot verification for every landing; private olean root
must mirror the whole tree, listed FIRST in LEAN_PATH; working-tree
root synced to origin after every plumbing landing; no literal scan
token in prose; zero local compute.

GOAL (user-set, session hook): an unconditional, assumption-free,
zero-laundering Lean proof that a torsion-free finitely presented non-MF
group exists.  Zero laundering means all of: `literatureInputNames = []`;
no axiom-tagged transcription premises; no LAUNDERED_PROP /
ASSUMPTION_INSTANCE findings; axioms ⊆ {propext, Classical.choice,
Quot.sound}; kernel audit green.

Division of labor (user directive): Opus 5 worker agents author Lean;
the coordinating session plans and supplies the mathematics.  Builds are
MSI-only per the standing remote-build protocol.

## Where the boundary is today (three-survey synthesis, 2026-08-21)

Machine-checked already (sorry-free, root-imported):
- The analytic mechanism end to end: normal Kazhdan subgroup of the
  compression defect ⟹ dies in every corona rep ⟹ non-MF
  (`NormalKazhdanCompressionObstruction`, `NormalKazhdanMFRadical`).
- The frozen endpoint
  `FullMFRadicalEndpoint.exists_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical`
  consuming `Nonempty (FiveConditionRoutingData D)` /
  `DefectRoutingData D`.
- The router interface and keystone: `RoutingLemmaData E N s B` →
  `toDefectRoutingData` (given `hB : HasKazhdanPropertyT B`) →
  endpoint (`SmallCancellationRouter.lean`).  "Whoever proves the
  routing lemma has proved the Main Theorem."
- Word-level engine from the gate: symmetrization, pieces, C'(λ),
  `norm_bound_of_greendlinger`, `injOn_mk'_of_greendlinger`,
  `protected_injOn_of_gate`.
- Free-product consequence layer conditional on two named predicates
  (`GreendlingerLengthBound`, `TorsionIntoFactors`): factor embedding,
  torsion-free quotient, `osin_conclusion`
  (`OsinRelativeSmallCancellation`, `FreeProductConjugacy`).
- Sources: `ConcreteCompressionSource.integerSource` (affine HNN at the
  doubling map; Britton nontriviality of the marked commutator via
  Mathlib `HNNExtension`); `Algebra/HNNTorsionFree.lean`
  (`isPowerTorsionFree_hnn`); `ExplicitSuitableDefect` (free basis
  inside the defect over (ℤ→F₂)⋊ℤ, hypothesis-free).
- (T) machinery: `ExactHodgeCertificate` (finite rational SOS/Hodge
  certificate ⟹ (T), group-agnostic, PROVED);
  `hasKazhdanPropertyT_of_finiteIndex` (PROVED); gap ⟺ (T)
  (`OrbitAverageSpectralGap`).

Paper-only / open, after the surveys — the complete gap list:
- G1 `GreendlingerGate` (n ≥ 3 factors) + the relative CoprodI form.
- G2 a torsion-free f.p. Kazhdan **partner** group `B` in Lean.
- G3 the router construction (explicit relator family + derivations of
  `defect_top`, `generates`, `partner_surjective`, f.p., torsion).
- G4 interface slimming + a concrete source instance.
- G5 assembly, gates, CI, cairn bookkeeping.

Everything Hull/Osin/AH-shaped is bypassed by design (bespoke route);
clauses (a)/(d) of Hull 7.1 are consumed by nothing downstream.

## Load-bearing design facts (derived this session; verify in Phase 0)

1. **`OrderPreservingRoutingData` is degenerate.**  `orderPreserving`
   (∀ x, orderOf (q x) = orderOf x) forces `ker q = ⊥`; with the derived
   surjectivity `q` is an isomorphism and `defect_surjective` then forces
   `defectNormal = ⊤` already in the source.  It is a manuscript-phrase
   artifact; the discharge target is the injectivity-based
   `RoutingLemmaData`/`DefectRoutingData` chain.  Prove the degeneracy
   lemma and record it (FiveConditionInsufficiency style).
2. **A nontrivial defect forces a proper self-embedding of the core Γ.**
   From `comm_c` and t-conjugation: tct⁻¹ commutes with ι(α(Γ)); the HNN
   associated-subgroup isomorphism forces the transported mark to
   commute with the compressed copy, so α = id kills the defect.  Hence
   any core whose Γ is co-Hopfian (e.g. Γ(3), any higher-rank lattice)
   can never carry a nontrivial defect — and faithful irreducible
   3×3-linear Γ additionally admits no external commuting partner
   (centralizer = scalars).
3. **RESOLVED AGAINST THE HOPEFUL READING (W0 trace, verified at
   source 2026-08-21): `core.kazhdan` is LOAD-BEARING.**  The
   root-capture step
   (`MarkedCompressionRootCapture.transportedRoot_displacement_hsDistSq_vanishing:243`)
   extracts a Kazhdan pair from the BASE's (T); an amenable base
   (ascending HNN over ℤ = Baumslag–Solitar) is MF and proves nothing —
   recorded as a theorem in `Sofic/BareDefectSource.lean`.  The W0
   slimming deletes ONLY the simple-factor fields (confirmed dead on
   the endpoint chain).  Surviving sharp demand on the source base:
   (T) + proper self-embedding + centralizing root + nontrivial marked
   commutator, realized inside a torsion-free f.p. ambient.  Sela
   (torsion-free hyperbolic (T) ⟹ co-Hopfian) and lattice rigidity
   exclude every off-the-shelf group: this is the FF-shaped demand and
   is now workstream W6, on the critical path beside W1.
4. **The simple subgroup is only for nonsoficity.**  Nothing in the
   `DefectRoutingData → not_isCDEOperatorMF` chain consumes simplicity;
   the frozen endpoint's quantification over `FournierFacioDefectData`
   (which demands `IsSimpleGroup`) is an interface accident.  Split:
   Phase A = torsion-free f.p. non-MF headline over slimmed data;
   Phase B (descoped) = simultaneously-nonsofic witness (needs a
   torsion-free f.p. non-LEF group — Burger–Mozes-sized, out of scope).
5. **The partner can never come from the router itself**: C'(1/6)
   groups are cubulated (Wise) hence a-T-menable; infinite ones are
   never (T).  G2 is irreducibly external to G1/G3.

## Workstreams

W0 (wave 0, dispatched): interface slimming + source wiring.
  Additive only — new files + adapters; never edit the complete frozen
  lane; never add requires to a complete cairn route.
  a. Trace consumers of `core.kazhdan` and the simplicity field through
     `TorsionFreeFullMFRadical.lean` → `FullMFRadicalEndpoint.lean`.
  b. Slimmed structure (working name `BareDefectSourceData`): core sans
     Γ-(T), sans simple subgroup; keystone
     `RoutingLemmaData → slimmed DefectRoutingData-analogue → endpoint`
     re-derived with (T) of Q from `hB` alone.  New parallel endpoint if
     needed; keep the old one untouched.
  c. Degeneracy lemma for `OrderPreservingRoutingData` (fact 1).
  d. Wire `integerSource` to a certified torsion-free source via
     `HNNTorsionFree` (stale docstring suggests this is undone).
  Exit: slimmed chain builds green on MSI; consumer trace documented.

W1 (critical path, math-first): `GreendlingerGate`, n ≥ 3.
  State: two-factor case closed; `GreendlingerTwoPiece` REFUTED
  (witness in-repo); residuals `PieceOverlapRight`
  (GreendlingerDehnCritical.lean:590, mirror + gate assembly proved),
  `CascadeLanding` (GreendlingerCascade.lean:245, assembly proved),
  max-conjugator frame (arithmetic proved; junction reading unwritten;
  `MaximalJunction` as literally defined is nearly vacuous — the content
  is the nested-matching reading; NO assembly theorem yet).
  Plan: coordinator derives the correct inductive strengthening (the
  classical Greendlinger boundary-layer count adapted to the in-repo
  refutation witness), writes the full paper proof, then Opus agents
  formalize against whichever residual it lands on (expected:
  PieceOverlapRight route).  Then the relative CoprodI transfer
  (`MetricSmallCancellation → GreendlingerLengthBound ∧
  TorsionIntoFactors`), which is mechanical re-plumbing over syllables
  IF the free case closes by the certificate method.
  Fragment caveat, CORRECTED 2026-08-21 (the first version had the
  direction backwards; two independent witnesses confirmed): in-repo
  whole-syllable pieces are FEWER than classical fragment pieces, so
  whole-syllable C'(λ) is a WEAKER hypothesis — it yields only classical
  C'(λ + 1/|r|), and no relator length rescues λ = 1/6.  The relative
  lane therefore carries the explicit FragmentSlack condition
  (λ·wlen r + 1 ≤ (1/6)·wlen r; e.g. C'(1/7) at ≥ 42 syllables) — see
  GreendlingerRelativeTransfer.lean.  The FREE-GROUP lane is unaffected
  (no fragments in a free-group alphabet; C'(1/6) honest), which is one
  more reason the avatar router presents over a free group.

W2: partner `B` — torsion-free, f.p., (T), unconditional.
  Chosen route: B = Γ(3) = ker(SL₃(ℤ) → SL₃(ℤ/3)).
  a. (T) for SL₃(ℤ): SOS certificate replayed through
     `ExactHodgeCertificate` on concrete integer matrices (ball products
     are matrix multiplications; decide-friendly; kernel-timeout lessons
     from the P13 Hodge lane apply).  Certificate data: ingest published
     exact certificates (Netzer–Thom / Kaluba–Nowak–Ozawa lineage) or
     SDP-solve + rationalize on MSI.  Data, not premise: zero
     laundering.  Prerequisite: elementary generation of SL₃(ℤ)
     (Gauss/Euclid induction — hard-but-standard).
  b. Torsion-freeness of Γ(3): Minkowski.  Elementary; the graded
     3-adic-valuation proof; Lean-tractable now.
  c. (T) for Γ(3): finite-index permanence — already PROVED.
  d. f.p. for Γ(3): the ONE research-grade atom, two halves:
     (i) f.p. of SL₃(ℤ) — RE-ATTRIBUTED 2026-08-21 after source
         verification: **Milnor AM-72 §10, Thm 10.1 + Cor 10.3** (via
         Silvester's Lemma 10.6 seven-case descent and Lemma 10.7;
         Nielsen–Magnus lineage).  NOT van der Kallen — he computes
         H₂(SL₃ℤ) = ℤ/2 ⊕ ℤ/2, a strictly larger, different invariant;
         conflating them would be an error.  Citation-hygiene note: old
         literature (Steinberg's Yale notes; Soulé 2.7; Bekka–de la
         Harpe Ex. IV) wrongly identifies St₃ℤ with the universal
         central extension — see Bárcenas–Velásquez arXiv:1311.5415
         Rmk 5.3.  IN REPO TERMS the atom is `Function.Injective toSL3`
         on the EXISTING P13 presentation (which IS Milnor's Cor 10.3:
         12 Steinberg relators + the fourth-power relator
         (e₁₂e₂₁⁻¹e₁₂)⁴); surjectivity is already proved, and
         `P13ParabolicKernel` (proved) plus the repo's Euclid-measure
         organization (see memory milnor-s10-crosscheck) cover part of
         the endgame.  This same atom is the sofic-side completeness
         blocker — closing it serves both manuscripts.
     (ii) f.p. descends to finite index — DOWNGRADED to ~2 lemmas:
         Mathlib now has Nielsen–Schreier + Schreier +
         IsFinitelyPresented with surjection/iso closure; missing only
         (A) f.g. free ⟹ finitely many Generators, and (B) the
         Hartung-style finite-transversal relator decomposition giving
         IsFinitelyNormallyGenerated (the Schreier condition is needed
         only for the free basis, never for the redundancy step; τ need
         not be formalized).
  Source-verification duty before any Lean work on (d)(i): pin the
  exact unstable statement and proof line in van der Kallen / Milnor
  §10 / literature, per the repo's quarantine doctrine (paper cites,
  Lean proves — the Lean proof re-derives; the citation is credit).

W3: router construction over E * B (after W1; design can start now).
  Choose h₁, h₂ and the protected s inside the defect using the
  `ExplicitSuitableDefect` free basis; Rips-style interleaved aperiodic
  relator family expressing each generator of E and B as a long word in
  defect conjugates; verify whole-syllable C'(1/6) BY DESIGN (blocks
  long, ranges disjoint, no proper-power relators); derive
  `defect_top`, `generates`, `partner_surjective`, f.p. (finitely many
  relators), torsion-freeness via `TorsionIntoFactors` + torsion-free
  factors.  Coordinator supplies the explicit word family and the
  piece-bound ledger; Opus agents formalize.

W4: assembly.  Instantiate slimmed source data (W0d) + router output
  (W3) + partner (W2) ⟹ slimmed `DefectRoutingData` ⟹ endpoint.
  State the final theorem in the ∃-form with `IsPowerTorsionFree` and
  bridge `IsMulTorsionFree` once.

W6 §4 APPARATUS TRAP (2026-08-21 night, caught by closures-1, confirmed
  by lit at source): Higman's §4 closure proofs (4.4–4.10, all but
  ι/υ) live in ⟨a,d,e⟩ and presuppose the d/e apparatus (Lemmas
  4.1–4.3, incl. the weight-vector property 4.2); the repo's coding is
  F₃-native with ASCENDING-sorted products, so ρ (order-reversing) and
  τ (exponent-swap, not letter-swap) are NOT automorphism clones of
  the σ shortcut — that shortcut works only because σ preserves order.
  Continue the F₃-native per-operation route (FlipWitness; τ via a
  witness-overgroup automorphism per Mikaelian §4); see
  HIGMAN_EMBEDDING_FORMALIZATION_PLAN.md §9.  θ needs no image-closure
  lemma (oddZero = ω₂(ζZ), closures-2); the shared lemma blocks ρ/τ.

W6 TRANSCRIPTION TRAPS (from the source pin; full detail in the
  program memory and the Higman memo): Lemma 2.8 is false as printed
  for X = ∅ (cite with the explicit hypothesis); σ³ζσ in the
  W-construction is DELIBERATE (ζ punches the single parity hole — do
  not "simplify" to σ⁴); the a(r) < 0 < b(r) step needs the widened
  window at h(r) = 0; p.464's local E clashes with the sequence space.

W6 (added 2026-08-21 after the W0 trace): the SOURCE BASE — a
  property-(T) group with proper self-embedding, centralizing root and
  nontrivial marked commutator inside a torsion-free f.p. ambient.
  `integerSource` is a shape voucher only (amenable base ⟹ endpoint
  unreachable).  Candidate routes, to be sized by a dedicated survey:
  (a) FF's universal-group construction: Chiodo absorber (countable
      form PROVED in-repo) + TorsionFreeHigmanHull (the
      torsion-order-preserving Higman embedding of one named countable
      group — OPEN) + Osin envelope inhabitation (interface-only).
      Leverage check: the in-repo Novikov–Boone / Post–Markov /
      S-machine corpus was built for exactly Higman-type machinery —
      the embedding may be far cheaper here than in a vacuum.
  (b) Non-f.p. bases (e.g. congruence `EL₃(ℤ[x])`, (T) by
      Ershov–Jaikin or by a new SOS certificate, torsion-free by graded
      Minkowski, non-co-Hopfian by substitution) require realizing a
      homomorphic image inside a f.p. ambient — again Higman-shaped;
      only worth it if (a)'s S-machine leverage materializes anyway.
  (c) A replacement analytic mechanism not reading base-(T): no known
      candidate (the torsion-critical branches are excluded here);
      treat as closed unless new math appears.

W5: gates + landing.  Audit roster (four gates, real transitive
  closure); orphan gate — root imports land in the SAME push as new
  modules; signatures regenerated before commit; badges/claim-strength
  rows; manuscript CLAIM_TARGETS when promoted; cairn node updates
  (close `bespoke-routing-lemma`,
  `small-cancellation-router-spec-proof` checked half already,
  `greendlinger-free-product-lemma`,
  `torsion-free-non-mf-from-bespoke-router`; new nodes for the partner
  atom and the K₂ atom; fix the J-convention drift in
  `fournier-facio-torsion-free-skeleton`); FRONTIER regen on MSI with
  locks synced; prover CI green; verified promotion.  Phase B
  (nonsofic simultaneous witness) explicitly descoped as its own node.

## Dependency graph

  W0 ──▶ W3(design now, formalize after W1) ──▶ W4 ──▶ W5
  W1 ──▶ W3 formalization; W1-relative ──▶ torsion clause of W3
  W2 ──────────────────────────────────▶ W4   (independent mountain)

Critical path: max(W1, W2).  W1 is combinatorics with three prepared
attack routes; W2(d)(i) is a long self-contained symbol calculus.

## Ops protocol (binding on every worker)

- Builds MSI-only (`scripts/remote-build.sh`); lock-free
  `lake env lean` probes on cores 8-11 with LEAN_NUM_THREADS=4;
  named-target `lake build` under the fleet mutex; sentinel echo on
  every command whose emptiness is the signal; pin a node; kill your
  own strays; never cancel prover CI runs.
- Shared tree: explicit-pathspec commits only; `git add -p` on shared
  files (root `GroupApproximation.lean` especially); re-read files
  after writing (style normalizer); never build from `cp -al` clones
  without touching sources.
- `-DwarningAsError=true`: unused simp args are fatal; `push Not`;
  `omit`/`include` go before the docstring; instance binders must be
  referenced or renamed `_inst`.
- Never: worktrees (local), reset, amend, revert, stash, branches.
  Recover forward.  Heredoc commit messages.
- Authoring without a compiler: grep for `sorry` is insufficient —
  elaborate every new file on MSI before claiming green.

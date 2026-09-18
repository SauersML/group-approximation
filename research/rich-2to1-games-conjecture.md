---
rg: 2
id: rich-2to1-games-conjecture
kind: claim
title: Rich 2-to-1 games are NP-hard to approximate between near-perfect and near-zero value
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
  - research/artifacts/unique-games-noisy-direction-counterexample-2026-09-07.md
  - research/artifacts/unique-games-affine-test-soundness-2026-09-07.md
---

**OPEN.**  The Rich 2-to-1 Games Conjecture of Braverman, Khot and Minzer:
the near-1 versus near-0 hardness gap holds for 2-to-1 games carrying the
additional *richness* condition: at each left vertex, a uniformly sampled
incident edge induces a uniformly random perfect pairing of the left
alphabet. This is Definition 5 of the cited ITCS paper.

By `rich-2to1-conjecture-is-equivalent-to-ugc` this is not a weakening of
`unique-games-conjecture` but an exact reformulation of it.  Its interest is
that it is stated on instances of the shape the existing 2-to-1 machinery
already builds, so the whole difficulty is concentrated in supplying
richness rather than in redesigning the reduction.

The known `F_lin` family pairs `x` with `x+b` on `F_2^k` for a uniform
nonzero `b`. It is much smaller than the family of all perfect pairings.
The proposed alphabet-independent list-decoding lemma for this family was
refuted on 2026-09-07 by `noisy-affine-selector-defeats-bounded-hitting`.
Consequently that proposed bridge does not supply the missing richness.

Full uniformity is more than the reduction needs.
`noise-test-sound-on-smooth-design-rich-inputs` shows the published soundness
proof uses only a strength-`(8d+1)` pairing design with the pull-back density
comparison. That weaker hypothesis is `smooth-design-rich-2to1-hardness`, which
feeds UGC through `ugc-from-smooth-design-rich-2to1`.

`dummy-padding-cannot-beat-the-random-guessing-floor` explains why an
alphabet-sized decoding list cannot supply the intended soundness gain.

## Attempts

* **Use the folded long-code noise test with only affine richness.**
  **Dead as a uniform soundness argument:**
  `affine-long-code-test-has-no-uniform-soundness` gives explicit source
  games of value at most `2/sqrt(N)` whose transformed games have value
  close to one. The published result's full-richness hypothesis is not
  supplied by the affine direction distribution. This leaves open tests
  or input families with additional structure.
* **Stop at an intermediate algebraic family.** **Dead for the noise test:**
  `separated-small-pairing-families-defeat-the-noise-test` extends the affine
  obstruction to every separated pairing family of subexponential size, e.g.
  affine or bounded-degree polynomial involutions. Route
  `ugc-via-subexponential-pairing-enrichment` records the kill. The pairing
  distribution at a left vertex must carry entropy linear in the alphabet size
  before this test applies.
* **Glue the affine orientations analytically.** **Dead:**
  `affine-orientation-glue-lemma` is refuted, and its conditional hardness
  route is invalidated. The historical endgame proposal
  `glue-lemma-implies-rich-2to1-hardness` never supplied an explicit reduction.
* **Randomize the fibers by conjugating each constraint.**  **Dead** --
  `edge-conjugation-of-2to1-constraints-is-pure-gauge` shows the folded
  long-code restriction is literally unchanged, so no randomness reaches
  the analytic object the test sees.
* **Orient each 2-to-1 fiber with local unique-constraint gadgets.**
  **Dead** -- `unique-constraints-orient-at-most-half-of-a-fiber`.
* **Hide a hard core inside a large randomly matched dummy alphabet.**
  **Dead** -- `dummy-padding-cannot-beat-the-random-guessing-floor`.
* **Prove soundness by an operator-algebraic (entanglement-robust) analysis.**
  Examples: matrix-valued hypercontractivity, quantum rigidity or low-degree
  tests as the soundness engine, or an inner decoder that handles entangled
  strategies. **Attempted, held OPEN (2026-09-17):** the kill below was drafted but
  referees refuted it as written. Lens 1: B3 omits the outer completeness and
  polynomial-time hypotheses on `O` that its proof uses. Lens 2: KRT Theorems 1.3
  and 4.5 apply to unique games only, so an entanglement-sound outer PCP to rich
  2-to-1 games followed by the classically sound noise test is not killed; the
  kill can at most cover soundness conclusions about the output unique game.
  The drafted content:
  - `entanglement-sound-soundness-cannot-prove-ugc` (via the Kempe--Regev--Toner
    import `unique-games-entangled-value-approximable-by-sdp`) shows such an
    analysis puts the source language in P when `6 eps + delta < 1`.
  - Under P != NP, every NP-hardness reduction to Gap-UG must produce infinitely
    many NO instances of entangled value `>= 1 - 6 eps`.
  - Composition with a classically sound outer PCP and an entangled-strategy
    decoder `D_cl`, or with an entanglement-sound outer PCP and a decoder `D_q`,
    also dies.
  - Unconditionally, for the binary test,
    `clifford-long-codes-realize-pairing-value-in-binary-noise-test`
    gives fully rich 2-to-1 games of value `<= 4/k^eta` whose `R_(rho,2)` output
    has entangled value `>= (1 + rho^3 (1 - 9 eta)^2)/2`.

  (Drafted conclusion, not established: a proof of this conjecture whose soundness
  conclusion is about the output unique game must use a step that is false for
  entangled strategies.) Open: an explicit clock-and-shift witness for `m > 2`.
* **Keep the left labels of a proved 2-to-1 instance and add locally complete
  right vertices until the matchings are rich.** This covers right compression,
  merging, auxiliary right vertices, and refining Grassmann-shaped instances.
  **Dead (2026-09-17)** -- route
  `rich-2to1-via-left-preserving-local-wrappers`, killed by
  `left-preserving-local-richness-wrappers-are-affine-ug-merges`.
  - Local completeness over affine intended classes `A_z` makes every constraint
    at `z` absorb the agreement subgroup `B_z = sum ker dr_(uz)`.
  - So `z` is either all `F_lin` translations or a right merge of an affine
    unique-game clique.
  - Pair-uniformity leaves translations at most `alpha_k ~ 1/k` of the mass.
  - Hence `val(W(G)) >= (1 - alpha_k) val(U_W(G))`. With certified completeness,
    `G -> U_W(G)` is already UG hardness.
  - Open survivors: re-encoded left labels, completeness without local
    certificates, non-affine intended classes, partial richness.
* **Run the known rich-producing constructions with perfect completeness, aiming
  at BKM Conjecture 7, which implies this claim.** The constructions are right
  merges `Psi(U)`, certified affine-local wrappers and an affine `F_lin`-stage
  start of the `F_j` chain.
  **Dead (2026-09-17)** -- route
  `rich-2to1-perfect-completeness-via-tractable-skeletons` toward the new OPEN
  node `rich-2to1-perfect-completeness-conjecture`. That node feeds here through
  `rich-2to1-from-perfect-completeness`. The route is killed by
  `perfect-completeness-rich-2to1-tractable-skeletons-are-in-p`.
  - Invariant: the tractable skeleton mass, meaning a sub-instance computable
    from the reduction's run that is a constant-seed forcing closure, a unique
    game or an affine system.
  - Step: completeness. A satisfiable game has satisfiable skeletons, skeleton
    search is polynomial, and soundness caps the value at `delta` below the
    skeleton mass.
  - `Psi_Sigma(U)` is satisfiable iff `U` is, and one seed forces a component.
    Certified wrappers make `U_W(G)` satisfiable.
  - The Grassmann skeleton has closure mass `0.0015` at `n = 6`, but Gaussian
    elimination solves it (brute-force artifact).
  - The kill is silent at completeness `1 - eps`, so it does not touch this
    claim's own hardness. It shows that Conjecture 7 needs P1, a re-encoding
    reduction with `o(1)` closure and no unique-game or affine skeleton.
  - Open spark: are the GKOPTW perfect-SDP 2-to-1 gap instances (ICALP 2010)
    rich, or can they be made rich without a merge skeleton?
* **Close the orientation-lift completeness hole with an efficient branch
  selector whose completeness witness is the honest encoding.** In the
  orientation-lift decomposition posted on the live bus, richness and soundness
  are free and one completeness hole remains: an efficient selector on proved
  2-to-2 or 2-to-1 instances with lift completeness `1 - eta'`. That
  decomposition has not landed in this graph. **Dead unless NP in RP
  (2026-09-18)** -- `efficient-branch-selectors-list-decode-honest-outer-labels`.
  - Scope: any randomized polynomial-time selector, view-local, parity-leaking
    or global, on a linearly encoded composition satisfying (B), (E) and (M).
    The selector must give the honest encoding of some outer labelling of value
    `>= 1 - eps` a lift value `>= 1/2 + gamma`. Then a decoder finds outer
    labellings of value `>= (gamma^3 2^(-l-2)/K)^2 - 2 eps`. So when the outer
    soundness is below half of that, the source is in RP.
  - Invariant: branch-bit advantage.
  - Step: guess one seed label. The branch bits then predict `<lambda_a, x>`,
    Parseval gives a list of `4/gamma^2`, and random list decoding beats the
    outer soundness.
  - Tight: under `P = NP` honest selectors reach `val_G(hon(lambda))`, so no
    unconditional kill exists.
  - Survivor: completeness witnesses far from every honest encoding, the
    non-honest heretic H2.
  - Not established here: that the Khot--Minzer--Safra 2-to-2 instances satisfy
    (E) and (M). The claim node gives the argument.
* **Make the honest-witness selector kill apply to the proved DKKMS 2-to-1
  instances themselves.** **Done for 2-to-1, and ESTABLISHED:**
  `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`
  (swarm-0917-w6-w6-re-pull2-unique-1, 2026-09-17). This answers live need
  `1cb0e45a` for the 2-to-1 instances, checked against ECCC TR16-198.
  - Membership, with each hypothesis read off Section 4.2:
    - (E) holds with `tau = 2^(l-1-2k)`. The new direction is uniform off
      `L' + H_U`, not off an `(l-1)`-space, so the parent's `2^(l-1-3k)` was
      wrong.
    - (M) holds with `K = 1`. Validity conditioning leaves the U-marginal
      uniform.
    - (B) holds up to the dirty-tuple mass `eps_out <= k eps_3`, because folding
      unfolds `a|_R` to `a|_L` on clean tuples.
    - Folded aggregated constraints embed into the multi-edge game with at least
      the same lift values.
  - Outer soundness is Lemma 5.4 of the paper, applied to players who ignore
    `Q`. Inner soundness and Hypothesis 3.6 are not used.
  - Corollary, under `NP not in RP`: no polynomial-time selector on these
    instances lifts an honest encoding `a|_R` of a good 3LIN assignment to value
    `>= 1/2 + gamma`. The same holds for any lift labelling within mass
    `gamma/4` of such an encoding.
  - Survivor: H2 witnesses, far from every honest encoding on the *clean* mass.
    Different labels on dirty tuples are absorbed by the corollary.
  - Still unchecked: membership of the KMS 2-to-2 instances.

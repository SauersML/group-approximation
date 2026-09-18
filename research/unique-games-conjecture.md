---
rg: 2
id: unique-games-conjecture
kind: claim
title: For every eps > 0 there is an alphabet size making it NP-hard to tell unique games of value >= 1-eps from value <= eps
root: true
goal: true
artifacts:
  - research/artifacts/unique-games-finite-density-moments-2026-09-12.md
  - research/artifacts/unique-games-smooth-design-richness-2026-09-11.md
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
  - research/artifacts/approximation-cs-root-audit-2026-08-31.md
  - research/artifacts/unique-games-noisy-direction-counterexample-2026-09-07.md
  - research/artifacts/unique-games-affine-test-soundness-2026-09-07.md
  - research/artifacts/ugc-state-of-the-art-2026-09-12.md
  - research/artifacts/ugc-galois-games-2026-09-12.md
  - experiments/grassmann-can-holonomy-2026-09-17/can_holonomy.py
  - experiments/grassmann-can-holonomy-2026-09-17/output.txt
---

**OPEN.** Khot's Unique Games Conjecture: for every `0 < eps < 1/2` there is an
alphabet size `K = K(eps)` such that, given a two-prover one-round game
whose every constraint is a permutation of a `K`-letter alphabet, it is
NP-hard to distinguish

```text
val(G) >= 1 - eps     from     val(G) <= eps.
```

The gap is *near-1 versus near-0*.  What is known unconditionally is the
2-to-2 Games Theorem, which reaches completeness near `1/2` with
arbitrarily small soundness; the near-1 side is exactly what is missing.

This is a **root** of the graph in its own right, not a lane under the
program goal `non-hyperlinear-group`.  It was opened 2026-08-24 by a user
directive to wire in an external attack on the conjecture, and it shares
vocabulary but no derivation with the repository's operator-algebraic
games region.  The one place the two regions touch is
`perfect-commuting-unique-game-is-classically-satisfiable`, which says a
*perfect* commuting-operator strategy for a unique game already yields a
perfect classical labeling; that rigidity is the mechanism behind
`unique-constraints-orient-at-most-half-of-a-fiber` below, and it is why no
quantum relaxation of the unique-constraint alphabet evades the wall.

The published equivalence route here goes through
`rich-2to1-games-conjecture`, which is *equivalent* to this claim by
Braverman--Khot--Minzer. The proposed `F_lin` attack was closed on
2026-09-07: `noisy-affine-selector-defeats-bounded-hitting` refutes both
`affine-orientation-glue-lemma` and its proposed star-density input.
The conditional globalization theorem remains valid. The prior two-hole
plan is no longer usable; the smooth-design formulation below replaces its
analytic input but still needs an explicit hardness reduction. Neither UGC
nor Rich 2-to-1 hardness
is proved or refuted by that counterexample.

**Current outer-hardness frontier (September 12, 2026).** The live route
`ugc-from-smooth-design-rich-2to1` combines the established analytic transfer
`noise-test-sound-on-smooth-design-rich-inputs` with the OPEN hardness claim
`smooth-design-rich-2to1-hardness`. Its hypothesis fixes the test alphabet and
balance parameter before selecting a smooth pairing design; it does not ask
one small family to work for all test alphabets simultaneously. The available
weighted design construction proves existence of admissible distributions,
not NP-hardness of games with those distributions. The reverse route
`smooth-design-rich-2to1-from-ugc` proves that this outer-hardness assertion
is itself equivalent to UGC. Neither direction supplies the missing hardness
input. The refuted affine test remains invalid and the root remains OPEN.

The further route `ugc-from-finite-moment-pairing-hardness` replaces
pointwise density domination by one finite density moment after the fixed
noise already present in the reduction. Its proved input
`finite-density-moments-control-noisy-tails` gives a dimension-independent
tail bound. The new OPEN hardness premise keeps the moment constant
independent of the source error and design strength; these quantifiers
allow the noise, moment order, constant, and degree cutoff to be chosen
without circularity. The matching-union formula makes the moment condition
an exact combinatorial overlap bound. No hard outer construction satisfying
it is supplied, and the exponential pairing-support obstruction persists.

## Attempts

- **NO-side spectral kill by the degree-2 SDP (swarm-0917-w5, 2026-09-17).**
  `spectral-gap-no-outputs-cannot-prove-ugc` proves, at every alphabet and
  without triangle inequalities, the bound
  `val >= 1 - 768 eps/gamma - 14 eps - 18 r^(2/3) eps^(1/3)` for SDP deficit
  `eps` and at most `r` constraint-walk eigenvalues above `1 - gamma`.
  - *Method:* fourth-tensor embedding, projection onto the top eigenspaces, a
    random grid, and root propagation through the `>1/2` matchings.
  - *Consequence:* a reduction to `Gap-UG[1 - eps0, delta]` implies `P = NP`
    whenever its NO outputs have fewer than
    `(1-delta)^(3/2)/(216 sqrt(2 eps0))` eigenvalues above
    `1 - 3072 eps0/(1 - delta - 56 eps0)`.
  - *Combined with the YES-side kill:* with
    `low-label-threshold-rank-reductions-cannot-prove-ugc`, a UGC reduction
    needs high threshold rank on both sides.
  - *Survivors:* long-code and noisy-cube compositions, and SSE graphs with
    many near-1 eigenvalues.
  - *Open follow-up:* raise `r` beyond `eps^(-1/2)` in polynomial time. That
    needs a rounding whose cut cost does not scale with the grid dimension.

- **Door P1 of the affine-view collapse, closed for the DKKMS family
  (swarm-0917-w4, 2026-09-17).** `grassmann-composed-2to2-coarsenings-are-satisfiable`:
  on every folded Dinur--Khot--Kindler--Minzer--Safra instance, and for every
  agreement test on its vertex set, the coarsening `Can` has value 1, satisfied
  by one gauge labelling. The labelling exists because folding offsets are
  coboundaries against Lemma 4.1 representatives. So every affine-view unique
  verifier composed on the 2-to-2 instances has `s >= 2c - 1`. Only these routes
  survive:
  - non-affine views (P2, `Can_part`);
  - outer games whose constraints link two subspaces of one label space;
  - verifiers without oblivious completeness.

* **Direct affine soundness of the published folded noise test.**
  `affine-long-code-test-has-no-uniform-soundness` supplies an explicit
  source family with vanishing value and folded output labelings with
  high acceptance. The complete proof includes all three noise layers,
  a finite-field incidence bound, and the conversion to permutation
  constraints. It closes this test under only `F_lin` richness; it is
  neither a UGC proof nor a UGC counterexample.
* **Structured 2-to-1 instances.**  Attack the equivalent Rich 2-to-1
  formulation on the `F_lin` instances whose fibers are affine pairs
  `{x, x+b}` -- the instances the presently known hardness machinery
  already produces. The published equivalence remains a live route
  (`ugc-from-rich-2to1-via-bkm-equivalence`), but the repository's proposed
  alphabet-independent list lemma is false. Richness is a distributional
  condition on pairings, not a synonym for that lemma.
* **Noisy direction decoding.** A complete counterexample to the proposed
  analytic bridge is recorded in
  `noisy-affine-selector-defeats-bounded-hitting`, with exact finite replay.
  The adversarial function is Boolean and folded and survives every fixed
  positive noise parameter. Those conditions alone cannot repair the bridge.
* **Naive influence transfer.**  Hope that a coordinate with large
  influence after restriction to an affine-pair subcube has large ambient
  influence, so that the ambient influential coordinates form the bounded
  label list.  **Dead**: `linear-pairing-memorizer-restricts-to-a-dictator`
  exhibits a bounded homogeneous function whose noisy restriction stays a
  fixed multiple of a dictator while every ambient influence tends to 0.
* **Manufacturing richness by randomizing constraints.**  **Dead**:
  `edge-conjugation-of-2to1-constraints-is-pure-gauge`.
* **Padding the alphabet with random dummy labels.**  **Dead**:
  `dummy-padding-cannot-beat-the-random-guessing-floor` -- an alphabet-sized
  decoding list only reproduces the game's own random-assignment value.
* **Symmetric quotient (Galois) gap instances.** A unique game whose lift is
  a Cayley graph with coset fibres, the Khot--Vishnoi type, is described
  exactly by `galois-unique-game-value-is-transversal-expansion`. Over
  `F_p^N`, `elementary-abelian-galois-games-round-with-linear-loss` rounds any
  SDP value `1-eps` to a subgroup complement of value `1 - O_p(eps log k)`,
  tight on Khot--Vishnoi. Such constructions are gaps only when
  `eps log k -> infinity`, and the exponent hypothesis is needed (cyclic
  quotients lose `sqrt(eps)`). This is structure for integrality-gap and
  dictatorship-test design, not a route in either direction.
* **Affine-view unique verifiers over 2-to-2 inputs.** This covers Hadamard,
  Grassmann and subspace encodings read as unique tests. **Class-killing
  obstruction and equivalence**:
  `linear-view-unique-verifiers-collapse-to-quotient-coarsening`. The set of
  inputs on which two affine views agree is a subspace. So above completeness
  `1/p`, weight at least `(pc-1)/(p-1)` sits on exact triples, and the output
  value is at least that weight times the value of a test-free, branch-blind
  quotient coarsening `Can` of the outer game. Any such proof of near-1 UG
  hardness is therefore a proof that `Can` is hard. No Grassmann expansion
  theorem can enter, and crossing the `1/2` wall needs views that are not
  affine in the outer label. Open: is `Can` of hard 2-to-2 instances hard?
  *Dead end (sw-034, decisive computation):* "restriction coarsenings are
  trivially satisfiable, so every affine-view verifier over folded 3LIN-derived
  inputs is capped at `s >= 2c - 1`". The cap would be tight: mixing the split
  (`c = 1/2`, `s ~ 0`) with trivial exact tests attains `s ~ 2c - 1`. It dies at
  folding. Without right-hand sides, `Can` has only identity constraints and
  value 1. With folding `f_u(s + e_u) = f_u(s) + b_u`, a chain of exact triples
  can shift a point by equation vectors. Around a cycle, `Can` then reads the RHS
  parity of an equation multiset summing to 0: the Hadamard restriction encoding
  of an odd 3LIN dependency. For the maximal one-bit restriction verifier
  (`experiments/grassmann-can-holonomy-2026-09-17/can_holonomy.py`):
  * no consistent instance has a parity conflict;
  * almost every inconsistent instance does (1388 of 1404 over n = 6..20);
  * every conflict is certified as an odd dependency.
  With one-variable overlaps `Can` is a matching of value 1. This rules out
  proving the cap from `Can` structure alone. `Can` on these inputs is a genuine
  Max-2Lin system over the RHS. So the open question is a gap question, whether
  that Hadamard restriction system is hard at soundness near 0, not a
  triviality. The toy has label dimension 1, not the KMS parameters.
* **Bounded-degree views (Reed--Muller, short-code, quadratic encodings).**
  **Candidate class-killing obstruction**: `low-degree-view-unique-verifiers-collapse`
  (OPEN after refereeing on 2026-09-17). Its formal items hold, but the class it
  kills is established only when the permutations `sigma` are affine. A
  non-affine `sigma` (for instance a transposition) makes soft triples of degree
  about `log_p(1/eps)` even for Grassmann views. The proposed repair
  `low-degree-view-collapse-survives-non-affine-sigma` is **refuted** by
  `non-affine-sigma-deletions-defeat-low-degree-collapse` (2026-09-17). With
  identity views, swapping two labels per edge keeps completeness `1 - 2^(1-k)` but
  drops the value from 1 (the coarsening's value) to `o(1)`. With arbitrary `sigma`,
  affine-view verifiers collapse only to the **deletion coarsening** `Can_del`:
  roundable triples (equal kernels, forced above completeness `1/p`) with sparse
  deleted label sets of average density at most `(1-c)/w_r`, and
  `val(V) >= w_r val(Can_del)`. The deletions are harmless when the homogeneous
  symmetries of the outer game surject onto the view quotients. They are not harmless
  for folded, over-determined inputs. So the soft triples of (P2) already occur
  over degree-1 views, where the degree lives in `sigma`, not in the encoding. Open: is `Can_del` of hard 2-to-2 families sound, with deletions of
  density `O(eps)` aimed at concentrated labellings?
  The invariant is the algebraic degree `D` of the view differences on the outer
  constraint spaces. A nonzero reduced polynomial of degree `D` is nonzero on a
  `p^-D` fraction of points. So at completeness `1 - eps`, the exact triples
  weigh at least `1 - eps p^D`. Exact triples induce bijections between
  level-set partitions, and the output value is at least `w_ex` times the value
  of the test-free, branch-blind partition coarsening `Can_part`. Every verifier
  with `eps p^D -> 0` dies at this step, whatever expansion its encoding has.
  **Remaining gap** for a composition proof over a linear outer game (such as the
  2-to-2 instances) reaching completeness `1 - eps`, for affine `sigma`. P1 and P2
  are alternatives (exact weight near 1 versus `Omega(1)` soft weight), and P3
  applies only to proofs that use the long-code noise test:
  1. **(P1) coarsening hardness.** Some branch-blind partition coarsening
     `Can_part` of hard 2-to-2 families is itself hard at `1 - o(1)` versus
     `o(1)`. This is the only door open to views of degree
     `< (1 - gamma) log_p(1/eps)`.
  2. **(P2) high-degree soft triples.** Otherwise, `Omega(1)` weight sits on
     non-exact triples that reject honest labels with probability `O(eps)`. By
     the density lemma these have degree `>= log_p(1/eps) - O(1)`, which is the
     long-code regime. Their soundness must be proved in the 99% regime; the
     imperfect-completeness 2-to-2 machinery works at completeness about `1/2`,
     and no 99%-regime version of it is recorded here.
  3. **(P3) no learnable collapse.** For the long-code noise test, the derived
     unique game must have vanishing value on the learnable families of
     `bkm-test-transparent-on-learnable-games`.

  Perfect completeness is out in this form
  (`unique-constraints-orient-at-most-half-of-a-fiber`, and UG with perfect
  completeness is in P). So every prerequisite is stated at `1 - eps`.
* **Real linear equations and the real code (Khot--Moshkovitz candidate, weak
  UGC) (swarm-0917-w5, 2026-09-17).** This route is independent of 2-to-2. It
  decomposes into four prerequisites:
  - (P-a) hardness of random `kCSP(PHLin)` and the `kLin(R)` Lasserre gap;
  - (P-b) completeness of the real code `interval(<sigma, x>)`;
  - (P-c) KM Theorem 14, soundness for `(l, gamma)`-list decoding strategies;
  - (P-d) near-complete folded strategies are list decodable.

  **(P-d) is refuted** by `distorted-periodic-half-spaces-defeat-real-code-junta-decoding`.
  The distorted codes `interval(sum_i sigma_i phi_a(x_i))`, with
  `phi_a(t) = t + (a/2pi) sin 2pi t`, are folded and reject all three KM tests
  within their completeness bounds. Yet they correlate at most `eta` with every
  junta of `l` real code functions once `n >= n_0(a, l, eta)`.
  - *Invariant:* the per-coordinate Fourier contraction `lambda_K(a) < 1`.
  - *Where it dies:* the list-decoding step of Theorem 14.

  This answers KM's Robust Gaussian Isoperimetry question negatively in junta
  form. What survives is a reparametrization-invariant structure theorem
  (decode the labels `sigma_i`, not the functions) together with soundness for it:
  (P-d') and (P-c'), both OPEN.
* **Refuting the conjecture.** The algorithmic negation is the open claim
  `unique-games-gap-admits-polynomial-time-algorithm`. Its Attempts record the
  algorithmic frontier: `affine-ug-easy-on-certifiably-hypercontractive-graphs`,
  `affine-ug-easy-on-globally-hypercontractive-graphs`, threshold rank, and
  symmetric quotients. A refutation would land as that negation established,
  not as a route.
* **Mainstream frontier.** The unconditional gap stands at completeness `1/2`
  (`two-to-two-games-theorem`, `unique-games-hard-at-completeness-one-half`). A
  second, one-way route into this root is `ugc-from-small-set-expansion-hypothesis`.
* **Fixed-exponent reductions: a size gate under ETH (class kill, 2026-09-18,
  wave 6).** `ugc-hardness-reductions-need-epsilon-dependent-size-exponent`
  (ESTABLISHED as a conditional theorem) imports ABS
  (`abs-subexponential-unique-games-and-sse-algorithms`).
  - *What it proves.* Assume ETH. A 3SAT reduction with output size `n^A` has:
    - `A >= c gamma^(-1/6)` for Gap-UG at completeness `1 - gamma` vs `1/2`;
    - `A >= c eps^(-1/6)` for every 2-to-1 hardness that the BKM noise test
      certifies at `eps`. The test has size `|E|^2 m^(6l)`. This covers
      Gap-Rich at `1 - eta` and at `1`, and the smooth-design and finite-moment
      holes, so it applies to all four BKM-test routes;
    - `A >= c/eta` for SSE on regular graphs, repaired to exact measure
      `delta`.
  - *Invariant.* The size exponent.
  - *Where it dies.* At decoding: `exp(k N^(O(eps)))` time on the output
    is `2^(o(n))`.
  - *Survivors.* Exponents growing as `eps^(-Omega(1))`, such as parallel
    repetition whose number of rounds tends to infinity; failure of ETH;
    irregular SSE outputs; completeness bounded away from 1.
  - *Consequence.* A route from `two-to-two-games-theorem` must pay the forced
    blow-up at completeness amplification, from `1/2` to `1 - gamma`.
  - Where it stops: it constrains the shape of a proof and proves nothing
    toward the conjecture.

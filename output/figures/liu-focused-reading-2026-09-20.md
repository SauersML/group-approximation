# Focused reading of Liu's internality argument

This is a partial mathematical review and comparison, not certification of the paper. No Cairn claim statuses were changed.

## Section 4: energy and distance are separated

Theorem 4.3 asserts equivariant rounding of a positive operator-valued partition to a projection-valued partition in the original dimension. Its important feature is that the total commutator energy tends to zero as the input energy tends to zero, even when the input purity deficit has a fixed positive limit. Distance from the input is bounded in terms of that purity deficit.

The proof first builds overlapping spectral cuts and an auxiliary direct sum of dimension at most four times the physical dimension. The column of cuts is an intertwiner in the ultraproduct. Inside the auxiliary commutant, projection comparison moves its range to a projection commuting with the entire internal algebra of outcome labels. Pinching then lifts this range to coordinate projections respecting all labels. A partial isometry pulls the label partition back to the original matrix space, with an invariant remainder added to one label.

The use of the entire internal label algebra matters: an arbitrary sequence of phase choices is available as a witness, so commutation is uniform over labels even if their number grows. Exact intertwining in the quotient yields vanishing summed coordinate energy. The move does not assume that the auxiliary commutant is internal.

Primary-source checks: Houdayer–Vaes, arXiv:1203.1254, Lemma 2.1, and Ioana, *Almost commuting matrices and stability for product groups*, Lemma 2.2(1), have the projection comparison and near-identity conjugacy statements Liu uses. Their finite-algebra hypotheses apply to the corner described on Liu p.14. No concrete error was found in this targeted reading of Theorem 4.3. This does not independently verify all background von Neumann algebra facts.

## Section 5: transport minimality back to the selection window

The earlier repository artifact `research/artifacts/low-energy-povm-flexible-cuts-2026-09-08.md`, §9, identifies a specific obstruction: minimality tested only inside a selection corner does not automatically transfer to a repaired projection outside that corner.

Liu addresses this in Theorem 5.1, Steps 5–6 (pp.26–29). The partial isometry V_i has initial projection P_i in the orthogonal physical partition and final projection contained in the original selection window b_i. Every sufficiently small projection q in P_i is transported to V_i q V_i* in b_i, with rank smaller than the chosen minimum-rank p_i. The original minimum-rank selection rule therefore applies. The leakage penalty and Lemma 5.3's estimate on the actual range projections control escape from the separate repair corner e_n. This distinction between the physical block, selection window, and repair corner is essential.

The transferred lower bound has additive defects xi_i whose sum tends to zero. Lemma 5.4 removes low-energy subprojections and bounds total discarded trace by the sum of defects. It realizes each remaining compressed contraction as the average of two nearby unitaries, preserving the desired scalar gap for a doubled generator list.

## Section 6: matching and order of limits

Scalar expansion within individual blocks does not describe off-diagonal intertwiners. Lemma 6.4 uses a polar isometry to turn a potentially unbounded Hilbert–Schmidt intertwiner into a bounded one, permitting use of property (T) in the tracial ultraproduct. Proposition 6.5 makes the resulting matching uniform over pairs, clusters blocks, and constructs coherent matrix units by choosing one representative in each cluster.

Theorem 5.1 fixes a discarded-trace tolerance epsilon first and supplies a positive gap c(epsilon), which may decrease as epsilon goes to zero. Proposition 6.6 first identifies the commutant in each retained corner, then approximates the full conditional expectation with error at most 2 sqrt(epsilon). It diagonalizes these expectation estimates rather than demanding a single gap uniform in epsilon. This is a significant distinction from stronger block-decomposition formulations.

## Scope of the comparison

There is close overlap with the repository's route, tools, and explicitly recorded bottlenecks. The focused comparison did not locate the complete resolvent/range-transport/matching construction in the earlier artifacts inspected. This is not evidence of access to the repository, a general originality judgment, or a complete proof verification.

## Parallel review findings

A separate bounded audit of Lemmas 5.2–5.4 and Theorem 5.1 found no concrete gap. It checked the block-Cholesky covariance estimates, the inverse identity behind the range-leakage estimate, transfer of the minimum-rank certificate, pruning costs, and the doubled-unitary calculation. The audit relies on Theorems 3.2 and 4.3 and does not certify the entire paper. A potential text-extraction ambiguity was resolved: on p.23, gamma = sqrt(t), so the stated F(t) = O(sqrt(t)) is consistent.

An independent comparison found a particularly close match between Liu §4 Steps 1–2 and the September 8 artifact, including thresholds in [1/3,2/3], sum of cuts bounded by 3I, outcome-count-independent total energy, direct sums of cut ranges, and polar completion of compressed unitaries. Physical orthogonalization is an important additional step; the deeper comparison below shows that returning tests to their original corner and paying leakage were also already present in other Cairn artifacts. No complete block-Cholesky/monotone-resolvent assembly was located in the sources searched.

The original one-level Cairn node also differs by asking for a gap for compressed original generators; Liu obtains expansion for two perturbed copies of each generator. This and the tolerance-dependent gap prevent automatically marking the stronger original node established.

## Deeper comparison: the existing return-to-corner argument

`research/artifacts/quantum-corner-expansion-transport-2026-09-08.md`, already present in commit `cdbecda002` on September 8, sends a test projection q back into the original corner p by taking the range projection of pq. Rank does not increase. Sections 1–3 transfer expansion with an explicit leakage penalty and sum that penalty over bounded projection frames. Thus neither returning tests nor charging aggregate leakage should be described as wholly new to Liu relative to this corpus.

Section 4 of that artifact records the exact remaining difficulty: the total leakage is controlled by seed boundary beta, but the variance estimate divides by the expansion threshold c. A bound of order beta/c need not vanish when beta and c have the same order. The artifact calls for beta=o(c), stronger leakage control, or another selection principle.

Liu supplies a proposed coupled procedure: select minimum-rank seeds with an explicit repair-corner leakage penalty; repair them to vanishing-energy projections; assemble positive increments of a monotone resolvent; orthogonalize while retaining vanishing energy; and build partial isometries returning every physical test to its original selection window. Lemma 5.3 controls the sum of leakage of the actual, nonorthogonal range projections. Equations (5.38)–(5.41) then give simultaneous expansion inequalities whose total additive defect tends to zero. With the gap threshold fixed first, pruning costs also tend to zero. This is the sharper distinction, not simply the idea of corner transport.

The September 8 soft-projection-cone artifact already optimizes overlapping positive sums and controls the residual `(I-S)_+`, but explicitly leaves expansion-compatible seed selection open. Soft overlapping selection itself was therefore also already contemplated.

## Deeper comparison: multiplicity and exhaustion

Cairn has coordinate capture for genuine representations (`at-op62-holds-for-representation-lifts`), polar intertwiner repair with genuine endpoints, and equivalences characterizing a liftable masa by bounded summed block gaps. These do not construct the missing finite partition structure for arbitrary approximate representations.

Liu §6 works with inexact scalar-expanding blocks of unequal ranks. Bounded polar intertwiners allow property (T) to apply in the quotient, force asymptotically equal ranks for matching blocks, and produce coherent multiplicity matrix units after choosing a representative in each cluster. The construction captures off-diagonal commutant elements, not merely scalar diagonal blocks. Its fixed-tolerance expectation estimate then permits exhaustion without a gap uniform across all tolerances. No completed version of this combined argument was located in the inspected Cairn sources.

## What the Cairn implementation changes about this audit

The vendored `tools/cairn.py` represents claims and AND-premise routes, with alternative routes providing OR. An empty-premise route asserts a complete proof. Established refuters and invalidators disable affected paths. The compiler checks this dependency bookkeeping, not the mathematical arguments. Its `why` output confirms the recorded normalization-to-nonhyperlinearity route is directly waiting on normalization.

The native search haystack includes graph-node bodies and, with `--notes`, the notes directory; it does not directly index proof bodies under `research/artifacts/`. Searching those artifacts separately was essential here. The native site includes an interactive SVG graph, with canvas rendering for large overviews; no PNG-export command was located.

This checkout's query also reported two unrelated schema errors in `research/fix-classtransposition-presentation.md` and 45 warnings. They were not edited. Query output should not be represented as a clean whole-graph validation.

The September 13 consumption audit in `actor-commutant-has-liftable-masa-in-every-model` explicitly deprioritized that particular branch: its only normalization consumer also required vertex rounding, which already sufficed by itself. This was not a shutdown of the nonhyperlinearity program. Later work and the September 20 attempted relaunch show the broader program continued; the later interruption was the model limit.

Bottom line: close overlap in destination, route, technical tools, and several partial constructions; a specific proposed completion of the finite-block/internality bottleneck in Liu. The search does not establish dependence, historical originality against all literature, or correctness of the full paper.

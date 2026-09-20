---
rg: 2
id: fpbs-invariant-spines-iff-tight-forest-repair
kind: claim
title: A nonamenable Cayley graph has invariant sparse spines iff its wired uniform spanning forest can be made connected by an invariantly coupled sparse edge set, while invariant Cayley cost one is the same repair with a forest that may vary, so the two differ exactly by tightness of forest past sizes
distinct_from:
  fpbs-soft-collapse-iff-invariant-sparse-spines: that proves soft collapse iff invariant sparse spines and builds spines over Z-quotients; this characterises spines themselves by sparse repairs of one fixed one-ended spanning forest and leaves its open question (every fixed-price-one group) split into two prerequisites
  fpbs-bernoulli-cayley-cost-above-one-forces-nonuniqueness: that proves spines imply c_inv(S) = 1 (one direction only); this proves c_inv(S) = 1 is equivalent to sparse forest repairs with varying forest, and that spines are equivalent to the same repairs with tight past sizes, so it names exactly what the converse lacks
  fpbs-invariant-cayley-cost-literature-status: that imports c_inv(S) = 1 for Kazhdan and amenable groups; this is an unconditional reformulation of c_inv(S) = 1 and of spines on every nonamenable Cayley graph
  fpbs-infinite-contact-zero-relative-cost: that repairs a subrelation on a fixed action to get cost bounds; this repairs a one-ended spanning forest by Cayley edges and outputs a connected sparse Cayley subgraph, with density controlled by mass transport through forest pasts
  fpbs-wired-forest-degree-two: that imports expected degree two and at most two ends for the wired forest of an invariant connected graph; this uses it (and one-endedness in the transient case) as one step
---

**ESTABLISHED (written deduction, agent-verified, not refereed).** Proof in
`fpbs-invariant-spines-iff-tight-forest-repair-proof`.

**Setting.** `Gamma` is nonamenable and finitely generated, `S` is a finite
symmetric generating set, `G = Cay(Gamma,S)`, `D = |S|`, `o` is the identity.

- A **forest repair** is a `Gamma`-invariant random pair `(F, C)` of edge sets
  of `G` such that `F` is a spanning forest all of whose trees have exactly
  one end a.s., and `F ∪ C` is connected a.s. Its **connector density** is
  `eta(F,C) = P(o in V(C))`.
- In a one-ended tree every vertex `v` has a unique ray `ray(v)` toward the
  end. The **past** of `o` is `past_F(o) = {v : o in ray(v)}`. It is finite
  a.s. The **past tail** is `tau_F(M) = P(|past_F(o)| > M)`.
- `c_inv(S)` is half the infimum of `E deg_H(o)` over invariant random
  connected spanning subgraphs `H` of `G`, as in
  `fpbs-invariant-cayley-cost-literature-status`.

**Theorem.**

1. **(Cayley cost one is sparse repair.)** `c_inv(S) = 1` if and only if
   `inf eta(F,C) = 0` over forest repairs.
2. **(Spines are tight sparse repair.)** `G` has invariant sparse spines if and
   only if
   `inf over forest repairs (F,C) of inf_M [ tau_F(M) + M eta(F,C) ] = 0`.
   If `(F,C)` is a forest repair, then for every `M` and `a > 0` the graph `G`
   has an invariant connected infinite subgraph `L` with
   `P(o in V(L)) <= tau_F(M) + M (eta(F,C) + a)`.
3. **(Fixed forest.)** Equivalently, let `W` be the wired uniform spanning
   forest of `G`. `G` has invariant sparse spines if and only if for every
   `eta > 0` there is an invariant coupling of `W` with an edge set `C` such
   that `W ∪ C` is connected a.s. and `P(o in V(C)) <= eta`. In particular,
   whether spines exist does not depend on which one-ended forest one tries to
   repair, as long as its law is held fixed.

**Corollary (where the converse "Cayley cost one gives spines" dies).**
Suppose `c_inv(S) = 1` but `G` has no invariant sparse spines. Then every
sequence of forest repairs with `eta_n -> 0` has
`liminf_n inf_M [tau_(F_n)(M) + M eta_n] > 0`. The past sizes of the
repairing forests must blow up at least as fast as the connectors thin out.
The step of the natural route that fails is the one that passes from a near
optimal `H_delta` (with `E deg <= 2 + 2 delta`) to its wired forest
`F_delta = WUSF(H_delta)`. That gives a repair with `eta <= 2 delta`, but the
law of `F_delta` moves with `delta`, and nothing controls `tau_(F_delta)`
uniformly in `delta`.

**Consequences.**

- **Soft collapse (via Theorem A of
  `fpbs-soft-collapse-iff-invariant-sparse-spines`).** A soft collapse family
  exists on `G` if and only if the wired uniform spanning forest of `G` is
  sparsely repairable in the sense of item 3. If
  `beta_1^(2)(Gamma) = 0`, then the free and wired forests coincide
  (Lyons–Peres, *Probability on Trees and Networks*, Section 10.2, as used in
  the Remark after Prop. 2.1 of Hutchcroft–Pete, arXiv:1810.11015). Item 3 is then
  exactly the invariant (not factor-of-iid) form of the Hutchcroft–Pete/Lyons
  strategy of repairing the free uniform spanning forest by a percolation of
  density at most `eps`. So that strategy succeeds on `G` exactly on the soft
  collapse class.
- **Decomposition of the open question** "does every fixed-price-one group
  have invariant sparse spines". It holds at `S` if and only if both of the
  following hold, and each can fail independently of the other in principle.
  - **(R1)** `c_inv(S) = 1`. This is the Beringer–Pete–Timár question at cost
    one. If (R1) fails at one `S` for a group with `beta_1 = 0`, then
    `p_c < p_u` on every Cayley graph of that group, by Theorem 4 of
    `fpbs-bernoulli-cayley-cost-above-one-forces-nonuniqueness`.
  - **(R2)** Tightness: the repairs of (R1) can be chosen so that
    `inf_M [tau_F(M) + M eta] -> 0`. By item 3, it suffices to repair the
    fixed forest `WUSF(G)` sparsely.

**Calibration.**

- **`F_2`.** A repair gives the connected spanning graph `F ∪ C` with
  `E deg <= 2 + D eta`, while `c_inv(S) >= cost(F_2) = 2`. So `eta` is bounded
  below and there are no spines, as Lyons requires.
- **Theorem B groups (`F_2 x Z`, fibred 3-manifold groups).** Spines exist
  there, so by item 3 the wired forest of every Cayley graph of these groups is
  sparsely repairable. This is a new statement about `WUSF(F_2 x Z)`, whose
  trees an independent sparse Bernoulli sprinkling does *not* connect (BLPS
  2001 Theorem 13.7, recorded in `fpbs-infinite-contact-zero-relative-cost`).
  So the repairing set must be correlated with `W`. The two statements are
  consistent.
- **Amenable groups** are excluded by hypothesis. The implication
  (repair `=>` spines) does not use nonamenability. There one-ended invariant
  spanning trees exist, and `C = empty` gives `inf_M tau_F(M) = 0`.

## Attempts

- **2026-09-20, swarm-0917-w23-w23-bs-break, reframing: the converse
  `c_inv(S) = 1 => spines`.** It dies at exactly the Corollary.
  - Taking `H_delta` and `F_delta = WUSF(H_delta)` gives one-ended forests
    (`H_delta` is transient: see Step 1 of the route) and connectors of density
    `<= 2 delta`.
  - The mass-transport bound on the spine density needs a single `M` with
    `tau_(F_delta)(M)` small for all small `delta`.
  - Building spines inside `H_delta` alone also cannot work in general. In a
    subdivided graph, a connected subgraph must carry whole subdivided edges,
    so its density is at least the skeleton spine density. The heuristic
    example is `F_2 x Z` with `H` equal to the vertical lines plus a
    density-`rho` set of horizontal rungs: `E deg_H = 2 + O(rho)`, but no
    sparse connected subgraph of `H` is visible. This is not proved, and it is
    recorded as a warning that any proof of (R2) must use Cayley edges outside
    `H`.

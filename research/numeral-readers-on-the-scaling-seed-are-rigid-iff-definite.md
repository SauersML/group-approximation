---
rg: 2
id: numeral-readers-on-the-scaling-seed-are-rigid-iff-definite
kind: claim
title: The numeral reader on the modular-machine scaling seed is quantum rigid iff its automaton is definite, so a rigid reader recognizes only eventually periodic numeral sets; more generally, free data carried by flows that can sit in two branches of the Bass–Serre tree kill rigidity, so rogue runs on HNN geometry are never space-filling
distinct_from:
  modular-machine-scaling-seed-reads-regular-numerals: that builds the reader and leaves its rigidity (gate RR) open; this decides RR, in the negative except for definite automata.
  rigid-seed-decorations-compute-only-where-rogue-walks-fill-space: that gives the coarse-density criterion; this shows the criterion cannot be met by flows on a tree of branching at least 2, and turns the clustering obstruction into a concrete kill for tree-borne flows.
  machine-subgroup-is-core-free-and-draws-the-machine: that shows the fate-bit relative seed fails once two unterminated components sit 2D apart; this proves such configurations exist for flows that move along the stable letters, by separating them in the Bass–Serre tree.
---

**ESTABLISHED** (lane proof, bh-invent-18, 2026-09-18; elementary; **not reviewed**; no priority claimed).
Notation of `modular-machine-scaling-seed-reads-regular-numerals`:
- `S_M = ⟨x, y, r_i, l_j⟩` is a multiple HNN extension of `Z²`, and `T` is its Bass–Serre tree;
- `Y^+` is the seed with layers M (transported origins and residues) and Q (reader);
- the reader is `q(h) = q_0` at origins and `q(h) = δ(q(s(h)), α(h) mod m)` otherwise, where
  `s(h) = h·l` is the descent along the `l`-letter of the residue of `h` (row `β = 0`, `α ≥ 0`);
- `𝒜 = (Q, δ, q_0)` reads numerals most-significant digit first, and `I` is the accepted set.

## Theorem

1. **RR is decided.** `Y^+` is `D`-quantum rigid for some `D` iff `𝒜` is **definite**: there is `K`
   such that `δ(q, u)` does not depend on `q` for every digit word `u` of length `K`. In the definite
   case `[α ∈ I]` depends only on `α mod m^K` for `α ≥ m^K`. So a rigid reader recognizes exactly
   the eventually periodic sets, and nothing more.
2. **For Cohen's rope set.** Cohen's rope set `I` (digits in `{1, …, 2n}`) is read by a non-definite
   automaton (ok/bad, with bad absorbing). So its reader is not quantum rigid at any scale. Both fixes
   proposed in that node fail:
   - (a) "a free per-chain bit is rigidity-neutral" is false;
   - (b) a co-deterministic reader fails by the same argument read from the other end, unless it too is
     definite.
3. **Tree separation lemma.** Suppose a group `Λ` acts on a tree `T` so that every generator moves a
   base vertex by at most one edge, and let `Y` be a subshift over `Λ` with a point `x` having two
   modifications whose supports have footprints in `T` at tree distance `> 2D`. Then `Y` is not
   `D`-quantum rigid.
   - **Flows along stable letters.** A walk whose steps are stable letters of an HNN extension (never
     inverted, never the reverse of the entry edge) traces a geodesic ray in `T`. So two such rogue
     flows entered from different branches of a vertex stay apart by the sum of their depths.
4. **No space-filling rogue runs on HNN geometry.** A path in a tree in which every vertex has at least
   3 neighbours is never within bounded distance of every vertex. So the sufficient criterion of
   `rigid-seed-decorations-compute-only-where-rogue-walks-fill-space` (item 1) cannot hold for rogue
   walks whose motion is carried by stable letters.
   - What remains usable is the necessary criterion (its item 2).
   - It holds only if, in every point, all flow-borne free data sit within `2D` of each other. By 3, a
     tree-homogeneous design can arrange that only when rogue flows never occur in two branches of one
     point.

## Proof

**Definite ⇒ rigid.** If `𝒜` is definite, `q(h)` is a function of the `K` digits read last. These are
the residues of `α(h), α(s(h)), …, α(s^(K−1)(h))`, and the base determines them within radius `O(K)`.
So layer Q is a deterministic finite-radius function of the rigid base, and a deterministic
extension of a rigid SFT is rigid. For the periodicity claim: the last `K` digits read are the
least significant digits of `α`.

**Not definite ⇒ not rigid.**
- *An infinite word with two runs.* Suppose `𝒜` is not definite.
  - For a left-infinite digit word `w = … d_2 d_1 d_0`, let `R_n(w)` be the set of states reachable
    after reading `d_(n−1) … d_0`. It decreases in `n`.
  - If `|R_n(w)| = 1` for some `n` for every `w`, compactness gives a uniform `n`, which is
    definiteness.
  - So some `w` has `|R_n(w)| ≥ 2` for all `n`. By compactness it carries two distinct consistent
    state sequences `(q_k)` with `q_k = δ(q_(k+1), d_k)` for all `k ≥ 0`.
- *Two far chains.* Let `g_1 = r^(D+1)` and `g_2 = r^(−(D+1))` for one letter `r = r_i`. Their
  `Z²`-cosets are vertices of `T` at distance `D + 1` from the sink vertex `Z²`, in different branches.
- *A point with rogue chains there.* Use the relation `x^m r = r x^(m²)` (the letter `r` sends
  `x^m ↦ x^(m²)`).
  - For `N ∈ m^(D+1) Z`, the configuration `x^(−N).y_*^+` is, on both cosets, the forced configuration
    shifted in the `x`-direction by `N m^(D+1)` and `N m^(−(D+1))` respectively.
  - Choose `N_k = m^(D+1)(1 + m + ⋯ + m^(k−1)) · m^(D+1)` and a site `p` whose low `2D + 2` digits are
    those of `w`. Choosing `w` with digits arranged appropriately, the two chains through `g_1 p` and
    `g_2 p` read the digits of `w` in the limit `k → ∞`, and their origins recede to infinity.
  - A limit point `x ∈ Y^+` of `x^(−N_k).y_*^+` therefore has, at `g_1 p` and at `g_2 p`, descent chains
    that never reach an origin, each reading `w`.
- *The two modifications.* On an unanchored chain, the layer-Q rules link each site only to its
  successor, so every consistent state sequence on the chain extends to its basin, the sites whose
  descents merge into it. Let `y_i` replace the state sequence on basin `i` by the second run of `w`.
  Then `y_i ∈ Y^+`, and `Δ(x, y_i)` lies in basin `i`.
- *Footprints.* Descent uses only letters `l` in the forward direction, and every other site of a basin
  descends into the chain. So the tree footprint of basin `i` stays in the branch beyond `g_i`: no
  `l^(±1)`-path crosses the `r`-edges joining `g_i` to the sink. The two footprints are at tree
  distance `≥ 2D + 2`.
- *Conclusion.* By 3, `Y^+` is not `D`-rigid. `∎`

**3.** The map `λ ↦ λ·v_0` is 1-Lipschitz from the word metric to the tree, so group distance is at
least footprint distance. Apply Lemma 1 of
`quantum-rigid-subshifts-cluster-the-modifications-of-each-point`.
- *Flows are rays.* A stable-letter step leaves along an edge different from the entry edge, so the
  path is locally injective. In a tree a locally injective edge path is a geodesic. `∎`

**4.** Pick a vertex `v` at distance `R` from the path `P`. Some neighbour of `v` lies on the far side
from `P`, and going outward through such neighbours reaches vertices at distance `R + 1, R + 2, …` from
`P`. So `P` is not `R`-dense for any `R`. `∎`

**2.** Cohen's automaton has states ok and bad (absorbing). The all-ones word leaves both states
consistent, so the automaton is not definite. For (b), a co-deterministic reader determines the chain
from its top. The upward `l^(−1)`-tree above an unanchored chain again has non-synchronized infinite
words, and the same separation applies.

## What this means for the machine rung and CAP

- **Tree-borne free data are dead.** Any seed layer whose unforced data ride on flows along stable
  letters (the reader's descent chains, the fate bit on runs of `(K_M, T'_M)` whose moves use `r_i`,
  `l_j`) is non-rigid as soon as two such rogue flows can occur in two branches of one point. A
  homogeneous construction supplies this by translating along `x` (the relation `x^m r = r x^(m²)` moves
  every coset). This is the concrete mechanism behind bh-free-56's "unterminated components 2D apart".
- **Space-filling is impossible there.** By 4, rogue runs that travel by `r`/`l` moves cannot fill
  space. So the coordinator's target (a space-filling rogue design) must be realized off the tree:
  - inside a single `Z²`-coset, as a two-dimensional space-time layer (bh-free-56's reversible layer),
    where the approach and coverage conditions are planar;
  - and, over `Z²`, with no periodic boundary points carrying rogue data, because those are mortal
    (`rigid-seed-decorations-compute-only-where-rogue-walks-fill-space` item 3).

  That is gate 4, an aperiodic hierarchical layer with rigid faults, confined to one vertex coset.
- **Rigid readers recognize only periodic sets.** So the rope must not be read by a flow along the
  tree. Any machine information that crosses the tree must be carried by a definite (bounded) label,
  or by the planar layer itself.

## Lesson for general BH

In a Bass–Serre tree, flows separate. A computation whose unforced data (a reader state, a fate bit)
travel along stable letters leaves unanchored flows in far branches of some boundary point. Their free
data are independent far modifications, which quantum rigidity forbids. So rigid flow layers over HNN
geometry must be definite: the numeral reader of the scaling seed is rigid exactly when it recognizes
an eventually periodic set, and a rogue run that moves through the tree can never fill space. Any
unbounded computation in a rigid seed tower therefore has to live inside one vertex group, as a
planar, aperiodic space-time layer (gate 4). The tree can only transport bounded, definite labels
between such layers.

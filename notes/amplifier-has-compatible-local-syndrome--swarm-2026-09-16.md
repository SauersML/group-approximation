# Swarm attack: amplifier-has-compatible-local-syndrome-effects (2026-09-16)

Agent `swarm-amplifier-has-compatible-local`. Lock taken with a 180-minute
TTL and released at the end. Nothing was committed.

## Setup

The target asks for one tuple `(W,{B_a},{N(a)},C_0,R)` on the relevant NO
outputs of the common amplifier:

- clause 1: physical realization;
- clause 2: `W^*B_aW <= C_0 sum_(b in N(a)) h'_b` with occurrence at most `R`
  and uniform constants;
- clause 3: `W^*Pi_S W = 0` for every infeasible fault set.

Status inherited from the graph:

- `research/artifacts/qpcp-positive-shift-audit-2026-09-11.md` shows that
  clauses 1 to 3 hold trivially after the positive shift
  `h' = (1-eps)h + eps I`, with `C_0 = 1/eps` and `R = 1`. With the YES
  margin, the anchored criterion containing this target is equivalent to the
  root. So proving the target for an amplifier that also carries the YES
  margin and (LPC1), with the remaining anchored components, would settle the
  root. Refuting it for every such amplifier would refute the root, because
  the shifted outputs of a hypothetical root witness satisfy the criterion.
- The target already carries the primal/dual pair obstruction (sharp
  `C_0 = d/4` for both-term neighborhoods). The graph also holds the
  nonorthogonal-pair, qubit-pair and fixed-term-chain obstructions. All of
  these have a vanishing energy floor or vanishing combinatorial gap.

So the useful question is which generic properties of unshifted NO outputs
would force clauses 2 and 3. The attack answered the obvious candidate
negatively.

## What was proven

The full proofs are in `research/artifacts/gap-floor-syndrome-separation-2026-09-16.md`.
The replay script is
`experiments/gap-floor-syndrome-separation-2026-09-16/check_separation.py`.
It ran under `timeout 600`, is single-threaded, and exited 0.

1. **Local frustration certificate (Proposition 3).** Assume clauses 2 and 3.
   For every frustrated `T`, `I <= C_0 min(|T|,R) H_(U_T)`, where `U_T` is the
   union of the neighborhoods. The proof combines the covering inequality with
   domination. It recovers `C_0 >= d/4` for the single pair. The gadget version
   for a union map with multiplicity `M` gives `I <= C_0 R H_(U_T)`.
2. **High-girth graph (Lemma 4).** For every `g`, a graph exists with degree at
   most `512`, girth above `g`, and least monochromatic fraction at least
   `1/10`. The proof samples `G(n,64/n)` with `n >= max(100, 400*64^(g-1))`.
   It uses Chernoff plus a union bound over colorings, then Chebyshev and
   Markov, and then deletes short cycles and high-degree vertices.
3. **Family H(g,N) (Proposition 5).** Antiferromagnetic edge projectors on `G`
   are combined with `|E|` pair qubits carrying `P` and `Q_N`. The family has:
   - locality two, qubits, norm-one projectors and degree at most `512`;
   - combinatorial gap at least `11/30`;
   - normalized ground energy at least `1/30`;
   - least bare rounder constant at most `11`.
4. **Obstruction (Theorem 6, Corollary 7).** Any tuple satisfying clauses 2
   and 3 on `H(g,N)` has `min(g+1, (N^2+1)/(2C_0)) <= 3R`. No restriction is
   placed on `W` or on neighborhood sizes. Hence no uniform `(C_0,R)` exists on
   the family. The gadget union-map version (Theorem 8) gives
   `min(g+1, d/(C_0R)) <= 3MR`.
5. **Kernel resolutions (Remark 8A).** Only POVM structure is used. So the
   uniform kernel resolutions of
   `amplifier-admits-a-uniform-local-kernel-resolution` are excluded on the
   same family with `C_0 = 1/delta`.
6. **Averaged necessary condition (Corollary 9).** `k ell(1/(C_0 min(t,R))) <= Rm`
   for `k` disjoint frustrated sets of size at most `t`. Here `ell(delta)` is
   the least size of a term set whose sum has least eigenvalue at least `delta`.

New graph nodes:

- claim `gap-and-floor-do-not-force-compatible-syndrome-effects`, with an
  `invalidates:` entry;
- direct proof route `gap-and-floor-compatible-syndrome-separation-proof`;
- dead route `compatible-syndrome-effects-from-gap-and-rounder-floor`, which
  targets the hole and requires the gap and rounder claims.

## Approaches and where each dies

- **Unconditional proof or refutation of the target.** This dies on the
  shift. Clauses 1 to 3 hold after shifting, and with the YES margin the
  anchored criterion containing the target is as strong as the root.
  Neither a construction nor a refutation for every amplifier is attainable
  here without resolving quantum PCP.
- **Derive clauses 2 and 3 from gap, floor or rounder, locality and degree.**
  Refuted by `H(g,N)`. This is the new claim, and the dead route records the
  inference.
- **Take `N(a)` to be the frustrated sets themselves.** This works for a fixed
  finite collection of term matrices: bounded frustrated sets are uniformly
  gapped by finiteness of incidence types. It fails when matrices vary, as in
  `H(g,N)`, where every bounded subsystem is nearly frustration-free. The
  fixed-collection question remains open; neither this family nor the
  fixed-term chain decides it.
- **Solve the joint-effect SDP per instance.** Proposition 3 is a necessary
  condition that any SDP solution must meet. It shows in advance that no
  bounded-occurrence solution with uniform constants exists on `H(g,N)`.
  Solving the SDP gives no uniformity.
- **Explicit Ramanujan graphs instead of random graphs.** Probably possible
  through the least-eigenvalue bound on the maximum cut. This was not checked
  and is not used; the probabilistic lemma is fully proved.
- **Non-union gadget maps.** Not treated. Theorem 8 covers only
  `J -> union phi(i)` with `|phi(i)| <= M`.

## Weakest points

- The bookkeeping in Lemma 4. The replay checks the constants numerically,
  but the probabilistic argument is text-only.
- Relevance. The obstruction lives on exact kernels of unshifted, essentially
  classical instances (the energy problem lies in NP) with `N`-dependent
  matrices. It kills a generic inference, not the target.

## Literature (2026-09-16)

- arXiv API queries:
  - `all:"combinatorial soundness" AND all:hamiltonian` returned nothing.
  - `au:Bafna AND au:Nguyen` returned only the unrelated arXiv:2609.04173v1.
  - `au:Bafna AND all:quantum` returned nothing.
  - `all:"gap amplification" AND all:hamiltonian` returned, among others,
    arXiv:2510.01333v1 (2025-10-01) and arXiv:2403.13084v1 (2024-03-19).
  - `ti:"quantum PCP"` returned arXiv:2411.00946v1 as its newest entry.
- Three web searches found no Bafna--Nguyen--Zhang preprint. The FOCS 2026
  acceptance is recorded in `research/locality-preserving-constant-combinatorial-gap.md`
  and was not refetched.
- None of the listed papers treats compatible local syndrome effects. No
  paper was read in full, and none is used in a proof.
- Erdos (Canad. J. Math. 11, 1959) is credited for the high-girth method.
  The citation is unverified; the proof in the artifact is self-contained.

## Referee (2026-09-16)

Adversarial referee pass before landing.

**What I checked.**

- *Definitions against the graph.* The target's clauses 2 and 3 match (T2)
  and (T3). Feasibility and `s*` match (CR3) and the combinatorial-gap
  definition of `combinatorial-gap-and-rounder-give-energy-gap`, and `C_min`
  matches (CR4). Clauses 1 to 3 of
  `amplifier-admits-a-uniform-local-kernel-resolution` match Remark 8A. (SD)
  with `C=C_0R` and the support criterion match section 6.
- *Lemma 1, Lemma 2, Propositions 3 and 3G.* Re-derived line by line. The
  coefficient bound `#{a in T : b in N(a)} <= min(|T|,R)` is correct, and in
  3G a label lies in at most `|phi(i)| <= M` of the disjoint `Phi_j`.
- *Lemma 4.* Every step re-derived: `M_x >= n(n-2)/4`, `mu_x >= 16(n-2)`, the
  Chernoff exponent `(1-ln2)/2 > 1/8`, the union bound `e^4(2/e^2)^n`, Chebyshev
  `2/(Dn)`, the cycle count `n^k/(2k)` with `sum D^k/(2k) <= D^g`, the degree
  tail `D^k/k!` with ratio `<= 1/8` and `Delta! >= (Delta/e)^Delta`, deletions
  `< Dn/50 = 1.28n`, and the final ratio `>= 0.1025`. No gap found.
- *Proposition 5, Lemma 5A, Theorems 6 and 8, Corollaries 7 and 9.* Re-derived.
  The forest argument uses only "at most g edges, so no cycle". The count
  `sum_j |U_j| <= sum_a |N(a)| <= Rm` is valid for disjoint `T_j`. Nothing
  assumes a size bound on `W`, or that `a in N(a)`.
- *Independent numerics.* A separate float check of the triangle with three
  pairs (`N=3`, 6 qubits) gives `lambda_min(sum h_a) = 1.6 = tau + 2m_c/d`. The
  solver's replay exits 0 under `timeout 600`, with the output as recorded.
- *Citations.* The arXiv API (2026-09-16) confirms the titles and dates of
  arXiv:2510.01333, arXiv:2403.13084 and arXiv:2411.00946. The Erdos citation
  is correctly marked unverified and is not used.
- *Duplicates.* `bin/cairn search --similar` on the new claim returns no
  lookalike. The `distinct_from` entries are accurate.

**What I changed.**

- In the claim statement, `G` is now required to have at least one edge, so
  `m >= 1`. The conclusion now also states `C_0>0`, since the tuple forces
  it.

**Caveats that stay.**

- The dead route requires `amplified-hamiltonian-has-a-constant-cost-rounder`,
  which is itself an ancestor of the target. This forms a requires cycle
  through `rounder-from-local-ports-and-exactifier`. The route is
  INVALIDATED, and least-fixpoint semantics never lets a cycle self-justify,
  so the cycle is harmless. It honestly records the tempting argument, which
  uses the floor or rounder as a premise.
- The invalidation kills the *generic* inference only. For the actual shifted
  standard reduction both premises and the conclusion hold trivially. The
  route body says this.

**Verdict.** Sound. The direct proof route is complete as ordinary
mathematics, and the status and scope are stated honestly. Landed with the
minor statement fixes above.

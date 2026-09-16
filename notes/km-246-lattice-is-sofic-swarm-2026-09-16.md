# Soficity of the (2,4,6) Kac--Moody lattice: swarm attack, 2026-09-16

- **Lane:** `swarm-km-246-lattice-is-sofic`.
- **Hole locked and worked:** `km-246-lattice-is-sofic` (OPEN). The target node was not modified.
- **New nodes.**
  - Claim: `research/irs-rigid-triangle-colimit-sofic-iff-one-letter-model.md`.
  - Route: `research/irs-rigid-triangle-colimit-one-letter-model-proof.md`. It requires only the
    ESTABLISHED `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`.
- **Artifact:** `research/artifacts/km-246-lattice-is-sofic-one-letter-models-2026-09-16.md`.
- **Script:** `experiments/km-246-lattice-is-sofic-2026-09-16/one_letter_models_checks.py`.
- **Outcome:** a reduction, not a resolution. Soficity of `S_q` is proved *equivalent* to a
  finite search problem inside one virtually free group. Before, only sufficiency was recorded.
  Nothing is decided about `S_q`.

## Setup

`S_q = Lambda_q/Z` is infinite, finitely presented, simple, Kazhdan and IRS-rigid for `q >= 4`
(`km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`, importing Caprace--Thom
arXiv:2606.27993v2 and Caprace--Remy arXiv:math/0607664). The graph records `Lambda_q` as the
colimit of the Levi triangle.
- Vertex groups: `T.(SL_2 x SL_2)`, `T.Sp_4`, `T.G_2` over `F_q`.
- Edge groups: `T.SL_2(q)`.
- This is the Abramenko--Muhlherr presentation, not read at source.

Two gates were already recorded in the target.
- The free-or-trivial test: almost actions whose global fixed set has proportion below 1.
- A sufficient one-stable-letter certificate: exact actions of the HNN group `K` in which `t`
  moves `o(d)` points.

## What was proven

For any colimit `S` of a triangle of finite groups satisfying three hypotheses:
- (S1) `S` is infinite and simple;
- (S2) `S` is IRS-rigid;
- (S3) the vertex groups embed in `S`;

the following are equivalent.
- (a) `S` is sofic.
- (b) Free vertex actions with all edges almost agreeing.
- (c) `epsilon`-models: free vertex actions, exact on two edges, with a defect set of size at
  most `epsilon d` on the third.
- (d) Actions of `K = HNN(K_0, t)` that are free on the vertex groups, with
  `|supp t| <= epsilon d`.
- (e) Finite-index torsion-free `M <= K_0` such that, for all but `epsilon [K_0:M]` cosets `kM`,
  every `k^(-1) n_x k` lies in `M`.

The proof has four parts.
- *Rounding* (Lemma A): an almost action of a finite group `H` is within
  `(|H|+1)(|H|^2+1) delta` of an action.
- *Padding* (Lemma C): add fewer than `lcm |X_ij|` points to make every chart free.
- *Alignment* (Lemma B with (F2)): two free actions of `H` disagreeing on `D` are conjugate by a
  permutation supported in `D`, and conjugating a whole chart costs `2|supp|/d` on every other
  element.
- *The converse:* an `epsilon`-model is an almost action with empty global fixed set, so the
  free-or-trivial node applies.

**Necessary shape of every model.**
- (N1) Every `K_0`-orbit meets the defect set.
- (N2) There are no Galois certificates: `M` is never normal.
- (N3) The defect elements normally generate, and a nontrivial vertex element needs at least
  `1/epsilon` of their conjugates.
- (N4) Nonsoficity is exactly a uniform support gap for `t`.

The torsion-free form of (e), with free rank `1 - [K_0:M] chi(K_0)`, is standard Bass--Serre
theory, and its proof is written out in the artifact.

At `q = 4`, with `|Z| = 1` (conditional), the three facts below give the instance data.
- `M` has index a multiple of `12831436800 = 2^12 . 3^4 . 5^2 . 7 . 13 . 17` and at least
  `540/epsilon`.
- The rank of `M` at index `lcm` is `46331360`.
- `chi(K_0) = -3.610769e-03`.

**Numerical checks (solver).** Lemmas A and B and (F2) were tested on `S3`, `A4`, `S4`, with 40 randomized
trials each (seed 20260916). All passed, with worst ratios `0.0463` (Lemma A) and `0.8889` (F2).

**Novelty.** Low. Rounding, padding and alignment of finite-group actions are folklore. The new
graph content is the necessity direction, the two-exact-edges normal form, and (N1)-(N3).

## Approaches and where each dies

- **Quantifying Caprace--Remy Theorem 15** (read at source in arXiv:math/0607664v2, Section 4.1,
  from a local text extraction). The no-quotient argument needs one fixed power `h` with `tau^h`
  in `T` modulo a finite-index normal subgroup.
  - *Fixed `h`.* In `epsilon_n`-models, for every fixed `h` and `s in T`, `rho_n(w^h s^(-1))` has
    `o(d_n)` fixed points. This is (AF2), because `tau^h notin T`.
  - *Growing `h`.* The needed identities cost `epsilon_n` times a relator count that grows with
    `h`, and nothing bounds that count against `1/epsilon_n`.
  - *Where it dies.* At the step "`tau^h` lies in `T` mod `H`".
- **Galois (normal-subgroup) certificates.** Dead by (N2). A normal `M` makes the defect all or
  nothing, and "nothing" contradicts (N1).
- **Euler characteristic / L2 counting.** The orbifold Euler characteristic of the triangle times
  `|T|` is `0.852509` at `q = 4` and grows with `q`. Even if the development were contractible
  (unknown, see `triangle-colimit-llp-reduces-to-relator-local-splitting`), this only says the
  second L2-Betti number is positive. That is consistent with Kazhdan and with soficity, so there
  is no sign obstruction. Dies at: the count has the harmless sign.
- **Spectral gap from property (T).** In a limit (Loeb) space of models, (T) makes almost
  invariant sets close to invariant ones. The limit action need not be ergodic, so invariant sets
  are allowed and no contradiction appears. The Alekseev--Thom criterion (arXiv:2608.05362v1,
  abstract read) forces every sofic embedding of `S_q` to have a non-ergodic centralizer, since
  `S_q` is finitely presented and not residually finite. That is a constraint, not an obstruction.
- **Highest-weight module truncations.** Truncate an integrable module at weight depth `n` and
  let the vertex groups act on the truncation. In non-affine type the weight multiplicities grow
  exponentially, so the boundary layer is a positive proportion and the edge disagreement does not
  vanish. This is the recorded "ball truncations" death in module form.
- **Twisting one edge by an automorphism of `X_2`.** For a free action `rho` and `phi(x) != x`,
  `rho(x)^(-1) rho(phi x)` is fixed-point free. So the twisted edge disagrees everywhere unless
  one conjugates back, which is Lemma B again.
- **Minimal degree of primitive groups.** `rho_0(n_x)` has small support in the transitive group
  `Q_0 = rho_0(K_0)`. Classical minimal-degree theorems (Jordan type; not re-read) only push a
  primitive `Q_0` towards containing `Alt(d)`, which nothing forbids. Dies at: no conflict with
  (N3).
- **Recorded deaths, not repeated here:** finite quotients, random gauges, orbit full groups,
  permanence, affine interpolation (target Attempts).

## Remark (unverified, not recorded as a node)

If the natural maps `S_q -> S_(q^k)` are injective, soficity of any `S_(q^k)` gives soficity of
`S_q`. This is the Tits functor over a field extension, together with the centre as the common
kernel of the roots. So the target is monotone along field extensions. Injectivity was not checked
at source.

## Literature gate (arXiv API, queried 2026-09-16)

Repository search first.
- `bin/cairn search "sofic triangle colimit free vertex actions one edge"`.
- `bin/cairn search --similar` on the new claim file.

The nearest existing nodes are listed in the claim's `distinct_from` block. Other hits:
- `simple-vertex-triangles-are-universal-for-triangle-vtf-proof`, about virtual torsion-freeness;
- `centralizing-hnn-sofic-strategy-route`, about the sofic-safe compiler;
- `character-rigid-fp-simple-groups-stability-dictionary`.

None of them states this equivalence.

arXiv queries, sorted by submission date.
- `all:sofic AND all:Kazhdan`: 5 hits, newest 2608.05362v1 (Alekseev--Thom, 2026-08-05).
- `all:sofic AND all:Kac-Moody`: 0 hits.
- `all:hyperlinear AND all:Kac-Moody`: 0 hits.
- `all:"permutation stability" AND all:Kazhdan`: 0 hits.
- `all:sofic AND all:building AND all:lattice`: 1 hit (1711.10238v2).
- `all:"stable in permutations" AND all:simple`: 0 hits.
- `all:sofic AND all:"simple group" AND all:"finitely presented"`: 0 hits.
- `all:"invariant random subgroup" AND all:sofic AND all:simple`: 0 hits.
- `all:"triangle of groups" AND all:sofic`: 0 hits.
- `ti:sofic`: 199 hits. The newest 12 were scanned: 2608.29599, 2608.21817, 2608.05362, 2608.02025,
  2607.21398, 2607.21376, 2607.20735, 2606.25475, 2606.08279, 2604.19174, 2604.11212, 2603.21449.
- `abs:sofic AND abs:simple`: 17 hits.
- `abs:"permutation stable"`: 8 hits.

Abstracts read:
- 2608.05362v1 (Alekseev--Thom, centralizers of sofic approximations of Kazhdan groups);
- 2608.02025 (Fournier-Facio, a torsion-free non-sofic group);
- 2604.19174v4 (Ersoy, minimal non-sofic groups);
- 2606.08279v1 (Ishikura, planar complexes and soficity);
- 2608.21817v1 (Moravec, polynomial permutation stability).

None mentions Kac--Moody lattices, and none settles soficity of any finitely presented infinite
simple Kazhdan group. Status unchanged: OPEN.

**Certificate boundary.**
- The equivalence theorem is self-contained, apart from the ESTABLISHED free-or-trivial node, used
  only for (c) => (a).
- Its instance at `S_q` rests on the Abramenko--Muhlherr Levi presentation and on `Z <= T`.
  Neither was read at source; both are recorded in the graph through Caprace--Remy.
- The order of `Z` and the Levi order formulas are conditional as stated in the artifact.

## Referee (2026-09-16)

**What was checked.**
- Read both nodes, the artifact, this note and the script in full, plus
  `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial` and its proof route,
  `km-246-lattice-is-sofic`, `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`, (KM2) of
  `simple-kazhdan-kac-moody-lattices-exist` and (TC2) of
  `triangle-colimit-llp-reduces-to-relator-local-splitting`.
- Re-derived every step of the route by hand.
  - Lemma A: the orbit argument, the disjointness of the orbits `O(x)`, and the constant.
  - Lemma B: invariance of the complement of `D`, and the conjugating permutation.
  - Lemma C and (C1): residues mod `|X_ij|`.
  - (F2) and the (b) => (c) constant `|X_2|(1 + 2|X_3|(1 + 2|X_1|))`.
  - (c) <=> (d), (c) <=> (e), (N1)-(N4).
  - (c) => (a). The multiplication-table plus edge-word presentation does present the colimit.
    (AF1) holds with `m(w) epsilon_n` by (F1). Some vertex group is nontrivial by (S1), so `Fix_n`
    is empty by (M1). Consequence 1 applies with `c = 1`. The hypotheses of the free-or-trivial
    node (infinite simple, finite generating set, IRS rigid) are exactly (S1), (S2) and `A` finite.
    (S3) is used only in (a) => (b), where it is needed.
- Bass--Serre remark of the artifact (section 3): the torsion and rank formula are correct.
- Recomputed the rank formula `1 - |L_ij| chi(L_i *_T L_j)` of (TC2), and checked the Cartan
  matrix in the script against (KM2).
- Ran the script (seconds, `all checks passed`; output agrees with the tables in the artifact).
- Citation spot-checks.
  - Downloaded arXiv:math/0607664v2 and extracted its text. Section 4.1 contains Theorem 15 with
    hypotheses (1) irreducible, non-spherical, non-affine and (2) nilpotent root groups.
  - The proof sets `h = [N : T.(N n H)]`. It uses Theorem 14 for a second root and Proposition
    3(iii) for nilpotence, and ends with Lemma 10(i),(ii). Corollary 16 follows. The paraphrase in
    the artifact is accurate.
  - arXiv API metadata confirmed 2608.05362v1 (Alekseev--Thom), 2608.02025 (Fournier-Facio),
    2604.19174v4 (Ersoy), 2606.08279v1 (Ishikura), 2608.21817v1 (Moravec), 2606.27993v2
    (Caprace--Thom) and 1711.10238v2, with the stated authors and dates.
  - The arXiv queries `all:sofic AND all:Kac-Moody` and `all:sofic AND all:"twin building"`,
    rerun on 2026-09-16, return 0 hits. `km-246-lattice-is-sofic` stays OPEN.

**What was changed.**
- Fixed a genuine, small gap: the theorem was false as written in the degenerate case `d = 0`.
  On the empty set, (b), (c) and (d) hold vacuously for every triangle. The claim now requires
  `d >= 1` throughout. The route's step (c) => (a) divides by `d_n`, and now says `d_n >= 1`.
- In this note, "Referee checks" was renamed "Numerical checks (solver)", since the solver ran
  those tests.

**Verdict.** Sound after the `d >= 1` fix.
- The equivalence theorem is a correct, elementary reduction resting only on the ESTABLISHED
  free-or-trivial node. Novelty is low, as the claim says.
- The `S_q` instance and all `q`-data remain conditional on the Abramenko--Muhlherr Levi
  presentation, on `Z <= T` and on the Levi order formulas, as labelled.
- Nothing about soficity of `S_q` is decided. The remark on field extensions above is unverified
  and is not a node.

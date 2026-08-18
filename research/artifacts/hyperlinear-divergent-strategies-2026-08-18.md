# 2026-08-18 — External dossier: divergent attacks on Pestov Question 3.4

Source: user-supplied external research session (LLM-assisted, unrefereed),
pasted 2026-08-18.  The author audited the live Cairn graph, deliberately
excluded its existing Kun–Thom/Clifford, wreath, Leavitt–Steinberg,
radical-collision, Cartan/masa, Burton and subgroup-test lanes, and then went
looking for machinery in distant fields that can be converted into
theorem-shaped subproblems for `q3-4-resolved`.  It claims **no** answer to
Q3.4 in either direction.

This file records the ingestion audit and then the dossier itself; the
canonical content lives in the graph.

## Ingestion audit (this session)

### Novelty sweep — confirmed

The dossier's central methodological claim is that its machinery is absent
from this repository.  Re-run here against `research/`, `notes/` and `docs/`:
zero hits for *de Finetti*, *traffic distribution*, *traffic moment*,
*coherent configuration*, *association scheme*, *CPSD*, *completely positive
semidefinite*, *multi-marginal*, *random hyperplane*, *Goemans*,
*Schur–Weyl*, *hypergraph matching*, *Keevash*, *asymptotic quantum
Birkhoff*, *symmetric extension*.  (`argmax` hits only the Atlas
flip-stationarity scans; `unistochastic` hits one unrelated file.)  So the
region below is genuinely new machinery for this graph, not a re-slug of an
existing lane.

### Literature verified

- **arXiv:2608.02590**, Jeronimo–Wu–Xu, *Optimal Quantum de Finetti Theorems
  via Argmax Rounding*, submitted 2026-08-03.  Abstract confirms both facts
  the dossier leans on: the method is sum-of-squares/argmax **rounding** of a
  symmetric-extension relaxation, and it contains "a dimension-free bosonic
  result in Hilbert–Schmidt distance" at the optimal `Θ(N^{-1/2})` rate.  It
  also disproves Watrous's disentangler conjecture and settles the
  Christandl–König–Mitchison–Renner `O(d/N)` question.  **Checks out.**
- **arXiv:2608.07986**, Miyamoto, *Near-Optimal Gap Amplification for
  Nonnegative Unentangled Quantum Proofs*, submitted 2026-08-08.  Abstract
  confirms "a dimension-independent de Finetti theorem in Hilbert–Schmidt
  norm that applies when the number of registers under consideration grows
  logarithmically".  **Checks out.**
- **arXiv:1009.0778**, Haagerup–Musat.  Abstract confirms the negative
  solution of the asymptotic quantum Birkhoff conjecture.  **Checks out**;
  this is the no-go the dossier uses as a boundary, and it is now recorded in
  the graph as `asymptotic-quantum-birkhoff-false`.
- **arXiv:2312.16765**, Culf–Mousavi–Spirig, *Approximation algorithms for
  noncommutative CSPs*.  **Checks out.**

The remaining references (Pestov 0804.3968; Burton–Chaudkhari–Juschenko–
Muliarchyk 2311.09202; Male 1111.4662; Charlesworth et al. 2404.07350;
Sikora–Varvitsiotis 1506.07297; Laurent–Piovesan 1312.6643; Pass 1406.0026;
Keevash 1807.05752; Martin–Tanaka 0811.2475; Hirasaka–Kim–Ponomarenko
1801.01328) were **not** re-fetched; they are standard and pre-2026, and no
node below imports a theorem from them as a premise.  Anything that later
wants to *use* one of them owes it a `-citation` route of its own.

### Mathematics re-derived here

All four of the dossier's self-contained lemmas were re-derived in full
before any of them was recorded as established:

- **Balanced amplification (its Lemma 4.1)** — correct.  With
  `a = tau(U*V)`, `tau(B(U)*B(V)) = a·conj(a) = |a|^2` because
  `conj(U)^* = conj(U^*)`, so `d_2(B(U),B(V))^2 = 2-2|a|^2 ≤ 2-2(Re a)^2
  = 2δ^2 - δ^4/2`; the `m`-fold bound then uses `1-t^m ≤ m(1-t)` on
  `t = |a|^2 ∈ [0,1]`.  Recorded as `balanced-replica-hs-amplification`.
- **Random-hyperplane binaryization (its Lemma 12.1)** — correct.  The
  Goemans–Williamson identity `Pr[sign disagreement] = E_x[θ(x)/π]`, then
  `1-cos θ ≤ θ` (lower) and Jordan's inequality `sin t ≥ 2t/π` on `[0,π/2]`
  (upper), then `E_x‖(A-B)x‖^2 = ‖A-B‖_F^2/D` and Cauchy–Schwarz.  Recorded
  as `random-hyperplane-hs-binaryization`.
- **Sphere recoding (its §8)** — correct and elementary; recorded as
  `hs-defect-is-mean-square-sphere-displacement`.
- **Permutation traffic (its Lemma 14.1)** — correct, with one caveat the
  dossier does not state: it computes the *plain* graph sum, not Male's
  injective traffic moment `τ⁰`.  The two determine each other by Möbius
  inversion over partitions of the vertex set, so nothing is lost, but a
  reader comparing against Male's normalization will not see the same
  formula.  Recorded (with the caveat) as
  `permutation-traffic-is-simultaneous-fixed-points`.

### Corrections to the dossier

- It states that Burton–Chaudkhari–Juschenko–Muliarchyk (2311.09202) is
  "already used extensively in Cairn".  It is not in the graph at all: the
  only occurrence in this repository is the legacy proof-corpus file
  `docs/TRUE_RELATIVE_BURTON_KUN_THOM_REDUCTION.md`.  The exclusion the
  dossier made on that basis was therefore correct in substance (the amenable
  control case is worked here) but wrong about where.  Nothing below depends
  on the distinction.
- Its §5 "concrete first encoding" and §19 replica/tropical material are
  proposals, not lemmas, and are recorded as such — no node asserts that the
  path-amplitude tensor `T` has the properties the program wants of it.

### What became graph

Established (each with the house companion route):
`balanced-replica-hs-amplification`, `random-hyperplane-hs-binaryization`,
`hs-defect-is-mean-square-sphere-displacement`,
`permutation-traffic-is-simultaneous-fixed-points`,
`asymptotic-quantum-birkhoff-false`, `dephasing-destroys-multiplicativity`.

Open targets: `definetti-group-table-rounding` (its Target A),
`geometric-schreier-design` (Target B) with its two subproblems
`spherical-candidate-hypergraph-quasirandom` and
`hypergraph-absorption-schreier-matching`,
`group-table-cpsd-cp-face-collapse`,
`finite-table-quantum-classical-hamming-gap` +
`coherent-groupification-of-table-gap` (Target C),
`traffic-branching-rounding-hierarchy`,
`coherent-configuration-orbital-rounding`.

Two of its no-gos became recorded-dead routes into
`hyperlinear-implies-sofic`: `sofic-model-via-quantum-birkhoff-channel-rounding`
(killed by Haagerup–Musat) and `sofic-model-via-unistochastic-dephasing`
(killed by loss of multiplicativity under dephasing).

What did **not** become graph: §20's arithmetic/Nullstellensatz moonshot (the
dossier itself gives no formulation that is not either false or unstated),
§19's replica/tropical selector (an ingredient wish, not a target), and the
§24 experiment list (kept below as prose — experiments are work items, not
propositions).

---

# The dossier, as received

> Reproduced with display formulas transcribed into the repository's plain
> `text` blocks; wording otherwise unaltered.

## Divergent attacks on Pestov Question 3.4

**Question.** Must every hyperlinear group be sofic?

**Date of audit:** 2026-08-18.  **Status: OPEN.  No proof of either direction
is claimed here.**

This document is intentionally not another pass through the dominant Cairn
lanes.  I audited the live graph and notes, excluded the approaches already
being pursued there, and then searched for machinery in distant parts of
mathematics that can be converted into theorem-shaped subproblems.

The most promising new synthesis I found is:

> Turn a hyperlinear microstate into a symmetric, dimension-free rounding
> problem; use balanced tensor amplification to create arbitrarily many
> replicas without losing HS multiplicativity; use 2026 dimension-free
> Hilbert–Schmidt de Finetti/argmax rounding to classicalize a carefully
> chosen group-table relaxation; and finish with a combinatorial
> design/permutation extraction theorem.

The second most promising synthesis is geometric:

> A normalized-HS microstate is exactly a mean-square almost action on a
> high-dimensional sphere.  Replace the amenable/Følner extraction paradigm
> by a joint quantization of that sphere into a finite labeled Schreier
> graph, using multi-marginal optimal transport, random geometric
> hypergraphs, and matching/absorption.

A third family of attacks uses richer observables than word traces:

> Traffic moments, coherent configurations, and CP-vs-CPSD cones give
> finite-dimensional languages in which "permutation consistency" is visible
> but ordinary tracial moments are not.  Use them either as a rounding
> hierarchy or as a finite separator search.

### 1. What Cairn is already doing, and what I excluded

The current root goal is `q3-4-resolved`, with the affirmative frontier node
`hyperlinear-implies-sofic` and several negative routes.  The live frontier
includes Kun–Thom / Clifford crossed-product Connes-embeddability routes;
invariant-graph Clifford models; fiber/masa-free cocycles and wreath-product
hyperlinearity; Leavitt–Steinberg normalized-HS instability; Schatten-one
survivor routes; simultaneous dilation / compressor splicing; and
amenable-near-representation approaches to the wreath candidate.

The notes also already contain substantial work on common Cartan/masa
extraction and Birkhoff monomialization; phase-cancellation gates for
monomial models; the Burton–Chaudkhari–Juschenko–Muliarchyk theorem for
amenable groups and attempts to relativize it; normal-IRS / finite-action
character formulations; subgroup tests as finite separators; property-(T)
commutant growth and adjoint-representation mechanisms; the false
"normalized HS metric group is automatically sofic" shortcut; and the failure
of naive Schoenberg/Poisson transforms to land in the finite-action character
cone.

I therefore do not count any of those as a new strategy here.  In the
repository's mathematical notes I found no substantive use of: quantum **de
Finetti**; **Schur–Weyl** as a Q3.4 rounding mechanism; **traffic
distributions**; **coherent configurations** / association schemes as an
intermediate category; **completely positive semidefinite** (CPSD) versus
completely positive (CP) cones; **multi-marginal optimal transport**;
hypergraph **absorption/design** as a permutation-extraction mechanism;
**argmax rounding**; tropical/non-Archimedean classicalization.

### 2. A finite-table lens that every new approach should respect

Fix a finite set `F` in a group `G`, containing `e` and enough products to
test a finite multiplication table.  Write

```text
d_2(U,V)^2 = (1/d)·‖U-V‖_F^2 = 2 - 2·Re tau_d(U*V)
```

for normalized Hilbert–Schmidt distance and

```text
d_H(sigma,rho) = (1/N)·|{x : sigma·x ≠ rho·x}|
```

for normalized Hamming distance.  A unitary microstate on `F` asks for
`d_2(U_g U_h, U_{gh}) ≪ 1` on tested products and `|tau(U_g* U_h)| ≪ 1` on
tested separation pairs.  A sofic model asks for the analogous conditions
with permutations and Hamming distance.

**Finite integrality-gap principle.**  If a hyperlinear group were nonsofic,
then there would be one finite table `F` and one constant `eps_0 > 0` such
that (1) for every `delta > 0`, `F` has a `delta`-accurate unitary model in
some dimension, and (2) no permutation model of `F` has defect below
`eps_0`.

This is immediate from the definitions, but it is strategically important.  A
negative solution can in principle be exposed as a finite robust
quantum/classical integrality gap.  A positive solution can be obtained from
a *table-dependent* rounding theorem; no dimension bound has to be uniform
over all tables.

## BREAKTHROUGH PROGRAM I — Dimension-free bosonic classicalization

### 3. Why the August 2026 de Finetti result changes the parameter game

Jeronimo–Wu–Xu, arXiv:2608.02590 (submitted 2026-08-03), prove the first
dimension-free bosonic de Finetti theorem in Hilbert–Schmidt norm, with
two-site error `O(N^{-1/2})`, independent of the local Hilbert-space
dimension.  Their proof is explicitly an integrality-gap / argmax-rounding
argument for a symmetric-extension SDP.

This is unusually well matched to hyperlinearity: the microstate dimension
can explode arbitrarily fast as the defect goes to zero, so any rounding
estimate containing a bad factor `d^c` is nearly useless for Q3.4; HS is
exactly the metric in the definition of hyperlinearity; symmetric tensor
powers are freely available; and the new bound is independent of the local
matrix dimension.  A second August 2026 result, Miyamoto arXiv:2608.07986,
develops a dimension-independent HS de Finetti estimate in a setting where
the number of observed registers can grow logarithmically — potentially
important if a finite-table encoding needs more than two local marginals.

The key problem is **not** to apply de Finetti blindly to a Choi state.  A
unitary channel has a maximally entangled Choi vector, and a permutation
channel does too.  The right split must be an assignment/consistency split,
not the physical input–output split.

### 4. A proved tool: balanced tensor amplification removes the dangerous phase accumulation

**Lemma 4.1 (balanced amplification).**  Let `U,V ∈ U(d)` and put
`delta = d_2(U,V)`.  Define `B(U) = U ⊗ conj(U)`.  Then
`d_2(B(U),B(V))^2 ≤ 2·delta^2`, and more generally for `m ≥ 1`,
`d_2(B(U)^{⊗m}, B(V)^{⊗m})^2 ≤ 2m·delta^2`, while
`tau(B(U)^{⊗m}) = |tau(U)|^{2m}`.

*Proof.*  Set `a = tau(U*V)`; since `delta^2 = 2-2·Re a`, `Re a = 1-delta^2/2`.
Moreover `tau(B(U)*B(V)) = tau(U*V)·conj(tau(U*V)) = |a|^2`.  Therefore

```text
d_2(B(U),B(V))^2 = 2 - 2|a|^2
                 ≤ 2 - 2(Re a)^2
                 = 2 - 2(1 - delta^2/2)^2
                 = 2·delta^2 - delta^4/2
                 ≤ 2·delta^2.
```

For `m` copies, `tau((B(U)*B(V))^{⊗m}) = |a|^{2m}`, so

```text
d_2(B(U)^{⊗m}, B(V)^{⊗m})^2 = 2(1 - |a|^{2m})
                             ≤ 2m(1 - |a|^2)
                             ≤ 2m·delta^2.
```

The trace identity is immediate from multiplicativity of the normalized trace
under tensor products.  ∎

**Consequence 4.2.**  Suppose a sequence of unitary tables has multiplicative
defect `delta_n → 0`.  Choose any integers `m_n → ∞` with `m_n·delta_n^2 → 0`
— for example `m_n = floor(delta_n^{-1})` once `delta_n < 1`.  Then the
balanced `m_n`-fold tensor tables still have multiplicative defect tending to
zero, while a tested nontrivial word with `|tau(U_w)| ≤ eta_n → 0` has
amplified normalized trace `|tau(U_w)|^{2 m_n}`, decaying dramatically
faster.  This is exactly the parameter regime a de Finetti argument wants:
**number of replicas to infinity while the local dimension may do anything
and the relation defect still tends to zero.**

*Why balancing matters.*  Ordinary tensor powers accumulate scalar phase: if
`U = e^{i·theta}·I` and `V = I`, then `d_2(U,V)` can be tiny while
`U^{⊗m} = e^{i·m·theta}·I` is far from the identity once `m·theta` is order
one.  Balanced doubling kills that phase before amplification.

### 5. The theorem-shaped de Finetti target

For a finite multiplication table `T`, build a convex "quantum assignment"
relaxation `Q_m(T)` with:

- **(DF1) Unitary lift.**  A unitary microstate with HS defect `delta`
  produces a feasible point of the `m`-symmetric-extension relaxation whose
  constraint violation is `O(sqrt(m)·delta)`.  Balanced amplification is the
  intended engine.
- **(DF2) Dimension-free local norm.**  The observable controlling all
  finite-table constraints is measured in HS norm with constants independent
  of the matrix dimension.
- **(DF3) de Finetti collapse.**  Every feasible `m`-symmetric point is
  within `O(m^{-1/2})` in the relevant local norm of a convex mixture of
  product assignment states.
- **(DF4) Product-state integrality.**  Product assignment states obeying the
  group-table constraints can be rounded, with dimension-free loss, to
  partial bijections; Hall-type repair then gives actual permutations.

If (DF1)–(DF4) can be implemented, take `m → ∞`, `delta → 0` with
`m·delta^2 → 0`.  Both the microstate error and the de Finetti error vanish.
This would prove hyperlinear ⟹ sofic.

**The genuinely hard gate is (DF4)**, and the encoding must be chosen so that
it is even plausible.  A naive Choi encoding fails: de Finetti across copies
says nothing about classicality inside the input–output pair.  A naive
dephasing encoding gives the unistochastic matrix `P_U(i,j) = |u_{ij}|^2`,
which is doubly stochastic and hence a convex combination of permutations,
but `|UV|^2 ≠ |U|^2·|V|^2` in general because of interference — precisely the
composition information one cannot throw away.  So the new object must retain
path coherence long enough to enforce multiplication and then use symmetry to
kill the irrelevant phase information only after the consistency constraints
have been imposed.

**A concrete first encoding to test.**  For one relation `gh = k`, consider
the three-index path-amplitude tensor

```text
T^{g,h,k}_{i,j,l} = (U_g)_{l,j} · (U_h)_{j,i} · conj((U_k)_{l,i}).
```

The relation `U_g U_h ≈ U_k` says that after summing over the middle index
`j`, the path amplitudes constructively match the direct amplitude.  A
permutation solution is the extreme case in which for each input `i` exactly
one middle vertex and one output vertex survive.  The proposed program is to
build a positive doubled moment object from `T`, take balanced replicas,
symmetrize the replicas, and ask whether the JWX argmax principle forces
concentration on a small number of path choices.  This is not yet a theorem;
it is a concrete algebraic object on which the de Finetti idea can be
falsified or developed.

## BREAKTHROUGH PROGRAM II — Group-table NC-CSPs and CP versus CPSD cones

### 6. Treat Q3.4 as a special noncommutative integrality-gap problem

Culf–Mousavi–Spirig, arXiv:2312.16765, develop approximation algorithms for
noncommutative CSPs by extending classical SDP-rounding ideas to operator
assignments.  Separately, the CP/CPSD-cone literature gives a clean algebraic
distinction: classical deterministic/randomized correlation data can be
represented over the **completely positive** cone, while finite-dimensional
quantum correlation data can be represented over the **completely positive
semidefinite** cone (Sikora–Varvitsiotis arXiv:1506.07297 for nonlocal-game
feasibility; Laurent–Piovesan arXiv:1312.6643 for the CPSD cone itself).

The Q3.4 version should not use an arbitrary game.  It should define a highly
special **group-table face** of these cones: given a finite partial
multiplication table `T`, construct a correlation system whose classical
points encode finite partial actions by bijections and whose
finite-dimensional quantum points encode unitary microstates with
regular-trace separation.  The desired equality is then

```text
closure( C_class(T) ) = closure( C_quant(T) )   at the regular-character face.
```

**Affirmative win.**  Prove that although CP and CPSD are very different
globally, their closures coincide on the group-table/regular-character face.
Group associativity, reversibility, uniform marginals and regular separation
may destroy the usual quantum advantage.  This would be a conceptual
explanation of hyperlinear ⟹ sofic: arbitrary quantum CSPs have integrality
gaps, but group-action CSPs at the regular trace do not.

**Negative win.**  Find an exposed linear functional `L` with

```text
inf{ L(x) : x ∈ C_quant(T) } = 0,      inf{ L(x) : x ∈ C_class(T) } ≥ c > 0,
```

and then construct a hyperlinear group whose coherent finite tables
asymptotically realize the quantum optimum.  The key is **coherent
groupification**: a generic quantum/classical CSP gap is not enough, since
many finite-dimensional quantum gadgets generate linear, hence sofic, groups.
The gap must survive through a nested sequence of group tables and be tied to
the regular trace.

Even if Q3.4 survives, this gives a computational search language: low-level
noncommutative moment/SOS hierarchies on the quantum side; CP, integer or
permutation relaxations on the classical side; explicit trace-polynomial dual
certificates; and symmetry reduction from the group table.  That is much
closer to "find a finite obstruction or prove no obstruction exists" than
another global operator-algebra argument.

### 7. A possible de Finetti + NC-CSP synthesis

The newest de Finetti theorem is itself proved as an integrality-gap
statement for a symmetric-extension SDP.  That suggests:

**Conjecture DF-CSP.**  For every fixed finite group table `T` and every
`eps > 0` there is an extension level `m = m(T,eps)` such that every
balanced, regular-trace, `m`-extendible noncommutative solution of defect at
most `eta(T,eps,m)` rounds to a permutation solution of Hamming defect at
most `eps`, with no dependence on the underlying matrix dimension.

This avoids the fatal circular parameter problem: first fix `T` and `eps`,
then choose `m`; only after that ask hyperlinearity for an absurdly accurate
microstate.  If true, this is already enough for Q3.4.

**What to prove first.**  Do not start with a full group.  Start with the
smallest table that has genuine associativity interaction: several generators
and overlapping triples `(g,h,k), (h,r,s), (g,s,t), (k,r,t)`.  This is the
finite "associativity square" where independent pairwise rounding can become
inconsistent.  If a dimension-free symmetric-extension theorem cannot repair
this square, the global route is dead.  If it can, the next step is gluing
such squares.

## BREAKTHROUGH PROGRAM III — Spherical quantization, transport, designs

### 8. Hyperlinear microstates are mean-square almost actions on a sphere

Let `U,V ∈ U(d)` and let `x` be uniform on the unit sphere of `C^d`.  Then

```text
E_x ‖Ux - Vx‖^2 = (1/d)·‖U-V‖_F^2 = d_2(U,V)^2.
```

Therefore, for a finite hyperlinear table,
`E_x ‖U_g U_h x - U_{gh} x‖^2 ≪ 1`; likewise
`E_x ‖U_g x - U_h x‖^2 = 2 - 2·Re tau(U_g* U_h)`, so trace-orthogonality of
distinct tested elements makes their actions on a typical point
macroscopically separated.  A hyperlinear microstate is thus a finite family
of measure-preserving isometries of a sphere that is an almost action **in
mean-square transport cost**, with the correct freeness statistic.  This
suggests attacking Q3.4 as a quantization problem in geometry/probability
rather than as an operator-algebra problem.

### 9. The geometric Schreier-design conjecture

Sample or construct a large nearly uniform finite point cloud
`X = {x_1,…,x_N} ⊂ S^{2d-1}`.  For each generator `s`, create a bipartite
geometric graph `B_s` on two copies of `X`, with an edge `i → j` when
`‖U_s x_i - x_j‖ ≤ r`.  For large enough `N`, each `B_s` should have many
near-perfect matchings; choosing one gives a permutation `sigma_s`
geometrically shadowing `U_s`.  The problem is to choose the matchings
**jointly**, so that for every tested relation word `w` the derived
permutation `sigma_w` fixes almost all vertices, while nontrivial tested
words move almost all vertices.

**Conjecture GSD.**  For every finite group table `T` and `eps > 0` there are
quantitative parameters `r`, `N_0`, `delta` such that if a unitary table has
normalized-HS defect at most `delta` and regular-trace separation at most
`delta`, then some sufficiently uniform spherical point cloud of size
`N ≥ N_0` admits labeled perfect matchings `sigma_s` satisfying the table in
Hamming error at most `eps`.  A dimension-independent theorem of this form
proves hyperlinear ⟹ sofic.

**Why independent nearest-neighbour matching is insufficient.**  Suppose
`sigma_g sigma_h(i)` and `sigma_{gh}(i)` correspond to two sample points that
are geometrically very close.  Hamming distance still counts them as
different unless the indices are literally equal.  This is the central
discrete–continuous gap; it is why "approximate every rotation by a
permutation of a fine net" is not a proof.  The matchings must be built with
the group law as a hard combinatorial constraint from the beginning.

### 10. Multi-marginal optimal transport formulation

For a finite word set `W`, let `mu` be uniform sphere measure and define the
coupling `gamma_U = (x ↦ (U_h x)_{h ∈ W})_# mu` on `S^W`.  Every marginal is
`mu`.  For a tested product `gh = k`, define the cost

```text
c_{g,h,k}( (x_a)_{a ∈ W} ) = ‖U_g x_h - x_k‖^2.
```

Under `gamma_U` its expected value is exactly the mean-square group-law
defect, so the unitary microstate gives an explicit low-cost multi-marginal
Monge coupling.  The desired finite sofic model is a very special integral
atomic Monge coupling: all marginals are the same `N`-point set and each
coordinate is obtained from the root coordinate by a permutation.  Hence the
theorem to seek:

> **Low-cost integral Monge rounding for group costs.**  Low-cost spherical
> couplings arising from almost unitary actions can be quantized into an
> equi-weight atomic coupling whose coordinate maps are permutations and
> whose group-table cost is small in Hamming loss.

General multi-marginal OT does not guarantee this; the structure of optimal
couplings can differ sharply from the two-marginal case.  That is an
advantage here: the correct theorem will necessarily use the special
algebraic form of the group costs.

### 11. Hypergraph matching/absorption as the integrality engine

Once a point cloud is fixed, the joint matching problem becomes a coloured
hypergraph design problem.  For a tested relation `gh = k`, create a
hyperedge recording a locally compatible choice `(i,j,l,m)` meaning: `j` is a
candidate image of `i` under `h`; `l` is a candidate image of `j` under `g`;
`m` is a candidate image of `i` under `k`; and the desired integral solution
forces `l = m` on most roots.  One then asks for a large collection of edges
with exact degree-one constraints for every generator-input and
generator-output slot — a matching/design problem, not a matrix-rounding
problem.  Modern hypergraph matching methods proceed by proving a fractional
solution, showing quasirandom degree/codegree conditions, and using a
nibble/absorption step.  This suggests a genuinely new use of hyperlinearity's
regular trace: **trace-zero may provide precisely the low-codegree
quasirandomness an absorption theorem needs.**

- **GSD-1.**  Prove that for a random spherical cloud and a trace-separated
  finite unitary table, the coloured candidate-transition hypergraph has,
  with high probability, almost uniform vertex degrees, controlled codegrees
  for distinct group words, and the divisibility conditions required for a
  simultaneous matching.  This is a finite high-dimensional probability
  calculation, much more attackable than Q3.4 itself.
- **GSD-2.**  Find a deterministic hypergraph theorem saying that the
  degree/codegree package in GSD-1 yields generator matchings whose finite
  word paths agree on `1-o(1)` of the roots.

If both succeed with dimension-free error bookkeeping, Q3.4 is solved
affirmatively.

**Why this may evade the Følner obstruction.**  Burton-style extraction
indexes an orthonormal block by a finite subset of the *group*, so
nonamenability creates a macroscopic group boundary.  The spherical-design
program indexes the finite model by a *random geometric codebook*, not by a
finite subset of `G`.  The combinatorial boundary is replaced by
matching/codegree conditions in a homogeneous probability space.  There is no
a priori Følner term.  That is the single most important conceptual reason to
test this route.

## BREAKTHROUGH PROGRAM IV — Random-hyperplane observables

### 12. A proved binaryization lemma

The false metric shortcut in Cairn correctly shows that one cannot simply
declare `(U(d), d_2)` to be a sofic metric group.  Nevertheless a weaker
statement is true and may be an excellent rounding primitive.

**Lemma 12.1.**  Let `A,B ∈ O(D)`.  Let `x,a` be independent uniform points
on `S^{D-1}` and set `b_A(x,a) = sgn⟨a, Ax⟩`, `b_B(x,a) = sgn⟨a, Bx⟩`.  Then

```text
d_2(A,B)^2 / (2·pi)  ≤  Pr[ b_A(x,a) ≠ b_B(x,a) ]  ≤  d_2(A,B) / 2.
```

The same holds for complex unitaries after realification.

*Proof.*  Condition on `x`.  Put `y = Ax`, `z = Bx`, and let
`theta ∈ [0,pi]` be their angle; a random hyperplane separates `y,z` with
probability `theta/pi`.  Write `r = ‖y-z‖ = 2 sin(theta/2)`.  Since
`1 - cos theta ≤ theta`, `r^2 = 2(1-cos theta) ≤ 2·theta`, hence
`theta/pi ≥ r^2/(2 pi)`.  Also `2 theta/pi ≤ 2 sin(theta/2) = r`, i.e.
`theta/pi ≤ r/2`, because `sin t / t ≥ 2/pi` on `[0,pi/2]`.  Average in `x`:
`E_x r^2 = D^{-1} ‖A-B‖_F^2 = d_2(A,B)^2`, and `E r ≤ sqrt(E r^2)`.  ∎

So HS-near operators become bit observables that disagree rarely;
trace-separated operators have constant probability of being distinguished by
a random bit test; repetition amplifies; and the estimates are dimension-free.

What it does **not** give: the hash `U ↦ (sgn⟨a_j, U x_j⟩)_j` is not
multiplicative.  This is therefore not a proof that HS microstates convert to
Hamming microstates.  Its useful role is as an interface inside another
consistency mechanism — as binary observables in an NC-CSP, as edge
predicates in a hypergraph design, or as a way to turn HS constraint
violation into literal Boolean disagreement before combinatorial rounding.

## BREAKTHROUGH PROGRAM V — Traffic probability and branching consistency

### 13. Why ordinary word traces are too one-dimensional

Traffic probability (Male, arXiv:1111.4662) enlarges noncommutative
probability by allowing graph-indexed matrix observables rather than only
cyclic words.  For a directed edge-labelled test graph `T` and matrices
`A_s`, a traffic moment has the schematic form

```text
tau_T(A) = (1/n) · sum over phi : V(T) → [n] of
                     prod over e = (v → w) of (A_{l(e)})_{phi(w), phi(v)}.
```

If `T` is a directed cycle this is a normalized trace of a word, which
hyperlinearity already controls.  If `T` branches, the observable records
whether several matrix-entry paths can be made compatible at shared vertices
— exactly the kind of information a permutation has and a diffuse unitary
need not have.

### 14. A useful exact lemma on permutation traffic

**Lemma 14.1.**  Suppose `P_s` are permutation matrices arising from an exact
action of the free group on a finite set `X`, and let `T` be a connected
finite labelled directed test graph.  Choose a root `v_0` and a spanning
tree; each vertex `v` acquires a word `a_v` by following the tree, and every
non-tree edge gives a cycle word `r_e`.  Then

```text
tau_T(P) = (1/|X|) · | intersection over non-tree e of Fix(r_e) |.
```

*Proof sketch.*  Once the root image `x` is chosen, the permutation
constraints on the spanning tree force every other vertex to be `a_v x`.  A
non-tree edge is consistent iff its cycle word fixes `x`.  So a valid graph
map is the same thing as a root fixed simultaneously by all cycle words.  ∎

**Consequence for the normal-Dirac target.**  If finite actions have
fixed-point characters converging to a normal `0/1` character `1_N`, then
every connected traffic moment has a forced limit: `1` if every cycle word
lies in `N`, and `0` if at least one cycle word lies outside `N`.  (The first
uses a union bound over finitely many almost-full fixed sets; the second is
bounded by the fixed-point fraction of one outside word.)  So **traffic does
not create a new independent invariant at the final 0/1 limit** — an
important failed hope.  It does create a powerful finite-defect hierarchy:
it packages simultaneous path consistency, which is exactly what rounding
needs before the limit is reached.

### 15. The traffic-lift conjecture

> **Traffic lift.**  Given a sufficiently accurate regular-character unitary
> table, construct a positive graph-functional extension whose connected
> branching moments are within `o(1)` of the canonical normal-Dirac values
> and which satisfies the positivity/reflection constraints of a finite
> permutation traffic law.

Then use a graph-moment realization theorem or an explicit random-permutation
construction to obtain the finite action.  This may be more tractable than
direct monomialization: it does not ask for a common basis in which every
`U_g` is almost monomial, only for a consistent collection of graph
observables — a convex/moment problem rather than a basis-selection problem.

**Finite search program.**  Enumerate all connected labelled test graphs with
at most ~6 vertices and at least one branching vertex.  For each: derive its
exact value in a permutation table from simultaneous fixed-point events;
express the corresponding unitary traffic polynomial; impose
unitary/regular-trace/table constraints via an SDP/SOS relaxation; maximize
deviation from the canonical permutation value.  Three outcomes are valuable
— every small graph forced to the correct value (evidence for a universal
traffic lift); one graph with a robust gap (a concrete new obstruction); or a
gap that disappears only after balanced/symmetric extension (direct evidence
for Program I).  The key economy: **cycles need not be searched**, since they
carry no information beyond ordinary traces.

## BREAKTHROUGH PROGRAM VI — Coherent configurations

### 16. Permutation representations have an extra integral algebra

Let a finite group act on a finite set `X`.  Its commutant in `End(C^X)` has
a canonical basis given by the orbitals of the action on `X × X`.  The
matrices `A_0,…,A_r` are `0/1`; their supports partition `X × X`; transpose
permutes the basis; `A_i A_j` is a nonnegative **integer** combination of the
`A_k`; and the all-ones matrix is their sum.  This is coherent-configuration
/ association-scheme structure.  An arbitrary finite-dimensional unitary
representation has a semisimple C*-commutant, but no reason to possess a
distinguished nonnegative integral orbital basis.  This suggests a new
intermediate category:

```text
unitary representation  →  approximately coherent orbital algebra
                        →  permutation representation.
```

This is not the existing Cartan route.  A Cartan/masa route tries to find a
basis in the original Hilbert space and monomialize each `U_g`.  The
coherent-configuration route works in the commutant / pair space and tries to
recover a finite relational structure from integral multiplication constants:
basis-free at the first stage, and algebraic-combinatorial rather than
simultaneous-diagonalization.

### 17. Balanced adjoints naturally create pair-space data

For a unitary representation `pi` the adjoint representation on `End(H)` is
`pi ⊗ conj(pi)`.  For a permutation representation on `C^X` the same tensor
representation is literally the action on ordered pairs `X × X`.  So balanced
doubling, already useful for phase control, is exactly the passage from
points to pair orbitals on the permutation side.

**Coherent-configuration rounding conjecture.**  Suppose exact free-group
representations `pi_n` have normalized characters tending to the normal
regular character `1_N`.  Then, after perhaps balanced tensor amplification,
their pair-space commutants should admit finite families of positive
contractions `A_{n,0},…,A_{n,r_n}` that are approximately orthogonal in HS
inner product, a partition of the identity/all-ones relational mass, closed
under multiplication with almost nonnegative integer structure constants, and
compatible with the generator action.  If the "almost integer" errors are
below `1/2` after suitable normalization and rank control, the structure
constants can be rounded exactly; an exact coherent configuration can then be
tested for **schurity** (coming from a permutation group) or used directly to
synthesize the action.

**Potential obstruction.**  Not every coherent configuration is schurian.
That is not fatal: a coherent configuration is itself a finite relational
model, and the missing step becomes a well-studied algebraic-combinatorial
realization problem (Hirasaka–Kim–Ponomarenko arXiv:1801.01328) rather than
an arbitrary operator problem.

### 18. A classical/quantum cone hierarchy for traffic and orbitals

The CP/CPSD distinction can be applied not to generic game correlations but
to **orbital Gram data**.  In a finite permutation model, indicator vectors
of orbitals and local transition events are nonnegative and their Gram
matrices lie in CP-type cones; in unitary models the analogous objects are
positive operators whose Gram matrices lie in CPSD-type cones.  This yields a
more structured version of Program II: identify the face of the CPSD cone cut
out by group multiplication, involution, regular-trace and pair-orbital
relations; prove it collapses to the closure of the CP face, or find a
separating functional.  The advantage over a generic nonlocal-game encoding
is that the variables already have the combinatorial meaning needed for a
permutation action.  A dual separator would be a finite trace-polynomial /
graph-polynomial inequality `L(orbital moments) ≥ 0` valid for every finite
action but violated by a finite-dimensional unitary table — exactly the sort
of finite certificate a negative solution needs.

## BREAKTHROUGH PROGRAM VIII — Replica/argmax/tropical selection

### 19. Tensor powers as a zero-temperature selector, after phase balancing

A unitary relation is a sum over many paths; a permutation relation has one
path per input.  If one could convert the complex path amplitudes to
nonnegative weights `w_p` and then take high powers `w_p^m`, the mass would
concentrate on maximizers as `m → ∞` — the usual zero-temperature / tropical
/ argmax mechanism.  Balanced doubling is the natural first step because it
turns scalar overlaps into absolute squares and removes global phase.  The
2026 de Finetti paper is strikingly relevant because its proof itself uses
argmax rounding, suggesting that the correct tropicalization should happen
not entrywise but at the level of a symmetric-extension moment tensor where
the argmax operation is mathematically controlled.

**Candidate path selector.**  For a finite labelled graph or multiplication
square, construct a positive replicated partition function
`Z_m = sum over path assignments p of W(p)^m` from doubled matrix
coefficients, with constraints ensuring that all replicas share the same
coarse assignment variables.  If one proves (1) low group-law defect ⟹ `Z_m`
concentrated on globally compatible assignments, (2) regular trace ⟹ no
nontrivial word concentrates on fixed assignments, and (3) dimension-free
concentration constants, then the maximizing assignments define the desired
permutations.

**Why naive tropicalization fails.**  For Fourier/Haar-like unitaries many
matrix entries have equal magnitude, so entrywise `m → ∞` preserves a huge
tie rather than selecting a path; an infinitesimal generic perturbation
breaks ties but destroys multiplicative coherence.  The only credible version
is a constraint-aware argmax theorem, probably inside the symmetric-extension
or traffic formalism.

## MOONSHOT IX — A dimension-free approximate Nullstellensatz

### 20. Can analytic smallness force a finite algebraic model?

For fixed matrix dimension, compactness/algebraic geometry says that
arbitrarily accurate approximate solutions of polynomial equations have exact
complex solutions; hyperlinearity evades this because the dimension changes.
A dream theorem would be a dimension-free effective Nullstellensatz for
group-word systems: if a finite group table has unitary solutions with
sufficiently small normalized trace/HS error, then some finite algebraic
model realizes the table on most of its mass — then reduce modulo a prime and
obtain a finite permutation action.

**Why the naive version is false or far too strong.**  Euclidean smallness of
an algebraic number has no reason to imply divisibility modulo a prime; and
an exact finite matrix model of the whole table can imply
LEF/residual-finiteness-type properties stronger than soficity.  A viable
version would have to be block/statistical: exactness only on `1-o(1)` of a
finite module, a rank/trace notion rather than entrywise congruence, and
bounds depending on the finite word table but not on ambient matrix
dimension.  Low probability, high upside: arithmetic invariant theory is one
of the few areas with techniques designed to turn polynomial near-vanishing
into exact algebraic structure using degree/height certificates.

## 21. No-go results and failed attempts

1. **Plain quantum Birkhoff is not available.**  Send `U` to a bistochastic
   quantum channel, tensor many copies, and approximate by convex
   combinations of classical/permutation channels — false in general:
   Haagerup–Musat, arXiv:1009.0778, refute the asymptotic quantum Birkhoff
   conjecture.  *Lesson:* any de Finetti/Birkhoff attack must use the special
   group-table/regular-trace/symmetric-extension face, not arbitrary
   bistochastic channels.
2. **Dephasing loses multiplication.**  `|U|^2` is doubly stochastic, but
   `|UV|^2 ≠ |U|^2 |V|^2` because of interference.  *Lesson:*
   classicalization must be delayed until after path consistency is encoded.
3. **Ordinary tensor powers accumulate phase** (§4).  *Repair:* use
   `U ⊗ conj(U)` before taking many copies.
4. **Random hyperplane hashing is not a homomorphism** (§12).  *Repair:* use
   it only as local observables inside a global CSP/design rounding theorem.
5. **Pairwise optimal transport does not give Hamming equality.**  Two
   selected sample points can be arbitrarily close while still being
   different indices.  *Repair:* choose generator permutations jointly under
   the group-law constraints — a hypergraph/design problem.
6. **Generic multi-marginal relaxations are not integral.**  The two-marginal
   Birkhoff miracle does not generalize naively to higher-dimensional
   stochastic tensors.  *Repair:* exploit the special group cost + spherical
   quasirandomness rather than expect a generic integrality theorem.
7. **A generic quantum/classical game gap does not produce a nonsofic
   group.**  Finite-dimensional perfect quantum strategies often generate
   linear groups, and finitely generated linear groups are sofic.  *Repair:*
   any negative CSP/cone gap must be tied to a nested regular-trace
   group-table construction, not merely a contextuality gadget.
8. **Traffic is not an independent limit invariant at a normal Dirac trace**
   (Lemma 14.1).  *Repair:* use traffic for finite-defect rounding, not as an
   extra limiting invariant.
9. **Naive arithmetic reduction has the wrong topology.**  Small complex
   numbers need not vanish modulo any useful prime.  *Repair:* a viable
   arithmetic route needs a normalized-rank/statistical Nullstellensatz.

## 22. How the strongest programs fit together

```text
hyperlinear finite table
        |
        v
balanced adjoint/tensor amplification
        |
        +------------------------------+
        |                              |
        v                              v
symmetric-extension / de Finetti       spherical mean-square almost action
        |                              |
        v                              v
NC-CSP / CP-CPSD relaxation            multi-marginal candidate transitions
        |                              |
        +---------------+--------------+
                        |
                        v
              traffic/orbital moments
                        |
                        v
          hypergraph/coherent-design rounding
                        |
                        v
                 finite permutations
```

The de Finetti and sphere routes attack the same obstruction from opposite
sides: de Finetti tries to remove **quantum correlation**, geometric design
tries to remove **continuous location**, traffic/coherent configurations
record the exact shared-vertex consistency both need to preserve, and
hypergraph matching is the final integrality mechanism.  A proof does not
need every box, but the diagram suggests natural hybrid lemmas.

## 23. Three theorem targets that would constitute real progress

- **Target A — dimension-free symmetric group-table rounding.**  For every
  finite partial group table `T` and `eps > 0` there are `m` and `eta > 0`
  such that every balanced `m`-extendible unitary model of defect `< eta` and
  regular-trace error `< eta` yields an `eps`-sofic permutation model.
  *Impact:* proves hyperlinear ⟹ sofic.  *Novel ingredient:* 2026
  dimension-free HS de Finetti + group-table-specific product-state
  integrality.
- **Target B — geometric Schreier design theorem.**  For every finite table
  `T` and `eps > 0`, sufficiently accurate mean-square orthogonal almost
  actions of `T` on a sphere admit a finite labelled Schreier graph whose
  word maps shadow the table on `1-eps` of the vertices.  *Impact:* proves
  hyperlinear ⟹ sofic.  *Novel ingredient:* multi-marginal optimal transport
  + random geometric hypergraph absorption.
- **Target C — finite group-table CP/CPSD separation.**  Exhibit a finite
  table `T` and `c > 0` such that the quantum/unitary defect infimum is `0`,
  the classical/permutation defect infimum is at least `c`, and `T` is
  realized coherently inside a hyperlinear group.  *Impact:* produces a
  hyperlinear nonsofic group.  *Novel ingredient:* conic/NC-CSP dual
  certificate rather than property-(T)/Clifford/radical collision.

## 24. Concrete experiments worth running now

1. **De Finetti associativity square.**  Take the smallest overlapping
   relation square `U_g U_h ≈ U_k`, `U_h U_r ≈ U_s`, `U_g U_s ≈ U_t`,
   `U_k U_r ≈ U_t`.  Build a low-level noncommutative moment relaxation and
   its symmetric extensions; optimize an explicit nonclassicality/collision
   functional; test whether the optimum shrinks with extension level
   independent of local matrix dimension.
2. **Branching traffic enumeration.**  Enumerate connected labelled test
   graphs with 3–6 vertices, discard cycles, and compute the maximum
   deviation of the unitary traffic polynomial from its canonical permutation
   value under a small group table (symmetry-reduced SOS/NPA).  Search theta
   graphs, forks, diamonds, and two-cycle graphs sharing an edge/root first.
3. **Spherical Schreier SAT.**  For random small unitary near-tables: sample
   a spherical codebook; form candidate transition graphs at several radii;
   solve the joint generator-matching problem as an IP or SAT instance;
   compare feasibility with pairwise matching feasibility.  The key
   observable is the gap between "each generator individually matches" and
   "all words jointly match".
4. **Orbital-algebra integerization.**  For exact free-group representations
   generated by small unitary matrices whose selected relators have trace
   near one, compute the pair-space commutant numerically; search for a
   positive approximately disjoint basis; estimate how close the
   multiplication coefficients can be made to nonnegative integers.
5. **CP/CPSD dual separator.**  Compile a tiny group-table consistency
   instance into classical and quantum conic relaxations; ask a solver for a
   dual functional separating the two; inspect whether the separator can be
   written as a branching traffic inequality.  This would connect Programs II
   and V automatically.

## 26. Prioritization (as given)

| Rank | Program | Novelty vs Cairn | Chance of useful theorem even if Q3.4 survives | Directness |
|---|---|---|---|---|
| 1 | Dimension-free de Finetti + group-table symmetric extensions | Very high | Very high | Direct positive route |
| 2 | Spherical quantization + hypergraph Schreier design | Very high | Very high | Direct positive route |
| 3 | Traffic branching hierarchy | Very high | Very high | Diagnostic + rounding |
| 4 | CP/CPSD / NC-CSP group-table face | High | Very high | Positive or negative |
| 5 | Coherent configurations / orbital integerization | Very high | High | Positive intermediate category |
| 6 | Random-hyperplane binaryization | High | High as ingredient | Not sufficient alone |
| 7 | Replica/tropical argmax | Very high | Medium | Ingredient / moonshot |
| 8 | Arithmetic dimension-free Nullstellensatz | Very high | Medium if formulated correctly | Moonshot |

## 27. Additional deductions

- **The dimension blow-up problem is not automatically fatal any more.**
  Balanced amplification plus dimension-free HS de Finetti lets one pick the
  symmetric-extension level *after* fixing the finite table, then request a
  microstate accurate enough that `m·delta^2 ≪ 1`.  No relation between `m`
  and the original matrix dimension is needed — a genuine structural
  improvement over any argument with an error term such as `d^C/m`.
- **The right classical object may be a coherent configuration before it is a
  group action.**  Demanding permutations immediately may be too rigid;
  traffic and pair-space data naturally produce a finite relational structure
  first.
- **Normal-Dirac traffic rigidity is good news for a positive proof.**  All
  connected permutation traffic moments are forced at a normal `0/1` limit,
  so a traffic hierarchy is not guessing an unknown limiting parameter; it
  already knows the target and only has to prove quantitative convergence.
- **The negative route should search for a robust finite cone gap**, not
  another global rigidity theorem.  If no small gaps appear across a large
  class of group tables, that empirical evidence favours the positive
  rounding program.
- **The spherical program gives a clean meaning to trace separation:**
  `tau(U_w) ≈ 0` gives `E‖U_w x - x‖^2 ≈ 2`, so freeness is a geometric
  anti-collision statement on a homogeneous space, and codegrees/packing
  probabilities can potentially be estimated from it directly, without
  extracting a masa or a group-indexed Følner block.

## 28. What would falsify the top two routes quickly?

- **De Finetti kill test.**  Find a fixed associativity-square table and a
  sequence of balanced, arbitrarily extendible finite-dimensional quantum
  solutions with vanishing group-law defect but a dimension-independent
  positive distance from every classical partial-bijection solution in the
  exact local norm needed for Hamming rounding.  That would show de Finetti
  separability is happening in the wrong tensor split.
- **Spherical-design kill test.**  Construct a sequence of exact or
  vanishing-defect orthogonal tables for which every finite point cloud and
  every choice of generator permutations geometrically shadowing the
  generators has a fixed positive relation Hamming defect — a genuine
  integrality gap between low-cost geometric fractional transport and
  labelled Schreier designs.  Such a counterexample would itself point toward
  a negative Q3.4 mechanism.

## 29. Literature used

1. V. Pestov, *Hyperlinear and sofic groups: a brief guide*, arXiv:0804.3968.
2. P. Burton, M. Chaudkhari, K. Juschenko, K. Muliarchyk, *Hyperlinear
   approximations to amenable groups come from sofic approximations*,
   arXiv:2311.09202.
3. F. G. Jeronimo, P. Wu, H. Xu, *Optimal Quantum de Finetti Theorems via
   Argmax Rounding*, arXiv:2608.02590.
4. M. Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled
   Quantum Proofs*, arXiv:2608.07986.
5. E. Culf, H. Mousavi, T. Spirig, *Approximation Algorithms for
   Noncommutative CSPs*, arXiv:2312.16765.
6. J. Sikora, A. Varvitsiotis, *Linear conic formulations for two-party
   correlations and values of nonlocal games*, arXiv:1506.07297.
7. M. Laurent, T. Piovesan, *Conic approach to quantum graph parameters using
   linear optimization over the completely positive semidefinite cone*,
   arXiv:1312.6643.
8. C. Male, *Traffic distributions and independence*, arXiv:1111.4662.
9. I. Charlesworth et al., *Random permutation matrix models for graph
   products*, arXiv:2404.07350.
10. B. Pass, *Multi-marginal optimal transport: theory and applications*,
    arXiv:1406.0026.
11. P. Keevash, *Hypergraph matchings and designs*, arXiv:1807.05752.
12. U. Haagerup, M. Musat, *Factorization and dilation problems for
    completely positive maps on von Neumann algebras*, arXiv:1009.0778.
13. W. J. Martin, H. Tanaka, *Commutative association schemes*,
    arXiv:0811.2475.
14. M. Hirasaka, K. Kim, I. Ponomarenko, *Schurity and separability of
    quasiregular coherent configurations*, arXiv:1801.01328.

## 30. Bottom line (author's)

No complete solution of Q3.4 is claimed.  The strongest new point is the
conjunction of three facts: hyperlinear defect is naturally Hilbert–Schmidt;
balanced tensor amplification lets the number of symmetric replicas go to
infinity while retaining vanishing multiplicative defect; and as of August
2026 there is a genuinely dimension-free bosonic de Finetti theorem in
Hilbert–Schmidt norm proved by argmax/SOS rounding.  The strongest
geometrically independent point is that a hyperlinear microstate is an exact
family of sphere isometries forming a mean-square almost action, so the
missing theorem can be attacked as a joint quantization/design problem.  If
one of these routes breaks, the failure should itself produce a finite,
explicit obstruction.

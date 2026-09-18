---
rg: 2
id: fpbs-nonamenability-bounds-critical-connectivity-operator
kind: claim
title: Nonamenability makes the critical connectivity operator bounded on l2
artifacts:
  - research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md
  - research/artifacts/fpbs/creative-branches.md
  - research/artifacts/fpbs/exploration.md
---

**OPEN.** For every connected, locally finite, nonamenable transitive graph
`G=(V,E)`, the matrix of critical connection probabilities

```text
T_{p_c}(u,v) = P_{p_c}(u <-> v)
```

is bounded as an operator `l2(V) -> l2(V)`. This is Hutchcroft's L2
boundedness conjecture, stated in arXiv:1904.05804. Only finiteness is asked
for; the bound may depend on the graph.

It implies `fpbs-benjamini-schramm-universal` through
`fpbs-critical-l2-implies-nonuniqueness`, and also implies mean-field critical
behaviour, so it is a **strictly stronger conjecture** than the percolation
goal, not a consequence of nonamenability that anyone has proved. Section 2 of
`research/artifacts/fpbs/docs/priority-assessment-2026-09-09.md` warns
explicitly against mistaking a clean sufficient condition for a solved
difficult part; that warning is the reason this node is OPEN and separate from
the imported implication.

The forwarded 2026-09-09 priority verdict nonetheless identifies this as the
concrete finishing theorem that makes Benjamini--Schramm the primary
affirmative target: the desired conclusion needs only a finite bound with a
graph-dependent constant, so rough but structurally correct estimates are
admissible, and neither threshold, critical exponent nor universal numerical
gap has to be computed.

## Attempts

* **Use the product law in the averaging-projection derivative
  (2026-09-10).** `fpbs-projection-noise-variance-identity` proves the
  exact positive matrix remainder in -p(1-p)Q_p'>=Q_p-Q_p^2.
  `fpbs-bernoulli-projection-resolvent-bound` integrates it to
  Q_p<=[I+p L_G/(2(1-p))]^{-1}, including on the infinite graph.
  This excludes the norm-one vertical FIID countermodel and uses the
  actual independent edge law. **Where the next step fails:** Q_p still
  divides by cluster size. Adding ghost killing preserves a resolvent
  bound, but subtracting or differentiating the separate upper bounds
  does not bound the connectivity operator. The explicit single-edge
  calculation in `fpbs-projection-resolvent-ghost-obstruction` refutes
  that inference. The size-weighted estimate remains unproved.

* **Dyadic decomposition of the critical clusters** (response 4,
  `creative-branches.md` Section 2.2; response 8, `exploration.md` Sections
  3--4). Write `<f,T_{p_c} f> <= sum_k 2^(k+1) <f,Q_k f>` where `Q_k` averages
  over clusters of size in `[2^k,2^(k+1))`, so the size-weighted summability
  `fpbs-critical-dyadic-projection-estimate` would give boundedness. On every
  regular tree the estimate holds sharply, `||Q_N|| asymp N^(-3/2)`, with an
  exact closed formula. **Where it dies:** Theorem 6 of `exploration.md`
  constructs a group-equivariant factor of iid on the nonamenable graph
  `T_4 x Z` with all clusters finite, `E|C_o|=infinity`, and divergent dyadic
  sum. Nonamenability, finiteness of clusters and FIID admissibility therefore
  do not imply the estimate; the heavy-tailed intervals keep an amenable
  direction in which the shell projections have large operator norm. Any proof
  must use that all edges incident to a vertex share one independent retention
  law, or something equally restrictive.
* **Bound a single root overlap and iterate.** Composing two independent
  cluster projections gives the exact identity
  `<delta_o, Q_k^2 delta_o> = E[1{both in shell k} |C intersect C'|/(|C||C'|)]`
  (`creative-branches.md` Section 2.3), suggesting control of chains of
  intersections by expansion plus the rank-one merger cancellation (Q1).
  **Where it dies:** the same section states the obstruction. A root-overlap
  bound controls a trace moment, not an operator norm; rare or highly aligned
  spectral directions still matter, and no argument here controls arbitrary
  test functions or high enough spectral moments.
* **Reformulate as ghost regularity.** Weighting the cluster averages by
  `e^(-t|C|)` makes `||Q(0)-Q(t)|| <= Mt` *equivalent* to boundedness of
  `T_{p_c}` (`creative-branches.md` Section 2.4). **Dead as progress:** the
  note records that this is an equivalence, hence a restatement of the
  conjecture in positive-operator language, not a weaker solved substitute.
* **Read it off the established special cases.** Hutchcroft proves the
  conjecture for several classes, and
  `fpbs-hyperbolic-and-nonunimodular-nonuniqueness` and `fpbs-sc-choi-seo`
  give the percolation conclusion for hyperbolic, nonunimodular and
  acylindrically hyperbolic geometries. **Where it dies:** those proofs use
  the geometric hypothesis directly. Section 3 of the priority assessment
  states as a research judgment, not as evidence, that a general proof may
  isolate their common mechanism and replace the geometry by nonamenability;
  no such mechanism is isolated here.
* **Weight the operator along a tree of cut vertices (2026-09-12).**
  `fpbs-free-product-cayley-graphs-have-critical-l2-gap` proves
  `||T_{p_c}||_{2->2} < infinity` for every Cayley graph of a free product
  `H_1 * ... * H_n` on a union of factor generating sets, other than the line,
  with no hypothesis on the factors. The method is a Schur test with a
  Busemann weight on the block–cut tree. The single path toward the end decays
  geometrically, and at `p_c` the paths away from the end are controlled by a
  matrix of spectral radius at most 1. **Where it dies:** the product formula
  needs cut vertices, and the down-path matrix needs block masses that do not
  depend on the entry vertex. See Section 4.2 of
  `research/artifacts/fpbs/docs/free-product-critical-l2-2026-09-12.md`.
  - Separators of two or more vertices, as in amalgams over nontrivial finite
    groups, break the product formula.
  - One-ended graphs have no block tree.
  - Transitive graphs with a cut vertex need a spectral bound, not proved here,
    for a matrix indexed by orbits of pairs (block, vertex).
* **Baire category on the compact space of marked groups (2026-09-17,
  finite-models reframing).** Restrict to Cayley graphs, and let `X_{k,eta}`
  be the compact space of `k`-marked groups with spectral radius at most
  `1-eta`. `fpbs-l2-gap-baire-dichotomy` removes every open set contained in a
  closed uniform class `U_{M,delta}`, iterates, and obtains a kernel
  `K_{k,eta}`. The gap holds on all of `X_{k,eta}` if and only if `K_{k,eta}`
  is empty. If `K_{k,eta}` is nonempty, failures are comeager in it.
  `fpbs-high-girth-uniform-l2-patch` uses Benjamini–Nachmias–Peres and
  Nachmias–Peres path counting to certify `M = 1+3/eta^2` and
  `delta = eta/(4(2k-1))` on the clopen set of girth at least `L(eta)`. So the
  kernel lies on finitely many relator cylinders `{w = e}`, `|w| < L(eta)`.
  The uniform conjecture `fpbs-uniform-l2-gap-marked-groups` then splits into
  the finitely many independently falsifiable pieces
  `fpbs-uniform-l2-gap-short-relator-cylinders`. See
  `research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`.

  **Where it dies:** Theorems 2.1–2.2 there are equivalences, and they do not
  decide whether the kernel is empty. The only certificate supplied is girth,
  which excludes every marking with a short relation, such as `Gamma x Z`,
  surface groups and any group with torsion generators of small order.
  Both claims are OPEN as of 2026-09-17: referee lenses 1 and 3 refuted the
  dichotomy claim as written, because its sentence that a failure "is never
  isolated in the marked-group topology" does not follow (an isolated marked
  group outside `C_2` would be a singleton kernel). The proofs are kept as
  attempt artifacts.
* **Produce the Schur weight invariantly (2026-09-17, obstruction).**
  `fpbs-invariant-schur-weights-cannot-certify-critical-l2` proves the
  following on every Cayley graph.
  - The normalized Schur supersolutions `W_C(p)` of `T_p` form a compact
    `Gamma`-space, compact by the Harnack bound `h(u)/h(v) <= C p^(-d(u,v))`.
  - `||T_p|| = inf{C : W_C(p) nonempty}`, so this node is equivalent to: some
    `W_C(p_c)` is nonempty.
  - An invariant probability measure on `W_C(p)` forces `chi_p <= C`, by mass
    transport and `r + 1/r >= 2`.

  **Where it dies:** at `p_c`, `chi = infinity`, so no `W_C(p_c)` carries an
  invariant measure, and every critical Schur weight has a non-coamenable
  stabilizer. This kills in one step:
  - constant weights, and weights that are factors of iid labels or of any
    invariant random object;
  - averages of weights over an invariant law;
  - weights read off an amenable quotient.

  **What survives:** a certificate must be boundary-type, a point of a compact
  `Gamma`-space without invariant measure. Both known non-perturbative
  certificates are of this type: `Delta^(1/2)`, fixed by a nonunimodular
  subgroup, and the free-product Busemann weight, fixed by an end stabilizer.
  Any general attack by Schur test has to construct such a boundary action for
  an arbitrary nonamenable group, with the Schur inequality at `p_c`. This node
  stays OPEN.

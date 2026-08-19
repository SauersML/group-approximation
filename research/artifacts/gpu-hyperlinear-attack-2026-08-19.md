# GPU attack on the hyperlinear frontier — 2026-08-19

## Executive target

Use GPUs only for **certificate discovery / adversarial falsification**.  Every
successful numerical object must terminate in an exact dimension-independent
mathematical certificate.  The first priority is the Leavitt/A8 atlas route,
because it points directly to an explicit nonhyperlinear group.  The second is
a whole-table branching/Markov route, because it could prove hyperlinear =
sofic and then combine with the known explicit nonsofic group.

## Cairn repair found during this audit

The node
`s3-weighted-two-generator-covariance-controls-commutant-distance` already had
a valid direct proof, but its proof-route id had length 70 while Cairn accepts
at most 64 characters.  Renaming that route to
`s3-weighted-covariance-gap-proof` changes the graph from 610 to 612
established claims and from 108 to 107 frontier holes.  The weighted S3
exchange rate is therefore not a mathematical bottleneck.

**Correction, measured against `main` rather than an extracted copy.**  The
id-length diagnosis is right and the repair landed, but the delta is larger
and the id was not the only broken node.  `cairn check` on `main` was
reporting three hard errors, and a file that errors is dropped along with
everything downstream of it, so the graph was loading 734 claims when it has
810.  Two direct-proof routes were also missing the mandatory `requires: []`,
and `atlas-three-word-gap-permutation-countermodel` listed a claim under
`invalidates:`, which takes routes.  After all four fixes: 810 claims, 620
established (from 561), 839 routes, 107 frontier holes.  Fixing one error
also revealed a fourth, so the check has to be iterated to a fixed point.

The proof is the weighted conjugation Laplacian on S3.  On the standard
2-dimensional representation the nonzero weighted gap is

    lambda(p,q) = p+q-sqrt(p^2-pq+q^2),

and polar rounding of the conditional expectation onto the commutant converts
linear distance to distance from a commuting unitary with the needed factor.

## Priority A — four-holonomy atlas GPU CEGIS

After the 2026-08-19 A4 graph-of-groups exactification, all chart and context
representation types converge to exact regular types.  The only growing object
is the common multiplicity k.  The local A4 qutrit compiler removes the fixed
3-dimensional factor, and the K(2,2) disjoint-union K(2,4) packet has only four
fundamental rectangle holonomies after tree gauge.

This suggests the finite compiler:

    exact regular A4 network
      -> four U(k) holonomies H1,H2,H3,H4
      -> collision-19243 residual Q(H)
      -> four A8 covariance trace deficits D01,D12,D23,D30.

The first symbolic task is to make Q and the D's explicit trace polynomials in
the H_i.  Once this exists, run a counterexample-guided GPU loop over
k=1,2,4,8,16,... and hundreds/thousands of starts.

Useful theorem thresholds, from weakest/most optimized to stronger forms:

    D_a + D_b < 1/512

or

    24(D01+D23+D30) + D12 < 1/256,

or the optimized root-energy ellipse

    S^2 + S*x12 + x12^2 < 3/512,
    S = 2*x01 + 2*x23 + 4*x30,
    xij = sqrt(Dij).

GPU primal problem:

    maximize target_energy(H)
    subject to collision_defect(H) <= eps
               packet/stable-letter residual <= eps
               H_i unitary.

Use a penalty/augmented-Lagrangian schedule and batch many independent starts.
The key scientific observable is the best value as a function of k and eps,
not a single optimizer.

Three outcomes are useful:

1. Best value stays well below threshold and stabilizes with k.  Fit a dual
   PSD / moment certificate and try exact rational reconstruction.
2. A stable escape exceeds threshold.  The specific ceiling route is false;
   inspect the escape block and add only the packet observable that detects it.
3. Escape decreases with increasing constraint radius but not with k.  This is
   evidence for a finite local-to-global compiler and tells us which residuals
   belong in the certificate.

### Certificate extraction

Do not mistake finite-k numerics for a proof.  After the primal search, solve a
dual finite moment problem for coefficients c such that

    threshold - target_energy
      >= positive combination of residual energies
         + matrix-sector positive terms.

Because Cairn already rules out an ordinary tracial SOS valid in every finite
tracial von Neumann algebra, any final certificate must visibly use the fixed
regular finite-group/matricial sector (or another genuinely finite-dimensional
ingredient).  The GPU stage is for discovering the support and coefficients of
that object.

## Priority B — radius-nine adversarial trace separator

Cairn's `atlas-radius-nine-trace-separator` is almost tailor-made for a GPU
min-max search.  Enumerate symmetry orbits of trace words of atlas X-length
<=9, and represent each finite-dimensional sample by its trace feature vector
phi(U) plus exact relator-defect penalty.

Alternate:

- **dual step:** fit a max-margin linear functional a·phi + C*defect that
  separates the canonical group trace from every current matrix sample;
- **primal step:** for dimensions n in a schedule, use batched GPU Riemannian
  optimization to find a unitary tuple minimizing the candidate functional;
- append every violating tuple to the sample bank and repeat.

This is CEGIS for a matricial trace separator.  A stabilized sparse functional
with rational-looking coefficients is a serious proof target.  If the inner
optimizer repeatedly kills every candidate, the radius-nine node is probably
too optimistic and we should increase the word window rather than hand-tune
coefficients.

## Priority C — Enomoto / branching marks / Möbius coordinates

The new paper's reusable mechanism is not specific to module categories:
orient dependencies so the change-of-basis is unitriangular, then classical
realizability becomes nonnegativity of mixed coordinates, and the first
negative coordinate is a canonical obstruction.

For a finite implication window, let the locally closed stabilizer patterns be
the closed sets B.  Define branching moments

    m(A) = Pr[A is contained in the point stabilizer].

If p(B) is the probability of exact closed pattern B, then

    m(A) = sum_{B >= A} p(B).

The zeta matrix of the closed-set poset is unitriangular, so

    p(B) = sum_{A >= B} mu(B,A) m(A).

Every classical finite action therefore satisfies the canonical Möbius sign
inequalities p(B)>=0.  These should replace blind enumeration of arbitrary
traffic graphs: each Möbius row tells us exactly which simultaneous-fixed-set
branching moments to combine.

The built-in minimal oriented associativity square

    {g,h}->k, {h,r}->s, {g,s}->t, {k,r}->t

has 40 closed sets and satisfies anti-exchange.  The script
`experiments/traffic_mark_mobius.py` computes its exact Möbius rows.

The next GPU problem is **not** raw unitary traffic (Cairn has an exact gauge
instability counterexample).  The optimization variable must include a
contextual hidden-state/POVM/relative-distribution lift.  For each candidate
lift, maximize the most negative Möbius coordinate subject to unitary table and
positivity constraints.  This gives either:

- a robust negative row: a canonical finite quantum/classical separator; or
- repeated nonnegativity: evidence for a whole-table Markovization theorem and
  a short list of inequalities to prove analytically.

## Priority D — CP/CPSD group-table face

Run the negative and positive Q3.4 programs simultaneously.  Enumerate small
partial multiplication tables with associativity squares and inverse/order
relations.  For each table:

- classical side: exact LP/MILP over finite-action/local-pattern variables;
- quantum side: low-rank CPSD / moment factorization on GPU;
- search for an exposed robust separator that survives the regular-trace and
  associativity constraints.

A local gap is not a group, so a negative result still needs coherent
groupification.  But the search can quickly tell us whether the regular
multiplication-table face behaves radically differently from generic quantum
correlation problems.

## GPU implementation discipline

Discovery runs:

- PyTorch/JAX complex64, batched starts, constraint minibatches;
- project/retract to unitary after every step;
- sweep k and epsilon, not only random seed;
- multi-GPU parallelism across k, radii, and dual candidates is embarrassingly
  parallel.

Verification runs:

- complex128;
- rerun candidate witnesses with independent implementations;
- rational reconstruction / interval arithmetic;
- exact finite-group computations;
- final proof in Lean or a small exact certificate checker.

The current sandbox has Torch/JAX but no CUDA device.  A GPU-ready prototype is
`experiments/atlas_gpu_batched_search.py`; it was CPU-smoke-tested here on the
complete radius-2 window (220 constraints).

## Stop criteria

A GPU run is not progress merely because a loss decreases.  Promote a result
only when it does one of the following:

1. falsifies a named Cairn inequality with a reproducible finite-dimensional
   witness;
2. discovers a sparse dual functional stable across dimensions and random
   starts;
3. identifies a finite escaping block/representation type that explains why a
   candidate theorem fails;
4. reduces the symbolic support needed for an exact certificate.

The most valuable immediate engineering task is therefore the **symbolic
four-holonomy compiler for collision 19243 and the four transvection trace
energies**.  Once that exists, GPU power can be aimed at the actual theorem
threshold instead of at a diagnostic surrogate.

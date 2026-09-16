# Swarm attack on `cubic-division-congruence-representations-converge-strongly` (2026-09-16)

Agent: `swarm-cubic-division-congruence-repr`.  Target locked with `--ttl 180m`.  Nothing committed.

## Setup

- `D = (K/Q, sigma, 2)`, `K = Q(2 cos 2pi/7)`, the order `Lambda = O_K + O_K x + O_K x^2`, and
  `Gamma_D = SL_1(Lambda)`.  This is a cocompact lattice in `SL_3(R)` with property (T).
  - The new nodes use a maximal order `O_D ⊇ Lambda`.  `SL_1(Lambda)` has finite index in `SL_1(O_D)`,
    and the two reductions mod `p` agree for `p` prime to the index.
- `pi_p = l^2_0(SL_3(F_p))` is the prime-level congruence representation.  The target asks that
  `||pi_p(z)|| -> ||lambda(z)||` for every `z in C[Gamma_D]`.
- The existing graph around the target:
  - tangle-freeness and delocalisation at radius `c log p`;
  - descent to thin subgroups, an equivalence;
  - the Ihara--Bass trace criterion;
  - root-counting traces for `P^2` and `F_p^3 minus 0`;
  - numerics in the `P^2`, Legendre, flag, `F_p^3 minus 0` and conic sectors.

  No cuspidal sector had been tested.

## Literature gate (checked 2026-09-16)

No source I found resolves the target, or the corresponding question for any cocompact lattice in
`SL_3(R)`.  The sources, as found by search and fetched abstracts:

- arXiv:2510.12520, van Handel, "Strong Convergence: A Short Survey" (ICM 2026 proceedings).  The target
  node already cites Section 2.2 as recording deterministic strong convergence for explicit free groups as
  open; I found nothing newer that changes this.
- arXiv:2507.00346, "The strong convergence phenomenon", and arXiv:2405.16026, "A new approach to strong
  convergence".  Seen only as search-result titles, not re-read today.  They are background on the polynomial
  method, which needs random models.
- arXiv:2603.24502, Gao, Kunnawalkam Elayavalli, Manzoor, Patchell, "A new source of purely finite matricial
  fields" (v1 2026-03-25, v5 2026-04-12).  According to the fetched abstract summary, it covers amalgamated free
  products, graph products and closed hyperbolic 3-manifold groups; nothing on (T), lattices or congruence
  quotients.
- arXiv:2604.14106, Gao, Kunnawalkam Elayavalli, "Toeplitz exactness for strong convergence"
  (2026-04-15/22).  C*-correspondences; not about congruence quotients.
- arXiv:2602.11905, Barbieri, Jezernik, "Strong convergence of random representations of free products of
  finite groups" (2026-02-12).  Random homomorphisms only; not deterministic.
- Representation theory of `GL_3(F_q)` and `SL_3(F_q)`: Gelfand--Graev representations, multiplicity one,
  class counts, Mackey theory.  Used as background only.
  - The one load-bearing import is multiplicity one of the Gelfand--Graev representation of `GL_3(F_p)`
    (Gelfand--Graev; Steinberg).
  - I did not fetch a source for it, so no theorem number is cited and the attribution is **unverified**.
  - Everything else in the artifact is a direct Mackey, Bruhat or counting computation.

## Approaches and where each dies

- **(a) Sarnak--Xue multiplicity plus girth.**  Every constituent of `pi_p` has dimension at least
  `p^2 + p`, and the Cayley graph of `SL_3(F_p)` on a free pair has girth `c log p`.  An eigenvalue `mu`
  then satisfies `mu <= 2 sqrt 3 exp(O(1/c))`.
  - This dies at a constant factor: beating it needs lengths `>> log p`.
  - Replacing girth by lattice-point counting in norm balls overcounts thin words and does not help.
- **(b) The `P^2` trace method, extended to the whole congruence representation.**  At fixed length the
  vector-sector traces of nontrivial words lie in `{-1, 0, 2}`.
  - Controlling them at `n >> log p` needs sign cancellation, a Chebotarev statement at lengths far beyond
    the reach of effective Chebotarev.  Dies there.
  - In the Gelfand--Graev sector the fixed-length traces vanish identically for large `p`, so there is not
    even a vertical statistic to exploit (new; part 4 of the splitting node).
- **(c) Outlier counting with a power saving.**  A bound of the form "at most `p^(8 - delta)` eigenvalues
  outside `[-2 sqrt 3 - eps, 2 sqrt 3 + eps]`" with multiplicity at least `p^2` excludes outliers only if
  `delta > 6`.
  - The available savings, from (T) via Sarnak--Xue-type density estimates, give small `delta`.  Dies there.
- **(d) A self-contained proof of the two-sector split.**  The mirabolic argument yields only degenerate
  Whittaker functionals, and `Ind_(P_(2,1))(St_2 (x) 1)` contains the non-generic `rho_(p^2+p)`.  So an
  input from the theory of generic representations is unavoidable.
  - I reduced it to multiplicity one, via the counts `p^3 - p^2` (End dimension) and `p^3 - p` (classes).
    This is the one import.
- **(e) Uniform gap from (T).**  Gives `||pi_p(Z)|| <= 4 - eps_0` uniformly, an exponential saving in the
  traces, not the square-root one.

## What was proven

The outcome is a **reduction**, not progress on the upper bound.

- **New claim `cubic-division-congruence-norm-splits-into-two-sectors`** (ESTABLISHED, unreviewed, one import),
  with proof route `cubic-division-congruence-norm-splits-into-two-sectors-proof` and artifact
  `research/artifacts/cubic-division-congruence-norm-splits-2026-09-16.md`.  It has four parts:
  1. Every nontrivial irreducible representation of `SL_3(F_p)` lies in exactly one of two sectors:
     - the vector sector `sigma_p^0 = l^2_0(F_p^3 minus 0)`;
     - the Gelfand--Graev sector `GG_p`, the sum over `a in F_p^x / F_p^x3` of `Ind_U psi_a`.

     So `||pi_p(z)|| = max(||sigma_p^0(z)||, ||GG_p(z)||)`.
  2. Both sectors converge in distribution.  So the target for a given `D` is equivalent to strong
     convergence of both sectors.
  3. The character is
     `chi_GG = kappa [(p^2-1)(p^3-1) 1{1} - (p^2-1) 1{transvection} + 1{regular unipotent}]`.
  4. For a free pair, the Ihara--Bass traces of the Gelfand--Graev sector count words that are unipotent
     mod `p`.
     - Under equidistribution the three weighted main terms cancel exactly.
     - At fixed length the traces are 0 for large `p`.
     - The criterion's forms (a) and (b) hold with `d_p = kappa (p^2-1)(p^3-1)`.
- **How part 1 was proved.**
  - Mackey shows that the vector sector has no generic constituent.
  - The vector-type irreducibles of `GL_3` number `p(p-1)`.
  - A Bruhat support computation gives `dim End(Ind_U^(GL_3) psi) = p^3 - p^2`.  With multiplicity one
    (the import), there are `p^3 - p^2` generic irreducibles.
  - The class number `p^3 - p` gives exhaustion for `GL_3`.
  - Restriction to `SL_3` gives the split; torus conjugation shows that the Gelfand--Graev pieces depend
    only on `a` mod cubes.
- **New OPEN holes**, for `D_7`:
  - `cubic-division-vector-sector-converges-strongly`;
  - `cubic-division-gelfand-graev-sector-converges-strongly`.

  Each has an `## Attempts` section.
- **New route `cubic-division-congruence-sc-from-two-sectors`** into the target.  It requires the splitting
  claim and both holes.  `D_7` is division, with invariants `1/3` at 2 and `-1/3` at 7.
- **What remains open.**
  - Both sector upper bounds.
  - The vector sector contains the `P^2` hole, which is necessary for it.
  - The Gelfand--Graev sector contains every cuspidal and Steinberg constituent.  Its traces have no
    fixed-length content, so any proof must work at lengths `>> log p` on counts of unipotent reductions.

## Computation

Directory: `experiments/cubic-division-gelfand-graev-2026-09-16/`.  Everything is single-threaded, with each
run under 10 minutes.

- `gg.c` (with `algebra.inc`, copied from `experiments/cubic-division-sc/sc_p2.c`) models `SL_3(F_p)/U` as
  pairs `(v, w)`, with section `s(v, w) = (v | w | e_k / det)` and unitriangular cocycle
  `u(g, x) = s(gx)^-1 g s(x)`.  It acts monomially by `psi_a(u(g, x))`.
- **`gg test p`** (`test-output.txt`), for `p = 5, 7, 11, 13`.
  - The identity acts trivially, and the cocycle identity fails 0 times out of 400000.
  - The traces match part 3 exactly:
    - identity `(p^2-1)(p^3-1)` per `a`;
    - transvection `-(p^2-1)` per `a`;
    - regular unipotent summing to `kappa` over `a`.

    At `p = 7` the per-`a` values are `15, -6, -6`, Gauss-sum sized, and they sum to 3.
  - The value is 0 on semisimple and mixed elements.
- **`gl3_degree_check.py`** checks the family counts and degrees in the `GL_3(F_q)` class and degree tables
  for 21 values of `q`.  Output: ALL OK.
- **`job-p13.sh`** writes `res-p13.txt`.  It uses the certified pair `A = a^19`, `B = u a^19 u^-1` in
  `SL_1(Lambda)`, at `p = 13`, with Lanczos `k = 1000`.  Ritz values are lower bounds for the norm of
  `Z = A + A^-1 + B + B^-1`; `2 sqrt 3 = 3.4641016`.

  | sector | dim | arithmetic | ctl1 (random conjugate) | ctl2 (Haar pair) |
  |---|---|---|---|---|
  | vector | 2196 | 3.5416 (+0.077) | 3.5076, 3.5562 | 3.4425, 3.5168 |
  | GG, `a = 1, 2, 4` | 368928 each | 3.4772 (+0.013) | 3.4740, 3.4791 | 3.4719, 3.4697 |

  - The three Gelfand--Graev sectors give identical extreme Ritz values.  This is expected, not a bug:
    every generic irreducible of `GL_3` that restricts irreducibly to `SL_3` lies in all three `GG_a`, by
    Frobenius, and presumably the extreme eigenvector sits in such a shared constituent.
  - Short Lanczos runs (`k = 6, 40`) do differ across `a`.
  - The arithmetic pair lies within the control ranges in both sectors.  Evidence only: `p = 13` is tiny.
- **Not run.**  `p = 29`, the next split prime, has Gelfand--Graev dimension about `2e7` per sector.  That is
  estimated infeasible within the 10-minute, single-thread and 2MB caps.

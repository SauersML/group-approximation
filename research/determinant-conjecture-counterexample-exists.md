---
rg: 2
id: determinant-conjecture-counterexample-exists
kind: claim
title: Some group has an integral group-ring matrix with Fuglede--Kadison determinant below one
root: true
distinct_from:
  determinant-conjecture: that is the universal positive statement; this asks for one violating group and matrix, which would refute it
artifacts:
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
  - research/artifacts/determinant-spectral-atoms-2026-09-12.md
---

**OPEN.** Exhibit a group `G` and `A in M_{m x n}(Z[G])` with
`det_N(G)(A) < 1`. This would refute Lück's determinant conjecture.

**Necessary shape.**
- `G` must be nonsofic (`determinant-conjecture-holds-for-sofic-groups`).
- By `determinant-conjecture-iff-serre-class-spectra`, one self-adjoint
  `A in M_n(Z[G])` and one nonzero `Q in Z[x]` must satisfy
  `integral_{Q!=0} log|Q| d mu_A < 0`.
- The model failure is `integer-moment-measure-with-negative-log-determinant`:
  conjugate algebraic eigenvalues carrying unequal von Neumann multiplicity,
  with no continuous part compensating.
- **The violating self-adjoint matrix must have infinite spectrum.** Over every
  group, finite-spectrum integral matrices have rational, Galois-equal masses
  and satisfy every Serre inequality
  (`finite-spectrum-integral-elements-obey-determinant`, via Zalesskii's
  theorem). So the model failure above cannot occur with finitely many atoms.
- **The violating self-adjoint matrix must have norm above two.** Over every
  group, a self-adjoint integral matrix of norm at most two decomposes into
  matrices over finite or virtually cyclic groups and obeys every Serre
  inequality (`norm-two-integral-matrices-reduce-to-virtually-cyclic-groups`,
  via the McKee--Smyth classification).

## Attempts

- **Test groups.** The binary Leavitt unit group
  (`openai-leavitt-unit-nonsofic`), the Kun--Thom wreaths
  (`kun-thom-nonsofic-wreath`), and Fournier-Facio's torsion-free group
  (`fournier-facio-group-is-nonsofic`). No candidate matrix has been proposed
  yet.
- **Kun--Thom wreath through finite quotients.** `L(W)` is the generalized
  Bernoulli crossed product, whose action is not sofic. The finite quotients
  obtained by summing over fibers of `G/Gamma -> G/(Gamma N)` approximate a
  proper quotient trace, not `mu_A`, because `Gamma` is not profinitely
  closed. So they certify neither side. A violation would have to live on the
  part of the spectrum that the profinite shadow does not see.
- **Galois-unequal multiplicities with finite spectrum.** Dead for every
  group. A self-adjoint `A` with atoms at `phi^2` and `phi^-2` carrying unequal
  multiplicity and no other spectrum would violate the conjecture. But its
  spectral projections are polynomials in `A` over `Q(sqrt 5)`, so they lie in
  the group algebra, and Zalesskii's theorem makes their traces rational, hence
  equal on conjugates (`finite-spectrum-integral-elements-obey-determinant`).
  This kills `determinant-counterexample-via-galois-unequal-atoms`.
- **Galois-unequal multiplicities with infinite spectrum.** Open. An isolated
  algebraic atom has its projection in `C*_r(G)`, not in `K[G]`, so neither
  Zalesskii nor soficity controls its trace. Galois invariance of
  L^2-multiplicity is known for sofic groups
  (`vn-rank-galois-invariant-for-torsion-free-groups` records the torsion-free
  question). Unequal atoms alone do not violate the conjecture; the rest of the
  spectrum must not compensate. Compensation does happen: the measure
  `0.3 delta_(phi^2) + 0.1 delta_(phi^-2) + 0.6 arcsine[-6,6]` obeys every
  Serre inequality (`research/artifacts/determinant-spectral-atoms-2026-09-12.md`,
  Example 4.2).
- **A heavy eigenvalue (2026-09-12).** Over any group, an eigenvalue `lambda`
  of a self-adjoint integral matrix with multiplicity above `n / deg(lambda)`,
  for instance a transcendental eigenvalue, yields an explicit violation
  `Q(A)`, with `Q` a box-principle polynomial of degree below `deg(lambda)`
  (`heavy-eigenvalue-gives-determinant-counterexample`, route
  `determinant-counterexample-from-heavy-eigenvalue`, open input
  `integral-matrix-eigenvalue-exceeds-degree-bound`). Conversely the conjecture
  forces algebraic eigenvalues with that bound, and at the level of one
  spectral measure nothing more about atoms (`serre-class-atoms-obey-degree-bound`).
- **Diagonally dominant matrices, through spanning forests (2026-09-17).**
  Dead as a source of violations. Over every group, a self-adjoint symmetric
  diagonally dominant `T in M_n(Z[G])`, with any signs, has `det >= 1`
  (`diagonally-dominant-integral-matrices-obey-determinant`).
  - **The proof.** Split off finite components, which contribute
    `log det'` of integer matrices. Dominate the rest by the wired uniform
    spanning forest term, which gauges to a forest Laplacian, and use Lyons'
    `h >= 0`.
  - **What it rules out.** Violations cannot be Laplacians, signed or signless
    Laplacians, or M-matrices of Cayley or Schreier multigraphs, with any
    nonnegative potential. Nor can they dominate such an injective operator.
    Reductions of such violations to quotients or to simple groups are vacuous.
    So are walk-count certificates `n log lambda - sum_k tau(A^k)/(k lambda^k)`
    for `lambda - A` with nonnegative `A` of row sums at most `lambda`.
  - **What is left.** Candidates must fail diagonal dominance, like the
    polynomials `Q(A)` above or `Delta - c` with integer `c >= 1`. Whether any
    positive `Delta - c` violates the conjecture is open.
- **Domination by a sofic subrelation (2026-09-17).** Dead as a source of
  violations, for a criterion that covers all self-adjoint integral matrices.
  If `0 <= S <= T`, with `S` injective and integral on a sofic subgroup, or on
  a sofic subrelation of an orbit relation of a free action of `G`, then
  `det T >= 1` (`sofically-dominated-integral-matrices-obey-determinant`, via
  log-monotonicity and Elek--Lippner).
  - **What it rules out.** It reproves the infinite part of the diagonally
    dominant case through a treeable relation. It kills the Laplacian-minus-
    constant candidates `Delta_S - c` whenever an infinite sofic sub-multiset
    of `S` (e.g. one element of infinite order) can be removed with the rest
    keeping bottom of spectrum at least `c`. Example: `Delta_(a,b,c,g) - 1`
    over any group with `<a,b,c>` free of rank 3 and `g` of infinite order.
  - **What is left.** A violation `T` dominates no injective integral element
    of any sofic subrelation. Keeping a random set of rows never produces one
    for square `T = B^*B`, such as the cubic `1 + w_1 + w_2`.

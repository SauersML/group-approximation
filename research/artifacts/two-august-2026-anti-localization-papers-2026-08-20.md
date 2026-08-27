# Two August 2026 anti-localization papers -- Cairn audit

This note records the parts of arXiv:2608.17429 and arXiv:2608.16857 that
touch the active normalized Hilbert--Schmidt obstruction program.  Neither
paper concerns hyperlinear groups directly, and neither supplies the missing
groupification theorem.

## A simple algebraic PCP proof: arXiv:2608.17429v1

Amireddy, Behera, Srinivasan, Sudan and Willumsgaard give a polynomial-size
binary PCP for graph 3-coloring with logarithmic randomness and constantly
many queried bits.  The construction avoids PCP composition.  Its new local
ingredient is a binary low-degree test obtained by encoding a univariate
polynomial as a low-degree multivariate polynomial and concatenating with a
low-degree Hadamard encoding.

The quantitative pieces most relevant here are:

- Theorem 4.1: a constant-query test over `F_2` whose low rejection
  probability forces closeness to the Hadamard encoding of a bounded-degree
  polynomial (with the degree relaxation stated in the theorem).
- Theorem 5.1: constant-query local correction over `F_2` with error bounded
  by `O_c(d_1/q+eta+delta)`.
- Appendix E: the complete verifier and honest prover for graph 3-coloring.

This is a cleaner possible source of constant-density binary checks than a
composition-heavy PCP.  The Schur--Clifford/S3 compiler can already turn each
fixed Boolean check into fixed-scale packet payment.  What is not supplied is
a group-word atlas for the polynomially many shared proof coordinates.  In a
matrix microstate, proof-coordinate Hamming distance does not exist until a
stable family of commuting binary coordinate projections has been
manufactured.  Globally commuting all proof bits would reduce the construction
to an ordinary classical CSP and fail the hyperlinearity falsification test.

## Adversarial quantum fault tolerance: arXiv:2608.16857v1

Breuckmann, Golowich and Vazirani prove fault tolerance against arbitrary,
correlated, non-Markovian corruptions on an almost-linear number of physical
qudits at every time step.  The informal main theorem gives, for a logical
circuit on `Nbar` qudits, at most `Nbar^(5+epsilon)` physical qudits,
subpolynomial depth overhead, and tolerance

```text
N / 2^(O(sqrt(log Nbar))) = N^(1-o(1))
```

per time step.  The exact parameter statement is Theorem 7.1.

The conceptual point is unusually close to the user's anti-dilution idea.
The paper explains that separately encoding each logical qudit leaves a small
block which an adversary can erase completely.  It instead jointly encodes
all logical qudits in one high-rate, high-distance code, so there is no small
vulnerable block.  The construction uses:

- polynomial-evaluation subsystem product codes with product lower bounds on
  `X`- and `Z`-distance (Theorem 4.2);
- local testability of classical tensor-product codes, stated as a filling
  inequality in Proposition 3.3;
- a single-shot error-correction gadget whose admissible input/run/output
  error weights are explicit (Lemma 5.2);
- recursive simulative composition to reduce the physical alphabet to a
  constant (Theorem 7.1).

The tempting synthesis is

```text
Slofstra/Gowers--Hatami Clifford exactification
  -> tensor sites on a marked packet carrier
  -> joint subsystem-product encoding
  -> no localized bad block
  -> same-model capacity contradiction.
```

The arrow in the middle is not known.  The paper's errors are supported on a
specified set of tensor factors.  A normalized-HS approximate representation
has no canonical site support: one coherent low-`2`-norm perturbation may act
across every prospective factor.  Moreover, finite-group HS exactification is
uniform only for a fixed packet, while this route needs a growing Clifford
packet with constants controlled as the number of sites grows.  These two
requirements are isolated in Cairn as the site-noise bridge.

## Effect on the active routes

The papers sharpen two distinct options rather than closing either one:

1. **PCP/S3 route.**  Use the new constant-query binary verifier as the outer
   anti-localization layer, then compile its local predicates by the existing
   S3 radical charts.  Missing: a shared proof-coordinate atlas in one finite
   group presentation.
2. **Fault-tolerant Clifford tape.**  Jointly encode the addressed Clifford
   sites so an approximator cannot sacrifice one vanishing block.  Missing:
   a dimension-free conversion from normalized-HS defect to adversarial site
   weight, plus self-similar access to the growing code inside the same model.

The more aggressive fixed-BCS simplification remains logically separate.  If
the three S3 chart comparisons and their endpoint marginals can be realized
locally around each context, the existing non-CE BCS already supplies a
dimension-free global forbidden-mass floor, and neither a PCP nor the Fanizza
tape is needed.  The unresolved point is the local comparison atlas itself;
the three semidirect-product stable letters alone admit uniform stationary
type flow and do not realize the diagonal/crossed endpoint laws.

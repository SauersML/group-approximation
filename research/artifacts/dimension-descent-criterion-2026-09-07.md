# Infinite descent on matrix dimension

2026-09-07.  Audit of a ninth forwarded note proposing a different shape of
proof: a minimal-dimension contradiction in place of the compression
argument.  The criterion is correct and is authored; the operation it asks
for is open and is authored as such.  The note's Cairn references are
accurate.

## The criterion

Let `G = <s_1,...,s_k | ...>` be countable with a nontrivial involution `z`,
let `R` be a finite set of relations of `G` containing `z^2`, and put

```text
delta(U) = max_(r in R) ||r(U) - I||_op.
```

Suppose there are `epsilon_0 > 0` and an operation which, from any
`U in U(d)^k` with `delta(U) < epsilon_0` and `||z(U) - I|| >= 1`, produces
`V in U(d')^k` with `1 <= d' < d`, `delta(V) < epsilon_0` and
`||z(V) - I|| >= 1`.  Then `z` lies in the MF residual of `G`, so `G` is not
MF, and if `z` normally generates `G` then `G` has full MF radical.

The proof is three lines and uses no property (T).  A corona homomorphism
that does not kill `z` has unitary lifts with `delta -> 0`; since
`z^2 in R`, the lifts `w_n = z(U^(n))` satisfy `||w_n^2 - I|| -> 0`, so their
spectra concentrate near `{1,-1}`, and since `||w_n - I||` does not tend to
zero some eigenvalue sits near `-1` along a subsequence, giving
`||w_n - I|| -> 2`.  Past a point the tuple satisfies both hypotheses.  Take
one of least dimension and apply the operation.

The involution hypothesis is what supplies the fixed constant `1`; without
it the surviving displacement has no dimension-free lower bound.

**Characteristic two makes the hypothesis free.**  In `EL_n(R)` over a ring
of characteristic two, `e_(ij)(a)^2 = e_(ij)(2a) = 1`, so every elementary
generator is an involution, and the basis transposition of
`char-two-basis-swap-normally-generates-elementary-group` normally generates.
So for the binary Leavitt groups the criterion applies with a normally
generating involution, and its conclusion is full MF radical.

## The error budget

The operation may lose accuracy, but only superlinearly.  With
`delta(V) <= C delta(U)^2` and `epsilon_0 < 1/C`, each descent keeps
`delta < epsilon_0`, and in fact the defect converges to zero quadratically.
A constant multiplicative loss `delta(V) <= 10 delta(U)` does not suffice:
after `d` descents the defect is `10^d delta(U)`, so admissibility would
require the initial defect below `epsilon_0 10^(-d)`, and MF supplies
`delta -> 0` with no control of the rate against the dimensions, which may
grow arbitrarily fast.

## What blocks the obvious constructions

- **Compression.**  `canonical-swap-corners-have-no-dimension-descent`
  computes the sharp cost of restoring a canonical swap corner's compressed
  actor to a unitary: any dilation with vanishing compression error has
  padding at least `(1-o(1))r_n`, so the removed dimension comes back.  That
  node closes repairing the literal compressed operators and explicitly
  leaves open constructing a different action on a smaller space.  The note's
  design point is exactly there: the new tuple need not consist of
  compressions of the old generators, and may be rebuilt from different words
  and corrected using a detected finite matrix factor.
- **Topological.**  `finite-order-root-cannot-carry-a-corona-bott-class`
  blocks using a torsion root as a Bott coordinate, and the four-sphere
  cancellation recorded in `stw22-matrix-four-sphere-bott-cancellation-proof`
  is the pairing problem the note reports for winding numbers under
  conjugation.  Both are already in the graph and both point away from the
  topological route.

## Status

The criterion is proved.  The operation is the research problem, and is
recorded as the open claim `binary-leavitt-dimension-descent-operation`,
whose discharge would close the goal `property-t-free-leavitt-full-mf-radical`
through a new route.  The existing ring identities do not establish it.

## Not asserted

No literature priority.  Nothing formalized.

---
rg: 2
id: random-anchor-contraction-does-not-yet-enter-the-diffuse-basin
kind: claim
title: Exact random-anchor gap does not by itself enter the diffuse balanced basin
distinct_from:
  operator-tail-contraction-misses-uniform-diffuse-matching: that shows the unique-neighbor tail recurrence is vacuous on a uniform low commutator profile; this audits the proposed next random-anchor operation after that tail peeling.
  sequential-pinchings-have-sharp-linear-disturbance-loss: that gives a generic accumulated-measurement lower bound; this retains the positive code-distance contraction at exact bases and isolates why it cannot yet be invoked off base.
  high-type-mass-is-discontinuous-at-exact-code-tuples: that rules out generated-algebra type as the diffuse statistic; this concerns the generator-local random-anchor dynamics.
---

ESTABLISHED AS A FENCE.  The random-anchor scheme has two valid ingredients:

1. `all-dual-unique-neighbors-contract-operator-tails` peels sparse high
   coordinate commutator tails down to the bad-row floor;
2. `random-code-anchor-pinchings-contract-exact-transverse-energy` gives a
   factor `1-delta` on every transverse block once an exact code-character
   PVM is already present, and implements one anchor with controlled
   normalized-HS displacement.

They do not currently compose into a basin-entry theorem.  The tail lemma
is silent on a uniform diffuse profile `q_i=a_L`, while the proof of the
anchor gap expands operators in blocks `p_x M p_y` of the exact joint code
PVM.  Before synchronization those blocks do not exist.  Introducing them
as the conclusion of the random-anchor iteration would be circular.

The nonlinear one-anchor estimate controls movement but not contraction of
the remaining presentation energy.  If `Q_i'` is obtained by pinching and
sign-rounding against `Q_a`, then

```text
(1/L)sum_i ||Q_i-Q_i'||_2^2
 <= (1/(2L))sum_i ||[Q_a,Q_i]||_2^2.                    (RAB1)
```

Triangle inequalities therefore bound the new pair, equality, and
bounded-face defects by a constant times the old energy, but give no
coefficient smaller than one.  The strict factor in `(RAP2)` came from the
exact code-character support condition, not from pinching alone.

Local parity re-exactification does not repair this logical gap.  It may be
performed inside the common commutant of all installed anchors, so it need
not destroy those anchors.  But independently exactifying overlapping
faces produces different copies of a shared coordinate; restoring their
equality is precisely the shared-face synchronization problem.  Conversely,
using one globally shared reflection turns simultaneous local
re-exactification into the original global code-rounding problem.  Thus the
proposed alternation has not reduced the open gate unless one proves an
additional global coercivity statement.

There is also no free Lipschitz theorem for the sign stage.  With

```text
A=diag(1,-1),
B_theta=[[cos(2theta),sin(2theta)],
         [sin(2theta),-cos(2theta)]],
```

one has `Phi_A(B_theta)=cos(2theta)A`.  As `theta` crosses `pi/4`, its sign
jumps from `A` to `-A`.  Estimate `(RAP5)` correctly charges this event by
large commutator energy, so it is not a counterexample to the algorithm;
it shows that equality and face control after separate sign operations must
be routed through the charged square function, rather than through a
coordinatewise Lipschitz assertion.

Accordingly the exact positive target exposed by this audit is:

> Prove, without first choosing an exact joint PVM, that balanced all-dual
> parity energy forces the one-anchor pinching/sign operation (followed by
> a **global**, equality-compatible local correction) to contract the full
> residual energy in expectation by `1-c(delta)` up to a quadratic error.

Inside an existing operator tube this is the known alternating-projection
argument.  Outside that tube it is equivalent to the unresolved
parity-aware row/column coercivity in
`balanced-overlay-diffuse-square-function-newton`.  The random-anchor idea
therefore gives a useful stochastic realization of the exact Jacobian gap,
but not yet the missing diffuse basin capture.

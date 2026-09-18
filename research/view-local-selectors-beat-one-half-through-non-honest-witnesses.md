---
rg: 2
id: view-local-selectors-beat-one-half-through-non-honest-witnesses
kind: claim
title: Some parity-faithful view-local branch selector on gauge-randomised Grassmann 2-to-1 YES instances has orientation-lift value at least 1/2 + gamma through labellings that are not honest labellings of a small equivariant witness menu
distinct_from:
  view-local-branch-selectors-are-gauge-blind: that bounds honest lift value over subexponential equivariant menus; this asks whether the full lift value, a maximum over all labellings, escapes that bound.
  parity-leaking-branch-selectors-reach-near-perfect-completeness: that keeps honest certificates and gives up locality of views; this keeps locality and gives up honest certificates.
  lift-witness-rules-below-cycle-scale-are-gauge-blind: that shows the witnesses of this claim cannot be produced by any rule whose dependence on the right-hand sides is cycle blind, so it prunes the survivor space here; this still asks whether some cycle-leaking non-honest witness family exists.
---

**OPEN.** This is heretic denial H2.

**Assumption denied (A2).** The HOT families assume the completeness witness is
canonical: one planted or honest labelling (or its gadget encoding) certifies
YES value. All the design effort then goes into supplying richness and soundness
at gadget level, because completeness is inherited. The orientation lift inverts
this. Richness and soundness come free, and completeness is the whole problem.
The denial is that completeness above one half is witnessed by labellings that
are not honest, or by an exponentially rich, unclustered menu.

**Claim.** There are `gamma > 0`, a Grassmann 2-to-1 reduction `D` from gap-3LIN,
and a view-local selector `S` with parity leakage `w_bad(S) = o(1)` and
`s = O(1)`, such that for every YES input `I` and most gauges `z`,
`val(U_(S(I^z))) >= 1/2 + gamma`.

**Why it is the exact complement of the kill.** By
`view-local-branch-selectors-are-gauge-blind`, the honest labellings of any
equivariant menu of size `exp(o(n/s^2))` reach at most `1/2 + o(1)` on most
gauges. So a witness for this claim is necessarily one of two kinds:
- a labelling whose A- and B-labels are not restrictions of one assignment
  satisfying the window equations, for example a zoom-structured or
  vertex-wise mixed labelling;
- an honest labelling drawn from `exp(Omega(n/s^2))` well-separated
  assignments.

**Falsifiers.**
- (i) A structure theorem that every lift labelling of value `>= 1/2 + gamma`
  on a YES instance agrees on `gamma'(gamma)` of the edge weight with an honest
  labelling from an equivariant menu of `exp(o(n))` clusters. Combined with the
  kill, this refutes the claim.
- (ii) A computation on small DKKMS windows (`k <= 2`, `l <= 3`) of
  `max_labelling val(U_o)` for radius-1 view-local selectors, averaged over
  gauges, showing a maximum of `1/2 + o(1)`.

## Attempts

* **Honest certificates (2026-09-18).** **Dead as a witness type.** Honest
  labellings from equivariant menus of size `exp(o(n/s^2))` reach at most
  `1/2 + o(1)` on most gauges (`view-local-branch-selectors-are-gauge-blind`,
  Theorem 2). Falsifier (ii) is deferred: the exact lift value is a maximum over
  `2^(#B-vertices * 2^(l-1))` labellings. That is feasible only for toy windows
  with a handful of B-vertices, where locality is vacuous.

* **Witness locality below the cycle scale (2026-09-18, agent e2-w2-ugc-h2).**
  **A second witness type is dead, and the hole is now a conjunction of two
  independent conditions.** New established claim
  `lift-witness-rules-below-cycle-scale-are-gauge-blind`, artifact
  `experiments/ugc-witness-locality-2026-09-18/check_witness_locality.py`.

  The reframe is to stop asking what a labelling *is* (honest, zoom-structured,
  mixed) and ask instead what it *reads*. A witness family for this claim is a
  rule `W` on the gauge orbit, `z |-> ` a labelling of `U_(S(I^z))`. Because the
  gauge acts on the right-hand sides by the column space `Im(M)`, the average
  lift value of any such rule over an orbit is, in Fourier terms,
  `sum_(c in ker(M^T)) hat f_e(c) (-1)^(<c,b>)` summed over edges. So the
  average is **the same on every gauge orbit** unless the edge-acceptance
  functions put Fourier mass on the **cycle code** `ker(M^T)`, the sets of
  equations whose left-hand sides cancel. Since the satisfiable instances over
  `M` form one orbit and, at density `m = C n` with `C = C(eps)`, more than half
  the remaining orbits are NO instances of gap-3LIN over the same `M`, a rule
  that certifies `1/2 + gamma` here certifies `1/2 + gamma/2` there. The kill is
  quantitative: completeness `1/2 + gamma` with confidence `1 - eta` forces
  soundness at least `1/2 + gamma/2` unless the cycle leakage exceeds
  `(gamma - 2 eta)/4`. A first-moment count gives a source with cycle scale
  `Omega(n)`, so a witness rule may read a **constant fraction of all right-hand
  sides** and still die.

  Consequences for this hole.
  - The canonical non-honest candidate, the DKKMS gauge labelling `F*` of
    `grassmann-composed-2to2-coarsenings-are-satisfiable`, is the folded zero
    label and reads only its own window. It is cycle blind, so it is dead.
  - Honesty *is* cycle leakage: for a window equation `j` with variables `V`, the
    character `e_j + sum_(i in V) u_i`, where `t_i = <u_i, b>` solves the system,
    lies in `ker(M^T)` and is exactly the test "does `t` satisfy equation `j`".
    So the one family that does leak is the one the established kill already
    caps at `1/2 + w_bad/2`.
  - **Decomposition.** A witness must now satisfy two conditions that can fail
    separately: **(H2a)** cycle leakage at least `(gamma - 2 eta)/4`, hence a
    vertex whose label depends on `Omega(n)` right-hand sides; and **(H2b)** not
    an honest labelling from an equivariant menu of size `exp(o(n/s^2))`.

  **Dead sub-approach, with the exact step.** The natural way to an *absolute*
  bound is decoupling. The lift is a unique game, so an accepted edge has its
  B-label determined by its A-label, and
  `val(U_o) <= sum_a max_(sigma) sum_(e in a) w_e [branch condition at e]`,
  a sum of maxima over constant-size label sets. This bound is local in `b` and
  therefore also gauge blind, and if the branch conditions were fair independent
  coins it would give `1/2 + O((l/deg)^(1/2))` and refute this claim outright.
  It dies at the discarded B-consistency: the folded branch offset `c_e(b)` is a
  function of the window right-hand sides, which sit inside the selector's own
  view, so the selector `g_e(view)(tau) := c_e(view)` makes the branch condition
  true for the folded zero label at every edge and the bound is identically `1`.
  `--mode decouple` of the artifact verifies both halves: `0` violations of the
  inequality over all `2^9` right-hand sides of a tiny instance, and minimum `1`
  of the bound under the offset-cancelling selector.

  **Open need (`H2-absolute`).** An absolute bound on `val(U_o)` for view-local
  `o` on DKKMS YES instances that keeps the B-vertex agreement constraint. This
  is where the Khot--Minzer--Safra Grassmann expansion theorem should enter, and
  it is the last missing piece between the two kills and a refutation of this
  claim.

---
rg: 2
id: trace-separating-k0-nuclear-qd-algebra-with-nonqd-trace
kind: claim
title: Some separable unital nuclear quasidiagonal algebra whose K_0-group separates tracial states has a nonquasidiagonal tracial state
distinct_from:
  qd-nuclear-algebra-with-qd-trace-positive-singular-class: that is the hole this implies; this adds the hypothesis that K_0 separates tracial states (for example real rank zero), under which one nonquasidiagonal trace is enough, so it is in general a stronger statement.
  amenable-traces-on-exact-cstar-algebras-are-quasidiagonal: that is the positive exact residual of X(1); this asks for a failure of it on an algebra that is moreover nuclear, quasidiagonal and K_0-trace-separating.
  bk-rr0-uct-stably-finite-algebras-are-qd: that is the open question whether separable nuclear stably finite real rank zero algebras with UCT quotients are quasidiagonal; this asks for a nonquasidiagonal trace on an algebra that is already quasidiagonal, which by Gabe's theorem forces the UCT to fail.
  stw99-problem-ix1-nuclear-faithful-trace-quasidiagonal: that asks whether a faithful trace makes a nuclear algebra quasidiagonal; this assumes quasidiagonality and asks for a nonquasidiagonal trace, and its quotient reduction lands either in this claim with a faithful trace or in a counterexample to that problem.
  bootstrap-tensoring-cannot-create-qd-trace-positive-class: that is an established permanence theorem showing tensoring with a bootstrap-class factor cannot supply trace separation; it constrains constructions of this claim but decides neither it nor its negation.
  stw07-trace-obstruction-forces-nonqd-trace-and-non-uct: that lists necessary consequences (a nonquasidiagonal trace, a non-UCT quotient) of a witness; this is an existence statement with an additional separation hypothesis, not decided by those consequences.
artifacts:
  - research/artifacts/qd-trace-positive-class-k0-state-form-2026-09-16.md
---

There is a separable, unital, nuclear, quasidiagonal `A` such that

- `K_0(A)` separates tracial states: `tau_* = tau'_*` on `K_0(A)` implies
  `tau = tau'`; and
- some tracial state of `A` is not quasidiagonal.

The main instance of the first condition is real rank zero.  Self-adjoint
elements are then norm limits of finite real combinations of projections, so
a trace is determined by its values on projections (artifact, Proposition 3).

**Why it matters.**  By Proposition 3 of the artifact
(`qd-trace-positive-class-from-k0-separated-nonqd-trace`), such an `A` carries
a singular K_0-class positive on all quasidiagonal traces.  So it solves
`qd-nuclear-algebra-with-qd-trace-positive-singular-class`, and then refutes
STW Problem VII through `stw07-qd-trace-positive-class-kills-qd-extension`.
Conversely, a witness for that hole whose `K_0` separates traces is exactly an
instance of this claim.

**What an instance must look like.**
- **UCT.**  `A` fails the UCT, by Gabe (arXiv:1511.02760v1: amenable traces on
  separable exact quasidiagonal UCT algebras are quasidiagonal).  Let `sigma`
  be any nonquasidiagonal trace.  The trace kernel quotient `A/J_sigma` also
  fails the UCT.  It carries the faithful amenable nonquasidiagonal trace
  induced by `sigma`, and Tikuisis--White--Winter apply, as in
  `stw07-trace-obstruction-forces-nonqd-trace-and-non-uct`.
- **Extreme reduction** (artifact, Theorem 1 and Proposition 4).  The
  nonquasidiagonal trace `sigma` can be taken extreme with
  `pi_sigma(A)'' ≅ R`.  The quotient `B = A/J_sigma` is prime and nuclear,
  its `K_0` separates traces, and it carries the faithful extreme
  nonquasidiagonal trace `sigma_B`.  Either `B` is quasidiagonal, and is then
  an instance of this claim with a faithful extreme separated trace, or `B` is
  a counterexample to STW IX(1).

## Attempts

- **Bootstrap tensoring cannot supply separation.**  If `A` is a
  nonquasidiagonal-trace algebra that is not a witness, then for every unital
  quasidiagonal `D` in the bootstrap class, `K_0(A tensor D)` still fails to
  separate traces (`bootstrap-tensoring-cannot-create-qd-trace-positive-class`).
  So separation cannot be imported from a UCT factor.  This includes
  `Z`-, UHF- and `C(T)`-stabilisation and crossed products by inner
  automorphisms.
- **Real rank zero examples.**  Any instance fails the UCT, but no separable
  nuclear C\*-algebra is known to fail the UCT
  (`nuclear-algebra-without-uct-exists` is open).  So no algebra in the
  current literature can be an instance.  Dies at the UCT.
- **Paths, gluings and mapping tori.**  Subalgebras
  `E ⊆ C([0,1], F)` defined by endpoint conditions were examined: interval,
  dimension-drop and pullback algebras.
  - For a trace `tau` of `F` and a projection `p in M_n(E)`, the path
    `t -> p(t)` is norm continuous.  So `(tau o ev_t)_*([p]) = tau(p(0))`.
  - Hence the K_0-state of `tau o ev_t` is that of a trace of the endpoint
    algebra `ev_0(E)`, pulled back along `ev_0`.  When the endpoint algebras
    have only quasidiagonal traces, no class separates.
  - The mapping torus of an inner automorphism `Ad(e^(2 pi i h))` is
    `C(T, A)`.

  No separation was produced.  This is an examined family, not an
  impossibility theorem.  Details are in
  `notes/qd-nuclear-algebra-with-qd-trace-positiv-swarm-2026-09-16.md`.
- **Crossed products by `Z`.**  For inner `Ad w` the crossed product is
  `A tensor C(T)`, which is covered by the tensoring theorem.  For other
  automorphisms, the new classes from `ker(1 - alpha_*)` on `K_1(A)`
  (Pimsner--Voiculescu) have trace values given by de la Harpe--Skandalis
  determinants along paths from `u` to `alpha(u)`.  No automorphism producing
  a separating class was found.  Open-ended; recorded as a direction, not a
  no-go.
- **Direct sums.**  `A (+) B` is a witness iff `A` or `B` is.  Its traces are
  the convex combinations of traces of the summands, and `K_0` splits.
  Nothing is gained.
- **Literature** (bounded, 2026-09-16).
  - arXiv API searches for quasidiagonal traces and real rank zero found no
    real rank zero or K_0-trace-separating nuclear quasidiagonal algebra with
    a nonquasidiagonal trace.
  - Moradi--Amini arXiv:2606.13924v1 (unrefereed) gives face and permanence
    properties of quasidiagonal traces, not examples.
  - Ozawa arXiv:2609.08892v1 gives a nonquasidiagonal trace on `R`, which is
    not exact.

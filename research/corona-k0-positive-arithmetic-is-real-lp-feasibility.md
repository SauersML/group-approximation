---
rg: 2
id: corona-k0-positive-arithmetic-is-real-lp-feasibility
kind: claim
title: Positive K-zero arithmetic of matrix coronas is finite real LP feasibility, so rank integrality never certifies a mark that a faithful trace keeps
artifacts:
  - research/corona-k0-positive-arithmetic-is-real-lp-feasibility-proof.md
distinct_from:
  finite-corona-dimension-certificate-calculus: that decides a finite list of homogeneous Murray-von Neumann equalities by one rational Farkas certificate; this treats countable systems with weak and strict inequalities, the unit class and existential projections, proves that matrix coronas and all II_1 reduced products solve exactly the same systems, and proves that every system interpretable under a faithful trace is solvable with the mark nonzero.
  matrix-corona-rank-germs-absorb-fixed-depth-leavitt-escape: that exhibits one rank germ satisfying the two families (FDL1) and (FDL2); this proves that every countable rank system whose finite parts are real-feasible is realized, and (FDL1), (FDL2) are its two simplest instances.
  finite-packet-functoriality-has-positive-regular-profile: that finds a positive regular point for the finite-group packet functoriality relations; this replaces packet functoriality by arbitrary Murray-von Neumann relations among projections of any representation in a finite von Neumann algebra, countably many at once, with inequalities.
  matrix-corona-projection-monoid-is-rank-germs: that classifies the projection monoid V(Q_d) as rank germs; this determines the positive-existential theory with inequations of that monoid and shows that it does not see integrality.
  kazhdan-mapping-tori-have-proper-stably-finite-radical: that kills certificates valid in every stably finite target, for Kazhdan mapping tori; this isolates what the integrality of matrix-corona K-zero adds over II_1 reduced products, namely nothing expressible by positive rank arithmetic.
---

**ESTABLISHED (written proof; not Lean-verified).**  This is an obstruction
to a class of approaches to `property-t-free-leavitt-full-mf-radical`.  It is
not a refutation of the goal, and the goal stays OPEN.
Proof: `corona-k0-positive-arithmetic-is-real-lp-feasibility-proof`.

## Rank systems

Fix a countable set `W` of projection variables and a unit symbol `u`.  A
**rank condition** is a formula

```text
sum_w a_w x_w   REL   sum_w b_w x_w,          REL in { = , <= , < },     (KLP0)
```

with nonnegative integer coefficients, finitely many nonzero, where `u` may
occur on either side.  A **rank system** `Sigma` is a countable set of rank
conditions that contains, for every `w in W`, a bound `x_w <= k_w u` with
`k_w` a positive integer.  Auxiliary variables are allowed, so every
positive-existential rank statement with inequations ("there are projections
`q_1,...,q_m` such that ...") is a rank system.

A rank system is interpreted in three ways.

- **(Cor)** In the projection monoid `V(Q_d)` of a norm matrix corona
  `Q_d = prod M_(d_n)(C) / directSum M_(d_n)(C)`.  Here `u` is `[1]`, `+` is
  direct sum, `<=` is Murray--von Neumann subequivalence (the algebraic
  order), and `a<b` means `a<=b` and `a!=b`.
- **(II)** In `V(A_N)`, where `A_N = l^infty(N)/c_0(N)` is the norm reduced
  product of a II_1 factor `N`, with the same conventions.
- **(R)** Over the reals, as a vector `y in [0,infty)^W` with `y_u=1` and the
  usual order.

## Theorem (KLP)

For every rank system `Sigma` the following are equivalent.

1. `Sigma` has a (Cor) interpretation in some norm matrix corona `Q_d`.
2. Every finite subsystem of `Sigma` has a real solution.
3. `Sigma` has a (II) interpretation for some II_1 factor `N`.
4. `Sigma` has a (II) interpretation for every II_1 factor `N`.

In addition:

5. If (1) holds for `d`, then it holds for every `d'` with `d_n | d'_n` for
   all `n`.
6. If the whole of `Sigma` has one real solution `y`, then the (Cor)
   interpretation can be chosen with coordinate rank lifts satisfying
   `rank(p_(w,n))/d_n -> y_w` for every `w`.  The (II) interpretation can
   be chosen with `tau(p_(w,n)) = y_w` for all `n`.

The gap between (2) and real solvability of the whole system is only
compactness, and it is genuine.  The system `{M x_a <= u : M>=1}`
together with `0<x_a` is (FDL1) of
`matrix-corona-rank-germs-absorb-fixed-depth-leavitt-escape`.  Every finite
part of it is real-feasible, but the whole system is not.  Divisibility at
every fixed depth, (FDL2), is the second instance.  Finite infeasibility is
decided by the rational alternative theorem.  The equality-only case is
`(FDC3)` of `finite-corona-dimension-certificate-calculus`.

In words: **the positive rank arithmetic of a matrix corona is that of a
nonstandard real line.  Integrality of rank, parity, divisibility,
pigeonhole counts and bounded multiplicities contribute nothing that a real
dimension function does not already give.**

## Corollary (faithful-trace transfer)

Let `G` be a group and `z in G`.  Let `(M,tau)` be a finite von Neumann
algebra with a faithful normal tracial state, and let
`pi:G->U(M)` be a homomorphism with `pi(z)!=1`.

Suppose `Sigma` is a rank system containing a condition `0 < x_z`.  Suppose
also that it has a **pi-interpretation**: projections `P_w` in `M_(k_w)(M)`
satisfying `Sigma` in `V(M)`, with the same conventions and
`P_z != 0`.  Then `Sigma` has a (Cor) interpretation with the class of
`x_z` nonzero, and its normalized ranks converge to `tau(P_w)`.

For `Delta = St_20(L_(F_2)(1,2))`, the mark `z = x_13(s_1t_1)` and
`pi = lambda`, the active projection `P_z = (1-lambda(z))/2` has
`tau(P_z) = 1/2`.

## What this kills

Call a **rank certificate** for `z in Rad_MF(G)` a scheme with two parts.
First, to every norm-corona homomorphism `rho:G->U(Q_d)` with `rho(z)!=1`
it attaches a rank system `Sigma` and projections over `Q_d` satisfying it,
with `x_z` sent to the active spectral projection of `rho(z)` and
`0<x_z` in `Sigma`.  Second, it proves that `Sigma` has no (Cor)
interpretation.  Call the scheme **pi-interpretable** when the same
construction, run in `(M,pi)`, produces projections satisfying the same
`Sigma`.

By the Corollary, **no pi-interpretable rank certificate exists, for any
finite von Neumann representation that keeps `z`.**  For `Delta`, the regular
representation keeps `z`.  This kills, uniformly:

- **Rank-pigeonhole and orbit-counting arguments.**  Many orthogonal
  equivalent translates of the marked carrier inside `1` form a
  (FDL1)-type system.
- **Parity and dyadic divisibility arguments**, including the forced
  divisibility of `[p_z]` by `2^k` coming from dihedral subgroups.  These
  are existential rank conditions.
- **Finite-packet multiplicity bookkeeping** of every kind: restriction,
  conjugacy, central cuts, orthogonal decomposition, and countable
  refinement towers.  This contains the regular-profile obstruction of
  `finite-packet-functoriality-has-positive-regular-profile`.
- **Cancellation and stable-finiteness steps** used only through `V`:
  `x = x + w` forces `w = 0`, and this is equally true under `tau`.
- **Mixtures of all of the above with normalized-rank (MF character) data.**
  By (6) the realization can have limiting normalized ranks equal to the
  regular values `tau_lambda(P_w)` for all `w` at once.  An example is the
  Haar-profile ranks of all spectral projections of all finite root-module
  packets.

**Invariant.**  The real LP feasibility of the finite parts of the rank
system.  Equivalently, the positive-existential type of the projection tuple
in `V`.

**Step where every member dies.**  The final arithmetic inference
"`Sigma` forces `[p_z] = 0`".  It fails at the diagonal rational
realization of the trace vector `y_w = tau_lambda(P_w)`, which satisfies
`y_z = 1/2`.

**II_1 twin.**  Let `N = L(Delta * Z)`.  This is a II_1 factor, because
`Delta * Z` is ICC, and it contains `L(Delta)` with the trace `tau_lambda`.
Then

```text
Delta -> U(A_N),      g |-> [(lambda(g))_n],
```

is an injective homomorphism into a unital stably finite C-star algebra with
cancellative projection monoid.  By (KLP), `A_N` and the matrix coronas
satisfy the same rank systems.

## What survives

A Property-(T)-free proof must use a property of the matrix coronas `Q_d`
that fails in `A_N`.  By (KLP), that property is not a positive-existential
rank statement.  What remains is:

- **(S1) Negated rank statements.**  Examples are indivisibility or odd
  rank, which say that no `y` satisfies `x = 2y`.  In `V(A_N)` every class is
  divisible, while in `V(Q_d)` the germ of `(1,1,1,...)` is not.  Neither
  monoid has a minimal nonzero class: `(1,0,1,0,...)` lies strictly below
  `(1,1,1,...)`.  So minimality arguments are unavailable in both, and only
  negated statements separate them.
- **(S2) Non-K-zero finite-dimensional structure.**  The model example is
  stable finiteness of the Hilbert--Schmidt adjoint corona
  `prod B(M_(d_n),HS)/directSum`, which is the finite-dimensional input of
  the Kazhdan transport in `non_mf_groups_exist.tex`.  Its `A_N` analogue
  `prod B(L^2 N)/directSum` is properly infinite.
- **(S3) Relations that are false under `tau_lambda`.**  The (BLAMR) rows of
  `binary-leavitt-atomic-morita-return` are an example: in `A_N` they would
  force `[p] = 2[p]` on the marked carrier.  So do same-reservoir returns and
  finite supercritical branching systems on fixed classes.  Such a relation
  fails for the regular model in `A_N`.  So its derivation must use a
  property of `Q_d` that fails in `A_N`, of type (S1), of type (S2), or of
  some other non-positive kind.  By (KLP), positive rank arithmetic combined
  with properties shared with `A_N` never derives it.

This makes the sentence "a successful projection/K-zero proof must produce
a finite closed supercritical branching system on fixed classes", in
`matrix-corona-rank-germs-absorb-fixed-depth-leavitt-escape`, an exact
criterion.  The supercritical system must be real-infeasible on a finite
part, so it must contain a relation that fails under `tau_lambda`.

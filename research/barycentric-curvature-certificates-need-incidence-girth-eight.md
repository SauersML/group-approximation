---
rg: 2
id: barycentric-curvature-certificates-need-incidence-girth-eight
kind: claim
title: A nonpositive-curvature certificate on the barycentric complex of local data needs every incidence cycle of nonscalar variables to have at least four contexts, and functional subdivision cannot supply them
distinct_from:
  commuting-nonscalar-readouts-force-coset-four-cycles: that caps the coset girth of one commuting pair inside one context group; this sums the link conditions of all three vertex types around an incidence cycle and turns that cap into a lower bound on cycle length.
  slofstra-zhang-high-girth-phase-survival: that proves phase survival for abelian solution groups of high incidence girth by planar pictures; this is a necessary condition for the metric developability certificate for arbitrary finite local groups, not a survival theorem.
  finite-readout-bcs-decoders-are-phase-surviving-local-colimits: that proves acyclic gluings never survive for sources without finite-dimensional models; this bounds from below the cycles that a curvature certificate of survival would need.
---

**ESTABLISHED** by `barycentric-curvature-certificate-girth-bound-proof`.
Not independently reviewed; elementary, no novelty claimed.

## Setting

Let `D` be finite local data for a Boolean constraint system `B` and `n`, as in
`finite-readout-bcs-decoders-are-phase-surviving-local-colimits`: finite
groups `J <= H_v <= A_c` for `v in V_c`, with `J` central of order `n`, and
readouts `y_v in C[H_v] p_omega`. Order the diagram as a poset

```text
A_c < H_v  whenever v in V_c,     A_c < J,     H_v < J,
```

so smaller groups sit at larger elements, as for a simple complex of groups.
The poset has a maximum `J`, so its geometric realization `X(D)` is a cone. Its
2-simplices are the chains `A_c < H_v < J`, one per incidence `(c, v)`.

A **barycentric curvature certificate** for `D` assigns to each incidence
`t = (c, v)` a geodesic triangle in the Euclidean or hyperbolic plane, with
angles `alpha_t`, `beta_t`, `gamma_t` at `A_c`, `H_v`, `J`, so that
`alpha_t + beta_t + gamma_t <= pi`, and every injective cycle in each of the
following metric graphs has length at least `2 pi`:

- **at `A_c`:** vertices `A_c/H_v` for `v in V_c` and `A_c/J`, with an edge of
  length `alpha_(c,v)` from `gH_v` to `gJ`;
- **at `H_v`:** vertices `{c : v in V_c}` and `H_v/J`, with an edge of length
  `beta_(c,v)` from `c` to each `hJ` (complete bipartite);
- **at `J`:** the incidence graph `Inc(D)`, with edge `(c, v)` of length
  `gamma_(c,v)`.

These graphs are the geometric links of the local developments of the simple
complex of groups over `X(D)`. A certificate is exactly a piecewise
constant-curvature (`kappa <= 0`) structure on `X(D)` whose local developments
satisfy the link condition. This is the hypothesis of the developability
theorem for nonpositively curved simple complexes of groups; the conclusion
that the local groups, and hence `J`, inject into `Lambda(D)` is not proved
here.

## Statement

**(CB1) Cycle inequality.** Suppose `D` has a barycentric curvature
certificate. Let

```text
c_1 - v_1 - c_2 - v_2 - ... - c_k - v_k - c_1
```

be a cycle in `Inc(D)` with `k >= 2`, distinct contexts, distinct variables and
`|H_(v_i) : J| >= 2` for every `i`. Put `m_i = m(H_(v_(i-1)), H_(v_i))`,
computed in `A_(c_i)` (indices mod `k`), as in
`commuting-nonscalar-readouts-force-coset-four-cycles`. Then

```text
2 + sum_(i=1)^k 1/m_i  <=  k.                                    (CB1)
```

**(CB2) Nonscalar cycles are long.** If moreover every readout `y_(v_i)` is
nonscalar, then `m_i <= 2` for all `i` by (CN3). If `r` of the `m_i` equal `1`,
then

```text
k >= 4 + r.                                                     (CB2)
```

So every incidence cycle of nonscalar variables has at least four contexts,
i.e. length at least 8 in `Inc(D)`. In particular a certificate forbids two
contexts that share two nonscalar variables, and three contexts pairwise
sharing nonscalar variables.

**(CB3) Functional subdivision does not help.** Subdivide a cycle with `k`
contexts by inserting `s` contexts, each forcing a new variable to be a function
of an old one (`y_(v') in C*(1, y_v)`, e.g. equality). The result has
`k' = k + s` contexts, and by (CN2) at least `s` of its `m`-values equal `1`. So
(CB2) for the subdivided cycle gives `k + s >= 4 + s`, i.e. `k >= 4`. A cycle
with fewer than four contexts among nonscalar variables stays obstructed
however it is subdivided.

## Scope

- This bounds only the barycentric realization of the minimal diagram
  `J -> H_v -> A_c`. Adjoining extra intermediate subgroups as diagram vertices
  leaves `Lambda(D)` unchanged but changes the realization, and is not covered.
- It is a necessary condition for one certificate of phase survival, not for
  survival itself. Survival can hold without any curvature certificate.
- By (LC4) and (LC3), sources without finite-dimensional models need cycles and
  have no finite-dimensional certificate; so for the tracial non-`R^U` source
  this lower bound on cycle length is a constraint on any geometric certificate
  of this kind.

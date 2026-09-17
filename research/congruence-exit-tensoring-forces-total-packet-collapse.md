---
rg: 2
id: congruence-exit-tensoring-forces-total-packet-collapse
kind: claim
title: Tensoring with congruence exits turns any bounded-type placement of packet mass into total packet collapse
distinct_from:
  toeplitz-self-embedding-fixes-unbounded-congruence-types: that builds the unbounded stationary exits and says they do not refute an estimate whose input is positive forbidden mass; this tensors those exits onto an arbitrary positive-mass representation, keeps a fixed fraction of that mass, and so does refute every such estimate unless its premise is empty.
  high-type-irreducibles-retain-finite-packet-mass: that needs a residually finite quotient tower on which the packet survives; this needs no survival hypothesis and applies to every tracial representation, including Connes-embeddable non-finite ones.
  commutant-density-forces-bounded-type-mass: that compares density with bounded-type mass inside one representation; this proves that bounded-type mass is destroyed by one exact tensor factor while packet mass is not.
  hs-schur-toeplitz-root-defect-collapse: that is an open qualitative collapse target for one root mark; this proves that the placement form of the parity density target is equivalent to such a total collapse for the whole embeddable class.
  canonical-packet-traces-do-not-place-old-commutant-density: that dilutes with regular quotients of a residually finite old group; this uses a single exact congruence factor of the non-residually-finite Toeplitz base and preserves the class of the input representation.
---

**Setting.** Let `G` be a discrete group, `Lambda<=G` an infinite
property-`(T)` subgroup, `B<=G` finite, and `z=z*=z^2 in C[B]`.  For a
tracial representation `pi:G->U(M)` (finite von Neumann algebra, faithful
normal tracial state `tau`) put

```text
q(pi)=tau(pi(z)),      mu_K(pi)=tau(pi(p_<=K)),                 (CET0)
```

with `p_<=K in C*_max(Lambda)` from
`kazhdan-bounded-types-form-central-summand`.  Let `N_K` be the number of
irreducible unitary types of `Lambda` of degree at most `K`
(`kazhdan-bounded-unitary-types-are-finite`).

An **exit family** is a sequence of finite-dimensional unitary
representations `rho_j:G->U(m_j)` such that every irreducible constituent
of `rho_j|Lambda` has degree at least `D_j`, where `D_j->infinity`, and

```text
beta_j=dim (C^(m_j))^B / m_j >= beta>0.                          (CET-H)
```

**(CET1) Tensor lemma.** For every tracial `pi`, every `j` and every `K`,

```text
q(pi (x) rho_j) >= beta_j q(pi),
mu_K(pi (x) rho_j) <= N_K K^4 / D_j^2.
```

Also `pi (x) rho_j` is finite-dimensional if `pi` is, and
Connes-embeddable if `pi` is.

**(CET2) Placement is total collapse.** Let `C` be the class of all
finite-dimensional representations of `G`, or the class of all
Connes-embeddable tracial representations of `G`.  Suppose that for every
`q_0>0` there are `K(q_0)` and `f(q_0)>0` with

```text
q(pi)>=q_0  ==>  mu_(K(q_0))(pi)>=f(q_0)        for all pi in C.
```

Then `q(pi)=0` for every `pi in C`.  The converse is trivial, because the
premise is then empty.

**(CET3) Density form.** In the finite-dimensional class, suppose every
`pi` with `q(pi)>=q_0` has `dim End_Lambda(pi)/dim(pi)^2>=g(q_0)>0`.  This
covers `(PCD1)` at zero energy with `g=c q_0^2`.  Then every
finite-dimensional unitary representation of `G` kills `z`.

**(CET4) Toeplitz instance.** Take `Gamma=EL_r(T)` and `alpha` as in
`toeplitz-self-embedding-fixes-unbounded-congruence-types`.  Let
`Lambda=Gamma`, let `B<=Gamma` be any finite subgroup (for example
`iota(B_f)` from `schur-child-crosses-toeplitz-compressor`), and let `G` be
the ascending HNN group with any extra relators that hold in the exits
below.  The exits are `rho_q`, the augmentation representation
`eta_q` of `SL_r(F_q)` inflated to `Gamma`, with `t |-> 1`.  They form an
exit family with `D=m=N_q-1` and

```text
beta_q >= 1/|B| - 1/(N_q-1).
```

**Consequences.**

- Take any cell design for the parity compressor that admits these exits.
  Then the scalar placement form of `(PCD1)` ("positive forbidden mass
  forces positive `p_<=K` trace") holds on finite-dimensional
  representations if and only if every such representation kills `z`.  It
  holds on Connes-embeddable representations if and only if every
  Connes-embeddable representation kills `z`.
- In the embeddable class, that total collapse already contradicts
  hyperlinearity, since `tau_can(z)=tau_B(z)>0`.  It is also strictly
  stronger: it kills `z` in every finite-dimensional representation, which
  (for finitely generated `G`, by Malcev) means `z` dies in every finite
  quotient.
- So no bounded-type compiler, covariance placement or separator estimate
  can give `(PCD1)` in any representation class closed under exact
  finite-dimensional tensoring, unless it first proves total collapse.
  The only escape is a coefficient cell whose relators fail on every
  congruence exit.
- The final sentence of
  `toeplitz-self-embedding-fixes-unbounded-congruence-types` has to be read
  sharply.  The exits cannot be excluded by using positive forbidden mass
  as an input, because positive mass survives tensoring with them.
- Scope. This covers masses of projections in `C[B]` for a finite subgroup
  `B`.  It does not cover coefficient-ring reservoir quantities such as
  `tau(P_f)` from `toeplitz-defect-needs-square-decoding`.  It also does
  not cover approximate microstate densities at positive energy, where
  `mu_K` is not defined.

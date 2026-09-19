---
rg: 2
id: one-dimensional-address-rules-have-periodic-models
kind: claim
title: Every nonempty finite-state one-dimensional payload address rule has an exact periodic active matrix model
distinct_from:
  baumslag-address-geometric-stationary-profile: that gives explicit finite-field quotients for the nonlocal binomial Baumslag address host; this proves the general periodic firewall for every finite-alphabet finite-window rule transported by one shift.
  periodic-bs-clock-defeats-spectral-first-hit-checksum: that uses cyclic spectral clocks for Baumslag--Solitar doubling; this uses diagonal packet PVMs and the periodic-point theorem for one-dimensional shifts of finite type.
  exact-first-hit-ladder-kills-regular-carrier: that rules out a trace-functorial infinite persistent ladder in a group factor; this produces exact finite-dimensional models with nonzero active payload and periodic supports.
  single-selected-atom-hs-escape: that asks for a payload-dependent escape from every reached shared-variable carrier; this refutes the entire finite-state one-shift local-rule class whenever its active fiber is nonempty.
---

**ESTABLISHED PERIODIC FIREWALL.**  Let `A` be a finite packet alphabet and
let `X subset A^Z` be defined by finitely many translation-invariant allowed
windows of radius `R`.  Model the packet by a PVM `(E_a)_(a in A)`, let `T`
be the address shift, and write

```text
E_(n,a)=T^n E_a T^(-n).                               (OPA1)
```

Suppose the proposed payload-conditional relations have the following
standard local form: on the active payload corner `F=1`, products

```text
product_(j=-R)^R E_(n+j,a_j)                          (OPA2)
```

vanish exactly for the forbidden windows, while on `F=0` all these rows are
vacuous.  Extra finite packet labels may be absorbed into `A`.  If the active
classical fiber `X` is nonempty, then the presentation has an exact
finite-dimensional active model with `F=1`.

Indeed, form the finite directed de Bruijn graph whose vertices are allowed
overlap blocks and whose edges are allowed windows.  A point of `X` gives a
bi-infinite path.  Some vertex repeats in the forward half, hence the graph
contains a directed cycle.  Repeating that cycle gives a periodic point
`x in X` of some period `L`.

On `H=ell^2(Z/LZ)`, let

```text
T delta_n=delta_(n+1),
E_a delta_n=1_(x_n=a) delta_n,
F=I.                                                   (OPA3)
```

Equations `(OPA1)` and every PVM/window relation hold exactly.  Any additional
finite internal label that enters only through the same window table has
already been absorbed into the alphabet `A`.

Every projection or reducing hull defined equivariantly from a fixed finite
window is periodic:

```text
D_(n+L)=D_n.                                          (OPA4)
```

Consequently no consequence of these exact rows can make a nonzero active
support produce infinitely many pairwise orthogonal translates.  Nor can it
give a strict exact recurrence

```text
tau(Q_(n+1)) >= (1+gamma)tau(Q_n),       gamma>0,      (OPA5)
```

on a periodic/reached carrier: after one period `(OPA5)` would imply
`tau(Q_n)>=(1+gamma)^L tau(Q_n)`, forcing `Q_n=0`, contrary to `F=1` and any
positive active seed.

This covers finite-state lamplighter packets, one-shift HNN address tables,
and every finite collection of classical prefix/first-hit labels compiled as
a one-dimensional local rule.  The Baumslag affine prefix is not literally a
fixed finite-alphabet SFT, but
`baumslag-address-geometric-stationary-profile` supplies the analogous exact
finite-field periodic models, with carrier mass decaying geometrically rather
than escaping supercritically.  Cyclic Baumslag--Solitar spectral addresses
are separately covered by
`periodic-bs-clock-defeats-spectral-first-hit-checksum`.

The scope is sharp.  The theorem does not cover a genuinely branching
strongly aperiodic rule, a noncommutative infinite packet with no periodic
active representation, or a relation whose active fiber has no exact finite
model.  But the last alternative is already the load-bearing matrix-only
statement: a successful conditional gadget must prove that every nonzero
active finite-dimensional realization pays a dimension-uniform defect while
the `F=0` tracial model survives.  One-dimensional finite-state addressing
cannot supply that statement because `(OPA3)` is a zero-defect active model.

DERIVATION
one-dimensional-periodic-address-proof

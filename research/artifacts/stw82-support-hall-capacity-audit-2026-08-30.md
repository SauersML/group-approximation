---
rg: 2
title: STW LXXXII support-local Hall capacity and minimal-support obstruction audit (2026-08-30)
kind: artifact
---

# What total tracial mass misses

The support-local coupled-cover theorem reconstructs an outgoing order-zero
map once its cutters cover the actual positive support `h`.  Tracing `h`
gives the previously recorded necessary inequality

```text
sum_v tau(h_v)<=d.
```

That is only an amplitude count.  Exact norm coverage is stronger: if
`(1-s_v)h_v=0`, then `s_v` acts as one on the entire range projection
`p_v=s(h_v)` in the tracial von Neumann algebra.  Charging these range
projections to pairwise orthogonal label cutters gives

```text
sum_v tau(p_v)<=d.
```

Allowed-label sets and label-capacity projections give the corresponding
weighted Hall inequalities.  At approximation scale `eta`, the same proof
applies to `1_[lambda,1](h_v)` with the loss `1-eta/lambda`.  Thus small
amplitudes can be discarded only below the error scale; every spectral
piece bounded away from zero consumes support capacity.

The two scalar supports `h_I=h_Q=1/2` expose the gap sharply.  Their
amplitudes are complementary and have total trace one, but both occupy the
same support projection.  One label cannot cover both with orthogonal
cutters, and the cover defect is at least `1/2`.  Therefore a bound of the
form

```text
total outgoing tracial amplitude <= max(p,q)+1
```

cannot by itself construct the coupled cover required by the local gluing
theorem.

# What support traces still miss

Support-projection Hall capacity is necessary but not sufficient.  For
minimal projections, exact quasicentrality forces every cutter to act by a
scalar on its assigned support.  Orthogonality then forbids the same label
at two nonorthogonal supports.  Conversely, a graph colouring supplies
projection cutters.  The exact coupled-cover number is therefore the
chromatic number of the nonorthogonality graph, even though the construction
is allowed to split each original support among many operator-valued
cutters.

Three pairwise nonorthogonal rank-one projections in `M_2` give the smallest
separation relevant to two-label gluing.  Their total support trace is
`3/2<=2`, and every subset satisfies the two-copy span-capacity inequality,
but their incidence graph is `K_3`, so three labels are required.  Compactness
of the finite-dimensional positive unit ball makes this obstruction robust
under simultaneous small cover, commutator, and orthogonality errors.

# Exact boundary for the extension problem

These are local no-go theorems for a fixed outgoing family, not a
counterexample to the nuclear-dimension maximum formula.  Nuclear
approximations may replace their outgoing maps, move spectral mass below the
error scale, or arrange different support incidence.  The results do show
that arbitrary extension geometry cannot be reduced to a single scalar
capacity estimate, nor even to all tracial span-capacity inequalities.

After the separable, stable, essential reduction, a universal maximum proof
using support-local coupled covers must additionally produce an incidence
matching: above every relevant spectral threshold, the same-labelled
support pieces must avoid nonorthogonal odd cycles (more generally, admit
the desired graph colouring).  In noncommutative targets this is information
not seen by traces.


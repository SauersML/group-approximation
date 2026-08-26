---
rg: 2
id: endpoint-whitehead-profile-has-maximal-gram-overlap
kind: claim
title: Iterated endpoint Whiteheads give a reversible profile with maximal incoming Gram overlap
artifacts:
  - research/endpoint-whitehead-profile-gram-proof.md
distinct_from:
  middle-pauli-probes-leave-three-hecke-classes-untyped: that isolates the three endpoint classes and observes that matching endpoint legs return the mark only at the third prefix scale; this adds fresh endpoint Whiteheads and audits the resulting finite moved-source profile.
  paid-cut-has-moving-hecke-source-or-detector: that produces one positive moving source or one paying detector; this asks whether iterating the detector branch itself creates finite-state rank expansion and proves that the literal full-Gram transports are reversible rather than branching.
  same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps: that computes the adjacent swaps on the original three Pauli arms and leaves the unequal native occurrence seam; this performs the analogous construction at an extracted endpoint root and tracks the complete source/range Grams of the induced profile automaton.
---

**ESTABLISHED SCOPED PROFILE FENCE.**  Let `r_1,r_2,r_3` be three spare
endpoint coordinates, where `r_3` may be the actor endpoint `2` or `4` at
which one of the three exceptional signed-Hecke detector classes has been
returned.  Put

```text
a_m=s_1t_(0^m),                 b_m=s_(0^m)t_1,
A_m=x_(1,r_m)(a_m),             B_m=x_(r_m,3)(b_m).
```

Then `[A_m,B_m]=z=x_13(s_1t_1)` for all `m`.  The adjacent prefix
Whiteheads on `r_m,r_(m+1)` carry the whole occurrence at scale `m` to the
one at scale `m+1`; they satisfy the two involution relations and the
Coxeter braid.  Thus the third-scale endpoint return can be moved to either
earlier scale, provided the signed source and the complete detector/probe
occurrence are conjugated with it.

This produces exact full-Gram edges, but no finite-capacity expansion.
For a source projection `Q` and each profile word `h` in the resulting
`S_3`, set

```text
Q_h=hQh^(-1).
```

For an adjacent generator `s_i`, its compressed edge is

```text
T_(i,h)=Q_(s_i h)s_iQ_h=s_iQ_h,
T_(i,h)^*T_(i,h)=Q_h,
T_(i,h)T_(i,h)^*=Q_(s_i h).                         (EWP1)
```

Each target in the two-generator Cayley profile has two incoming edges.
Both incoming range projections are the *whole same* target `Q_k`.  Hence
their cross Gram is maximal: if `e,f` are the two incoming edges at `k`,

```text
T_eT_e^*=T_fT_f^*=Q_k,
||(T_e)^*T_f||_2^2=tau(Q_k).                         (EWP2)
```

Equivalently the incoming row operator satisfies

```text
[T_e T_f][T_e T_f]^*=2Q_k.                           (EWP3)
```

Consequently the adjacency matrix has the formal Perron--Frobenius value
`2` only when one counts two completely overlapping copies.  The
Gram/Bessel error is then exactly the whole source mass.  Retaining only
one incoming edge at each target gives a permutation profile with spectral
radius `1`.  Neither choice yields a capacity contradiction.

The remaining reservoir freedom is also exact, rather than an approximation
loss.  After removing the adjacent label swaps, the two Whitehead factors
may be any involutions `V_1,V_2` satisfying the `S_3` braid.  The regular
representation of `S_3` supplies a finite exact model with nontrivial such
factors.  Along the moved charts the edge gauges are the coboundaries
`V_(s_i h)V_h^(-1)` and telescope to the identity around every profile
relator.  Conjugating the signed source therefore moves, rather than fixes,
the gauge frame.

Splitting `Q_k` into genuinely orthogonal incoming ranges would be new
information.  Operator-norm payment by one detector gives neither positive
normalized trace for all branches simultaneously nor orthogonality of their
spectral supports.  The exact return `[A_m,B_m]=z` only identifies the
product root; it gives no range-Gram separation.  Thus iterating the finite
detector types cannot replace the missing unequal native occurrence unless
an additional ordinary relation supplies proper subranges with small
cross-Grams in one fixed source frame.

This is a scoped exact consequence of the endpoint occurrence table, not a
finite-dimensional representation of the full Steinberg group.  No
Property `(T)`, canonical trace, literature theorem, local computation, or
Lean compilation is used.

DERIVATION
endpoint-whitehead-profile-gram-proof

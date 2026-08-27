---
rg: 2
id: uncoupled-spectator-cannot-create-first-chord
kind: claim
title: An uncoupled group spectator cannot create a nonuniform first-chord sign
distinct_from:
  common-corner-literal-contexts-stop-at-bass-serre: that rules out a completed no-CE atlas in every finite graph-of-finite-groups corner; this rules out even one chord in an arbitrary direct-product spectator extension when the frozen separators generate the root matrix block and the requested conditional table is nonuniform.
  chord-regauging-is-relative-commutant-feasibility: that identifies the common-relative-commutant interpolation problem in a finite matrix corner; this computes the relative commutant and its canonical conditional traces after adjoining an arbitrary uncoupled group factor.
  infinite-edge-common-commutant-for-first-chord: that permits a genuinely coupled infinite-edge or non-Bass--Serre extension; this proves that replacing such coupling by a direct-product spectator cannot work.
---

Let `K` be finite and let `q C[K]q isomorphic to M_D(C)` be a simple
corner.  Let `A_0,A_1` be star subalgebras of that root block satisfying

```text
A_0 vee A_1=M_D(C).                                    (USC1)
```

For an arbitrary countable group `H`, regard the root corner inside

```text
q C[K times H]q = M_D(C) tensor C[H].                  (USC2)
```

If a self-adjoint involution `Z` in `(USC2)` commutes with both `A_0` and
`A_1`, then

```text
Z=I_D tensor z                                           (USC3)
```

for a self-adjoint involution `z in C[H]`.  Consequently, with
`p=(1+Z)/2`, every nonzero root projection `e in M_D(C)` has the same
canonical conditional plus weight:

```text
tau(e p)/tau(e)=tau_H((1+z)/2).                         (USC4)
```

In particular, suppose a proposed first-chord construction asks for the
piecewise group transports `(IEC2)--(IEC3)` from endpoint signs `X_i` to
`Z`.  Conjugacy preserves the canonical group trace, so a necessary
condition is that all prescribed conditional fractions

```text
tau(e_(i,s)(1+X_i)/2)/tau(e_(i,s))                     (USC5)
```

are one common number, independent of `i,s`.  If the chord table is
nonuniform, no direct-product spectator `H` works -- finite, free,
nonamenable, property `(T)`, or otherwise.

Thus adjoining a non-virtually-free factor to the finite packet is not a
candidate for the first cyclic signed-Hecke chord.  The new group must couple
its infinite directions to the root matrix coordinates so that the common
relative commutant is not a tensor spectator.  Equivalently, the minimal
surviving holonomy equation is to construct an algebraic projection

```text
p in q C[Gamma]q intersect A_0' intersect A_1'          (USC6)
```

whose conditional canonical traces on the separator atoms equal the
nonconstant endpoint table, together with the finite group-translate
equivalences in `(IEC2)--(IEC3)`.


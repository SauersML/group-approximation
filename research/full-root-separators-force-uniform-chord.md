---
rg: 2
id: full-root-separators-force-uniform-chord
kind: claim
title: Full root separators forbid a nonuniform chord in every tracial extension
distinct_from:
  chord-regauging-is-relative-commutant-feasibility: that gives the algebraic common-commutant criterion and notes scalarity inside the finite root block; this adds a trace obstruction which persists in every finite tracial over-algebra even when the common relative commutant becomes infinite-dimensional.
  uncoupled-spectator-cannot-create-first-chord: that computes the relative commutant for a direct-product spectator; this needs no product structure and rules out genuinely coupled Hecke extensions as well when the requested conditional table is nonuniform.
  root-block-piecewise-transport-cannot-host-nonce-bcs: that forces some context projection to escape the finite root block; this proves that block escape alone cannot repair a chord whose frozen separators generate that block.
---

Let `(N,tau)` be a finite tracial star algebra (or finite von Neumann
algebra) containing a unital copy of `M_D(C)`.  Let `A_0,A_1` be star
subalgebras of that copy with

```text
A_0 vee A_1=M_D(C).                                    (FRT1)
```

If `p in N` is a projection commuting with `A_0` and `A_1`, then for every
root projection `e in M_D(C)`,

```text
tau(ep)=tau(e) tau(p)/tau(1).                           (FRT2)
```

Equivalently, the conditional `p`-weight is constant on every nonzero root
atom.  This remains true even if `M_D(C)' intersect N` is diffuse or
non-Connes-embeddable.

Apply this to a proposed first signed-Hecke chord in `q C[Gamma]q`, with the
normalized canonical corner trace, and put `p=(q+Z)/2`.  If the endpoint
separator algebras generate the root matrix block and the piecewise
transports `(IEC2)--(IEC3)` exist, then all endpoint conditional plus
fractions must coincide:

```text
tau(e_(i,s)(q+X_i)/2)/tau(e_(i,s))
 =tau(p)/tau(q),              for every i,s.            (FRT3)
```

Therefore a nonuniform endpoint table cannot be closed while both separator
algebras stay fixed -- in **any** group extension, including a genuinely
coupled non-Bass--Serre or nonhyperlinear one.

This changes the minimal first-cycle interface.  For a nonuniform chord, it
is not enough to manufacture a larger common relative commutant.  Before the
chord is installed, the construction must arrange that

```text
A_0 vee A_1 is a proper subalgebra of the escaped corner,                (FRT4)
```

with enough distinct relative-commutant central blocks to carry the
different conditional fractions, or it must alter one of the previously
frozen separator partitions.  Any route retaining `(FRT1)` and asking only
for a coupled projection `p` is inconsistent whenever its table is
nonuniform.

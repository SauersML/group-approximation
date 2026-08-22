---
rg: 2
id: packet-retraction-evaluates-hecke-collision-atlas
kind: claim
title: A packet retraction evaluates every Hecke collision atlas in finite dimension
distinct_from:
  augmentation-one-corner-retains-a-character: that uses scalar augmentation when the corner unit has augmentation one; this applies to nontrivial primitive-type corners of augmentation zero by retracting the ambient group onto the whole finite packet.
  root-block-piecewise-transport-cannot-host-nonce-bcs: that excludes an atlas already contained in the finite root corner; this shows that every atlas in a much larger algebraic corner descends to that root corner whenever the ambient group retracts onto the packet.
  primitive-packet-corner-is-matrix-over-hecke-atom: that gives the Morita normal form over the rank-one Hecke algebra; this proves that its coefficientwise finite evaluation preserves every coupled collision-block equation.
  edgeful-one-ghost-escape-avoids-term-recurrence: that constructs the local rank-two escape and leaves a coefficient-link C(4)-T(4) construction open; this rules out closing the global chord by any such construction whose ambient group retains the standard packet retraction.
---

Let `K<=Gamma` be finite and suppose there is a group retraction

```text
r:Gamma -> K,                    r|K=id_K.                (PRE1)
```

Let `p in C[K]` be any projection, including a primitive type projection or
the hyperoctahedral common-reflection projection `q`.  Linear extension of
`r` is a unital star homomorphism

```text
C[r]:C[Gamma] -> C[K]                                    (PRE2)
```

which fixes `p`.  It therefore restricts to a **corner-unital** star
homomorphism

```text
r_p:p C[Gamma] p -> p C[K] p,          r_p(p)=p.          (PRE3)
```

Consequently every compatible algebraic BCS projection atlas in
`pC[Gamma]p` evaluates to a compatible finite-dimensional atlas in
`pC[K]p`.  Projection, orthogonality, partition, forbidden-atom, and literal
shared-marginal equalities are all star-polynomial identities and are
preserved by `(PRE3)`.  Thus no BCS with a strict finite-dimensional gap can
have such an atlas in a packet-retractive group.

## Rank-two Hecke collision form

Take a primitive `D`-dimensional packet type and the Morita coordinates of
`primitive-packet-corner-is-matrix-over-hecke-atom`:

```text
p C[Gamma]p isomorphic to M_D(H),
H=e C[Gamma]e.                                             (PRE4)
```

Retraction gives the unital scalar evaluation

```text
epsilon_H:H -> e C[K]e=C e.                              (PRE5)
```

Hence a rank-two collision transporter

```text
U=[[a,b],[c,d]] in U(M_2(H))                              (PRE6)
```

evaluates coefficientwise to an ordinary matrix

```text
U_0=[[epsilon_H(a),epsilon_H(b)],
     [epsilon_H(c),epsilon_H(d)]] in U(2).                (PRE7)
```

Every finite square-complex equation among such blocks—including all
inverse, edge, return, and coefficient-link equations used in a proposed
`C(4)-T(4)` transporter—is a matrix star-polynomial identity over `H` and
survives `(PRE5)`.  The link condition can protect injectivity of a relative
presentation; it cannot stop this already-defined finite evaluation.

For the edgeful one-ghost relation, a Hamming-edge Hadamard cell changes
only one logical marginal, but `(PRE7)` turns every such cell into an
ordinary two-dimensional rotation in the root packet.  If a finite family
of those cells closes all `R_edge` overlap chords exactly, their evaluated
context PVMs form a finite perfect `R_edge` strategy.  Therefore this cannot
happen for a strict-gap source instance.

This gives a sharp design constraint on the surviving square-complex route.
Fresh free phases, direct-product spectators, and relative presentations in
which all new relators become trivial after sending the fresh letters to
`1` retain `(PRE1)` and are excluded, regardless of `C(4)-T(4)`.  A live
relative-small-cancellation construction must instead satisfy both:

1. `K` embeds by a genuine relative Freiheitssatz; and
2. the added relations destroy every retraction onto `K`.

The second condition is not cosmetic.  At least one load-bearing contour
must have nontrivial packet value under every attempted specialization of
the new Hecke coefficients, while the first condition must still protect
the packet.  This is precisely where finite evaluation ceases to trivialize
the holonomy.


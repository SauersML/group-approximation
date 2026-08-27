---
rg: 2
id: binary-jacobson-joint-shortest-cells-force-tail-action
kind: claim
title: The two shortest Jacobson cells kill the head after the tail packet is folded away
artifacts:
  - research/binary-jacobson-joint-shortest-cells-force-tail-proof.md
distinct_from:
  binary-jacobson-first-mixed-kernel-is-three-syllable: that controlled-swap cell alone retracts onto the whole finite packet and retains the head mark; this couples it to the independent affine braid and proves that its former tail retraction is now impossible.
  binary-jacobson-shortest-affine-braid-is-finite-marked: that affine braid alone has a full-packet marked quotient in `GL_4(F_2)`; this proves that adjoining the controlled-swap cell kills every quotient in which the tail packet is trivial.
  binary-jacobson-joint-shortest-cells-exclude-natural-completions: that rules out natural head modules with trivial spectators by a linear residual-swap calculation; this is a presentation-theoretic quotient theorem with no natural-module hypothesis, but only after the entire tail factor is killed.
---

**ESTABLISHED.**  Use the complete finite packet

```text
F=G_Q x G_P,                 G_Q ~= G_P ~= GL_3(F_2),
Gamma_F=F *_K (K x <h>)
```

of `binary-jacobson-one-step-finite-type-envelope-is-marked-mf`.  Let

```text
u=w_12,       b=w_23,       rho=u b,       d=u b u=w_13             (JTF1)
```

be the constant Weyl transpositions and cycle.  Adjoin simultaneously

1. the affine braid `(h b)^3=1` of
   `binary-jacobson-shortest-affine-braid-is-finite-marked`; and
2. the controlled three-cycle relation

```text
(rho^2 h u rho^(-2))(rho h u rho^(-1))(h u)=c,
c=(b,1) in G_Q x G_P,                                      (JTF2)
```

of `binary-jacobson-first-mixed-kernel-is-three-syllable`.

Call the resulting joint quotient `Gamma_joint`.  Then

```text
Gamma_joint / normalClosure(G_P) = 1.                       (JTF3)
```

In particular, every homomorphism from `Gamma_joint` which is nontrivial on
the head mark

```text
w=x_13(Q) in G_Q                                            (JTF4)
```

must be nontrivial on the tail factor `G_P`.  Since both factors are simple,
its restriction to each factor is then injective.  Thus every finite marked
quotient contains an embedded copy of

```text
G_Q x G_P ~= GL_3(F_2) x GL_3(F_2).                        (JTF5)
```

The proof is the finite Coxeter calculation hidden by the two separate
countermodels.  After killing `G_P`, the overlap makes `[h,d]=1`; the constant
Weyl relations and the affine braid give

```text
u^2=b^2=h^2=1,       (u b)^3=(h b)^3=1,       [h,u b u]=1. (JTF6)
```

On setting `d=u b u`, these are exactly the Coxeter relations of `S_4` on
the adjacent reflections `d,b,h`; moreover `u=b d b`.  In this `S_4`, with

```text
u=(12),       b=(23),       d=(13),       h=(24),          (JTF7)
```

the left side of `(JTF2)` is `(14)(23)`, while the folded target is `b=(23)`.
Thus the controlled relation kills `(14)`.  A transposition normally
generates `S_4`, so `u,b,h` all die.  The nonidentity element `u` lies in the
simple head factor `G_Q`, hence its normal closure kills `G_Q` and proves
`(JTF3)`.

This is a fence, not a finite-dimensional or MF collapse theorem.  It rules
out every tail-trivial marked model, but it does not decide representations
in which both finite simple packet factors act.  In finite-type language, a
surviving head-marked carrier must export support into a nontrivial tail type;
the regular packet has ample such tail multiplicity, so that export alone is
not a Hall deficit.

DERIVATION
binary-jacobson-joint-shortest-cells-force-tail-proof

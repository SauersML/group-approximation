---
rg: 2
id: algebraic-exhaustive-marked-type-detectors-violate-induction
kind: claim
title: Algebraic exhaustive marked-type detectors violate the induced-representation firewall
distinct_from:
  finite-selector-gadget-induction-barrier: that shows every marked selector character occurs in a finite packet; this shows why exact multiplicity-insensitive relator tests cannot charge all of those types after the packet is embedded in an ordinary group.
  finite-role-packet-cannot-supply-hybrid-predicate-row: that treats one scalar word in the finite regular packet; this permits arbitrary finite menus and non-scalar SMC commutator rows but rules out their exhaustive algebraic promotion.
  exhaustive-marked-type-energy-summation: that proves exhaustive coverage would be analytically sufficient in finite matrices; this identifies why ordinary SMC covariance cannot supply the coverage.
---

Let `A<=H<=Gamma`, where `H` is finite, `A` is an abelian selector subgroup,
and the central involution `y in A` remains nontrivial.  Let

```text
p_bad=sum_(chi(y)=-1, f(chi)=1) p_chi in C[A]         (IEM1)
```

be the spectral projection of a nonempty set of rejected marked selector
characters.  For `lambda in Irr_-(H)`, let `q_lambda` be the primitive
central projection of `C[H]`.

There is no finite family of group relators which has, in **every exact
unitary representation** `Pi` of `Gamma`, a multiplicity-insensitive
typewise operator estimate

```text
sum_(r in T_lambda)
 q_lambda (Pi(r)-1)^*(Pi(r)-1) q_lambda
 >= kappa_lambda q_lambda p_bad q_lambda              (IEM2)
```

for every marked `lambda` and positive constants `kappa_lambda`.

In particular, balanced SMC covariance/commutator formulas cannot be
promoted exhaustively from a selected type to all marked types while the
finite selector packet embeds.  Their Schur-factor calculations remain
valid on infinite multiplicity spaces, so an exhaustive version would have
exactly the forbidden algebraic form `(IEM2)`.

## Proof

Choose a rejected character `chi` in `(IEM1)`.  Frobenius reciprocity gives
a marked irreducible constituent `lambda` of

```text
Ind_A^H chi                                             (IEM3)
```

for which

```text
q_lambda p_chi !=0,
q_lambda p_bad q_lambda!=0.                            (IEM4)
```

It is marked because centrality of `y` makes it act as the scalar
`chi(y)=-1` on every constituent of `(IEM3)`.

Now take the unitary induced representation

```text
Pi=Ind_H^Gamma lambda.                                 (IEM5)
```

The copy of `lambda` supported on the identity coset shows that the
right-hand side of `(IEM2)` is a nonzero positive operator.  Every `r` in a
presentation relator menu is the identity element of `Gamma`, so the
left-hand side is zero.  This contradicts `(IEM2)`.

The argument uses no trace and no finite-dimensional multiplicity.  It is
therefore exactly the firewall that the desired non-hyperlinear compiler
must avoid.

## Consequences for the SMC exhaustive-coverage proposal

On one selected type, an SMC row has

```text
u=S tensor R,
v=P tensor T,
[u,v]=D_f tensor [R,T],                                (IEM6)
```

and the outer D8 commutator cancels `[R,T]`.  Schur factorization and this
cancellation are algebraic on arbitrary Hilbert multiplicity spaces, not
finite-matrix phenomena.  If the same construction supplied a positive
rejection operator on every marked `H`-type, it would yield `(IEM2)` and
contradict `(IEM5)`.

Thus the exhaustive strategy has a precise split verdict:

```text
finite typewise energy summation:             VALID;
ordinary algebraic SMC coverage of all types: IMPOSSIBLE.                (IEM7)
```

There are only two honest escapes.

1. The finite packet does not embed: rejected selector characters are
   collapsed in its image.  Then the packet no longer retains the claimed
   selector semantics; by induction applied to the image selector subgroup,
   every character which remains still occurs.
2. The estimate is genuinely finite-dimensional-only, using cyclic finite
   trace, integer multiplicity, a proper-corner return, or another matrix
   capacity law.  Such an estimate need not hold in `(IEM5)` and is exactly
   the remaining viable exhaustive-type actuator.

This is not a no-go for exhaustive coverage itself.  It is a no-go for
obtaining that coverage solely from the algebraic, multiplicity-insensitive
SMC identities already used on one selected type.

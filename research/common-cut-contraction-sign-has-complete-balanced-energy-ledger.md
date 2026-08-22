---
rg: 2
id: common-cut-contraction-sign-has-complete-balanced-energy-ledger
kind: claim
title: Common-cut contraction and terminal sign have a complete balanced-energy ledger
distinct_from:
  aggregate-cut-compression-stores-boundary-as-involution-defect: that identifies the boundary and positive involution defect and gives a coarse word telescoping estimate; this gives the exact even-word and pair formulas and tracks every balanced layer through the terminal sign.
  one-anchor-grading-makes-parity-damage-quadratic: that works with the grading of one reflection and an operator-small odd row; this applies to an arbitrary common projection and gives unconditional Hilbert--Schmidt energy bounds.
  involution-augmented-code-jacobian-adds-no-cb-loss: that is an infinitesimal splitting at an exact reflection tuple; this is a finite, base-free compression and final-rounding ledger.
  whole-face-sign-rounding-does-not-inherit-gap-contraction: that rules out strict contraction from repeated local sign maps; this signs only once after the augmented contraction energy has vanished.
---

ESTABLISHED.  Let `p` be a projection, `q=1-p`, and let
`B_1,...,B_L` be reflections in a finite tracial von Neumann algebra.  Put

```text
 Phi(T)=pTp+qTq,       X_i=Phi(B_i),       O_i=B_i-X_i,
 d_i=||O_i||_2=||[p,B_i]||_2.                         (CCL1)
```

Then `X_i` is a selfadjoint contraction, `O_i` is block off-diagonal, and

```text
 X_iO_i+O_iX_i=0,       I-X_i^2=O_i^2>=0,
 r_i^2:=||I-X_i^2||_2^2=tau(O_i^4)<=d_i^2.             (CCL2)
```

The damage to all three non-involution layers has an exact algebraic form.
For a word `W=B_(i_1)...B_(i_m)`, let `W_S(X,O)` denote the ordered word
with `O` in the positions in `S` and `X` elsewhere.  Then

```text
 X_(i_1)...X_(i_m)-epsilon I
  =Phi(W-epsilon I)
   -sum_(nonempty even S subseteq {1,...,m}) W_S(X,O). (CCL3)

 X_i-X_j=Phi(B_i-B_j),                                 (CCL4)

 [X_i,X_j]=Phi([B_i,B_j])-[O_i,O_j].                   (CCL5)
```

In particular, there is no term with one cut boundary in a parity word or
pair commutator.  Without any operator-norm smallness one still has the
dimension-free estimates

```text
 ||X_(i_1)...X_(i_m)-epsilon I||_2^2
   <=2||W-epsilon I||_2^2+2m sum_(a=1)^m d_(i_a)^2,    (CCL6)

 ||X_i-X_j||_2<=||B_i-B_j||_2,                         (CCL7)

 ||[X_i,X_j]||_2^2
   <=2||[B_i,B_j]||_2^2+8 min(d_i^2,d_j^2).            (CCL8)
```

Thus bounded-width, bounded-occurrence parity and equality layers are
charged by the average boundary `D=L^(-1)sum_i d_i^2`; the normalized
complete-pair layer is charged by at most `8D`, since
`L^(-2)sum_(i,j)min(d_i^2,d_j^2)<=D`.

Now choose `S_i=sgn(X_i)`, taking `sgn(0)=1`, and put
`a_i=||S_i-X_i||_2`.  Scalar functional calculus gives the stronger
conventional squared-residual estimate

```text
 a_i^2<=r_i^2.                                         (CCL9)
```

For every parity word of length `m`, equality edge, and ordered pair,

```text
 ||prod_a S_(i_a)-epsilon I||_2^2
   <=2||prod_a X_(i_a)-epsilon I||_2^2
      +2m sum_a r_(i_a)^2,                              (CCL10)

 ||S_i-S_j||_2^2
   <=3||X_i-X_j||_2^2+3r_i^2+3r_j^2,                  (CCL11)

 ||[S_i,S_j]||_2^2
   <=3||[X_i,X_j]||_2^2+12r_i^2+12r_j^2.              (CCL12)
```

Consequently a contraction tuple with vanishing augmented balanced energy
can be signed **once, simultaneously**, to a reflection tuple with
vanishing balanced energy.  The constants depend only on face width and
the normalized occurrence bounds, never on `L`, matrix dimension, number
of cuts, or spectral multiplicity.

At an exact code tuple, quotienting simultaneous conjugation is sufficient
to remove the Hilbert-space kernel exhibited by common character rotation:
the remaining normal variables are handled by the explicit involution
inverse and the tangent Hilbert Jacobian has the established transverse
gap, and the finite-time covariant divergence gives the required cb
contraction on that quotient.  The rotated two-character family is
therefore not a counterexample:
terminal sign returns its pinched contractions to the original character
tuple at the same quartic energy scale.  This statement does **not** turn
an exact-base quotient into a global basin theorem.  The remaining analytic
obstruction is to run the finite-time covariant correction before an exact
code-character decomposition exists while controlling sparse parity and
equality re-exactification, not compression, common-conjugacy gauge, or
final sign.

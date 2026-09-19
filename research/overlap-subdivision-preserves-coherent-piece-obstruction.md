---
rg: 2
id: overlap-subdivision-preserves-coherent-piece-obstruction
kind: claim
title: Equality subdivision raises macro girth but not coherent coefficient-piece girth
distinct_from:
  coherent-four-potential-pairings-cannot-be-long-c-sixth: that counts the four recurrent potential blocks in one already-given pairing contour; this proves that soundness-preserving subdivision of the external BCS overlap graph leaves such endpoint contours in place.
  equality-synchronized-lifts-create-two-pair-contours: that treats lifted Pauli occurrence games and their relative two-pair contours; this treats signed-Hecke coefficient potentials and exact overlap-equality subdivision.
  slofstra-zhang-high-girth-phase-survival: that uses incidence girth to protect a central phase in a solution group; this separates that macro incidence girth from the term-pairing link needed for a signed-Hecke corner identity.
---

Let a finite operator constraint system have context observables `X_(c,x)`
and overlap equations

```text
X_(c,x)=X_(d,x).                                         (EOS1)
```

Replace an overlap `e` by a path of length `L_e`, naming intermediate
observables `Z_(e,k)` and imposing

```text
Z_(e,0)=X_(c,x),   Z_(e,L_e)=X_(d,x),
Z_(e,k-1)=Z_(e,k)                    (1<=k<=L_e).        (EOS2)
```

This operation is harmless semantically.  Exact solutions of `(EOS2)`
forget to exact solutions of `(EOS1)`, and every exact solution of `(EOS1)`
lifts by taking the path constant.  Quantitatively, for the unweighted
squared Hilbert--Schmidt consistency energies,

```text
||X_(c,x)-X_(d,x)||_2^2
 <= L_e sum_(k=1)^(L_e)||Z_(e,k-1)-Z_(e,k)||_2^2.       (EOS3)
```

Consequently, if the original full energy has finite-dimensional infimum
`gamma>0`, the subdivided full energy has infimum at least
`gamma/L_max`, where `L_max=max_e L_e`.  With averaged test weights there
is only the additional finite ratio between the old and new numbers of
tests.  Thus any fixed finite subdivision preserves a strict gap, although
it can make that gap smaller.

It does **not** give the small-cancellation input needed by the standard
signed-Hecke term compiler.  At an original context, a coherently escaped
projection still has coefficients

```text
y_ij h_i h_j^(-1) E_ij.                                 (EOS4)
```

The first segment incident to that context still pairs `(EOS4)` with a term
at the first new path vertex.  Subdivision changes how many such local
pairing relators occur in series; it does not lengthen any endpoint pairing
relator and does not replace the words `h_i` occurring in `(EOS4)`.  On the
cyclic 2-core, every endpoint or intermediate potential used by the two
adjacent segment equations is recurrent.  Each local equality therefore
has the same four-recurrent-potential form

```text
H_1 B_1 H_2 B_2 H_3 B_3 H_4 B_4                       (EOS5)
```

as before.  The piece-counting theorem
`coherent-four-potential-pairings-cannot-be-long-c-sixth` applies to
`(EOS5)` independently of `L_e`.  In particular:

* relative `C'(1/6)` still fails when the coefficient bridges are
  peripheral;
* bounded ordinary coefficient bridges still bound the possible contour
  length; and
* making the **macro** overlap cycle arbitrarily long does not change either
  conclusion.

There is a useful dichotomy behind this observation.  If instead one writes
only one long path relator and lets a fresh internal path letter occur once,
then that letter is Tietze-eliminable.  Explicitly,

```text
<G,t_1,...,t_L | A t_1...t_L B^(-1)>
  is isomorphic to G * F(t_1,...,t_(L-1)),               (EOS6)
```

by solving for `t_L`; the displayed relator imposes no equality between the
old endpoint words `A` and `B`.  Making the path enforce `(EOS1)` requires
reusing or constraining the internal letters.  The local equality
implementation `(EOS2)` does exactly that and returns to the recurrent
piece system `(EOS5)`.

This result does **not** rule out an exotic relative `C(4)-T(4)` compiler.
Four recurrent potential blocks are compatible with the numerical
`C(4)` threshold, unlike `C'(1/6)`.  But the relevant `T(4)` link is the
link of coefficient-pairing relators, including repeated term pairs inside
each context, not the subdivided BCS incidence graph.  External high girth
alone proves neither `C(4)` nor `T(4)`.  A live `C(4)-T(4)` route must first
replace the term system by one whose *coefficient link* has no two-piece
collisions or triangles while retaining the single vertex-potential
cocycle.  Occurrence-specific copies do not supply that replacement:
without synchronization they destroy projection coherence, and with exact
synchronization they fall under `(EOS2)--(EOS5)`.

Thus soundness-preserving high-girth subdivision is useful bookkeeping, but
it is not a Freiheitssatz for the first signed-Hecke chord.  Any appeal to a
relative or graphical Freiheitssatz must verify its hypotheses on the
coherent coefficient presentation itself.

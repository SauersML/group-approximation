---
rg: 2
id: one-sided-amitsur-oracle-has-two-unitary-corner-model
kind: claim
title: Two unitary variables carry the one-sided Amitsur oracle with a fixed half-corner gap
distinct_from:
  one-sided-amitsur-oracle-has-bounded-fock-model: that uses two proper Fock isometries and countably many named left inverses; this replaces the isometries by corners of two unitaries and removes every inverse generator, while preserving a dimension-matched constant normalized-HS residual.
  rational-unitary-additive-dilation-is-trivial: that rules out a fixed rational unitary representation of the additive line; this uses an external two-by-two corner and Halmos dilations only to unitarize two already bounded operators, leaving the alternating star-polynomials additive.
  universal-block-return-violates-the-regular-firewall: that forbids a fixed functorial proper-return decoder; this gives an exact chosen infinite representation and a finite-coordinate PI residual, and explicitly does not claim that its corner equations follow from group relators in every tracial representation.
  constant-hs-groupification-of-residual-dimension-tape: that asks for finite group-word control and runtime-independent semantic transport; this removes the bounded-model, nonunitary-letter, inverse-generator, and carrier-density issues before that still-open compiler.
---

ESTABLISHED.  There is a countable star-polynomial presentation with only two
variable generators, both required to be unitary, which has a bounded exact
infinite-dimensional representation and whose instruction indexed by the
finite corner dimension has normalized Hilbert--Schmidt residual exactly
`1/sqrt(2)`.

Let `P=e_11 tensor I` be the fixed half-corner in `M_2(B(H))`.  For two
unitary variables `U_x,U_y`, put

```text
X=P U_x P,                  Y=P U_y P,
W_j=X Y^j X,
A_n=s_(2n)(W_1,...,W_(2n)),
R_n=((2n)!)^(-1) A_n^* A_n-P.                         (TUC1)
```

Consider the countable relations

```text
U_x^*U_x=U_xU_x^*=U_y^*U_y=U_yU_y^*=I,
R_n=0                                                   (n>=1). (TUC2)
```

They have an exact bounded model.  On full Fock space let `L_x,L_y` be the
left creation isometries.  If `V` is either one, set

```text
D_V=I-VV^*,
H(V)=[[V,D_V],[0,-V^*]] on H direct_sum H.             (TUC3)
```

Because `D_V` is a projection, `D_V V=0=V^*D_V`; hence `H(V)` is unitary and

```text
P H(V) P=[[V,0],[0,0]].                                (TUC4)
```

Taking `U_x=H(L_x)` and `U_y=H(L_y)`, the prefix-code calculation of
`one-sided-amitsur-oracle-has-bounded-fock-model` gives

```text
A_n^*A_n=(2n)! P,                                      (TUC5)
```

so every relation in `(TUC2)` holds.  All operators in the model are bounded;
indeed the only variable operators are unitaries.

Now evaluate the same formulas at arbitrary
`U_x,U_y in U(2d)`, keeping the external projection
`P=e_11 tensor I_d`.  The compressed letters `X,Y` act on the `d`-dimensional
space `P C^(2d)`.  Amitsur--Levitzki therefore gives

```text
A_d=0,
R_d=-P,
||R_d||_(2,2d)=sqrt(rank(P)/(2d))=1/sqrt(2).            (TUC6)
```

Thus unitarizing the Fock letters causes no loss whatever in the
dimension-matched semantic gap, and the moving generators `q_n` are
unnecessary: the positive relation `A_n^*A_n=(2n)!P` already supplies their
job.

This is not yet a unitary **group-relator** presentation.  The family
`R_n=0` is countable, its alternating sums have growing support and coefficient
mass, and the fixed matrix corner is an external coefficient rather than a
group word.  Moreover one cannot simply require the underlying Fock row
isometry relations to hold functorially after a block-word decoding: in the
finite algebra `M_m(L(Gamma))`, two decoded operators with
`S_i^*S_i=P` and orthogonal ranges below `P` would give

```text
2 tau(P)=tau(S_1S_1^*)+tau(S_2S_2^*)<=tau(P),           (TUC7)
```

so faithfulness forces `P=0`.  The Fock prefix proof is therefore a
completeness witness in the chosen properly infinite representation, not a
relation that a group compiler may decode on the regular carrier.  The exact
remaining terminal is a finite group-word/PCP compiler for the positive
relations `(TUC2)` which preserves `(TUC6)` without deriving the proper-row
relations and without paying their growing evaluation length.


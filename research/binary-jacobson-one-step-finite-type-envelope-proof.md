---
rg: 2
id: binary-jacobson-one-step-finite-type-envelope-proof
kind: route
title: Amalgamate the finite packet with its complete balanced overlap and apply unitary Hall balance
target: binary-jacobson-one-step-finite-type-envelope-is-marked-mf
requires:
  - binary-jacobson-active-cycle-generates-rank-three
  - finite-packet-graph-atlases-have-a-regular-stationary-flow
---

The equality `F_2[Q] ~= F_2 x F_2` is
`binary-jacobson-constant-q-root-envelope-is-finite`.  Elementary groups
commute with finite products, and
`EL_3(F_2)=SL_3(F_2)=GL_3(F_2)`, proving `(JFT2)`.

The calculation in
`binary-jacobson-active-cycle-generation-proof` gives `h^2=1`.  Direct
matrix multiplication using `Q^2=Q`, `QS=0` and `TQ=0` shows that `h` fixes
the coefficient column defining `x_13(Q)`, hence `[h,w]=1`.

For completeness, compute the subgroup `K` in `(JFT4)`.  Use the faithful
unilateral-shift module with basis `e_n`, where `Q` projects onto `e_0`,
`P=1-Q` projects onto the span of `e_n,n>=1`, `S e_n=e_(n+1)`, and
`T e_(n+1)=e_n`.  An element of `F` is a pair `(A,B) in G_Q x G_P`: it acts
by `A` on the three coordinate copies at level zero and by the same matrix
`B` at every positive level.  The involution `h` acts on coordinate/level
pairs by

```text
(1,0) |-> (1,0),
(1,n+1) <-> (2,n),
(3,n) |-> (3,n).                                        (JFTP1)
```

Requiring `h(A,B)h` to preserve every three-dimensional level forces `B`
to be diagonal and forces `A` to preserve
`<e_1,e_3> directSum <e_2>`.  Since the field is `F_2` and `B` is invertible,
`B=I`.  Comparing the action at levels zero and one then forces `A e_2=e_2`.
Conversely every such `(A,I)` commutes with the permutation `(JFTP1)`.
This proves `(JFT4a)`, including `theta=id`.

In particular `K` is finite.  Moreover

```text
h K h = h(F cap hFh)h = hFh cap F = K,
```

so `theta` is an involutive automorphism.  The matrix entry `T` in `h` does
not belong to `F_2[Q]` (for example this is immediate in the faithful
unilateral-shift model), hence `h notin F`.  Thus `<K,h>` has the stated
semidirect-product presentation and is the finite group `B`.

Bass--Serre normal form embeds both vertex groups in `Gamma_F=F *_K B`.
An amalgam of finite groups over a finite group is virtually free and
residually finite.  Residual finiteness supplies a finite quotient separating
simultaneously the finitely many nonidentity elements of `F`; hence that
quotient is injective on `F` and in particular does not kill `w`.  The
finite-dimensional regular representations of such quotients give a
faithful separating family, so `Gamma_F` is operator MF.

All amalgamating relations hold for the literal subgroups `F,B<=E`, giving
the map `(JFT6)`.  Its image contains `F` and `h`, hence also `a=hu`.  Since
`F` contains the three constant roots `x_12(1),x_23(1),x_31(1)`, the active
cycle generation theorem says that the image is all of `E`.

For `(JFT7)`, let `P=(1-rho(w))/2`.  Since `[h,w]=1`, `rho(h)` restricts to a
unitary `U` on `P`.  Let `{P_i}` be any finite orthogonal decomposition of
`P`, including one selected from the actual finite-matrix coordinate, and
put `P_S=sum_(i in S)P_i`.  By definition of `N(S)`,

```text
U P_S = P_(N(S)) U P_S.
```

The map `UP_S` is an isometry, so its range has rank `rank(P_S)` and lies in
the range of `P_(N(S))`.  This proves `(JFT7)`.  If only central `F`-isotypic
projections are used, `u in F` commutes with each such projection.  Therefore

```text
P_j rho(a)P_i=P_j rho(h)P_i rho(u),
```

and the `a`- and `h`-support graphs coincide.

Finally write an irreducible of `F=G x G` as `alpha box beta`.  In the
regular representation its multiplicity is `d_alpha d_beta`.  The negative
`w`-space inside the label representation has dimension `r_alpha d_beta`;
multiplying gives `(JFT8)`.  Since a transvection normally generates the
simple group `G`, it acts trivially in an irreducible `alpha` exactly when
`alpha` is trivial.  Hence `r_alpha>0` for every nontrivial `alpha`.
Left multiplication by the nonidentity involution `w` on `C[F]` consists of
two-cycles, so its two sign spaces both have dimension `|F|/2`, proving the
sum assertion.  The regular stationary-flow theorem gives compatible
amplifications across the finite edge group `K`, completing the proof.

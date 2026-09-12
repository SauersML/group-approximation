# Hybrid rank router: tensor-closure refutation and surviving pointed face

Date: 2026-08-23

## Outcome

The universal hybrid rank router proposed after the independent-set
reduction is impossible as stated.  This is not a failure of one attempted
D8 implementation.  It follows from tensor closure of ordinary-group
representations.

The rank-conjugacy overlap lemma itself remains valid.  What fails is the
simultaneous demand that

1. every zero-overlap pair of projection reflections have an exact gadget
   extension;
2. fixed group words universally decode

   ```text
   R=diag(A,B),          S=diag(AB,1);
   ```

3. one exact group relator conjugate `R` to `S`.

The correct successor is source-specific and pointed: exact completeness
for one distinguished perfect trace, and soundness only on a global moment
face containing the canonical matrix microstates.  That face must not be
closed under the tensor product below.

## 1. Tensor-closure contradiction

Write `A=1-2P` and `B=1-2Q`.  Complement-flexible exact completeness
includes the three scalar admissible pairs

```text
(P,Q)=(1,0),   (0,1),   (0,0),
(A,B)=(-1,1),  (1,-1),  (1,1).                        (TC1)
```

Choose each promised exact representation in the negative sector of the
central marked involution `m`.  Tensor the three representations.  Every
ordinary relator stays exact, and the central character stays negative:

```text
(-1)^3=-1.                                             (TC2)
```

The two interface words multiply, so the tensor product has

```text
A=-1,                  B=-1.                           (TC3)
```

Universal zero-defect routing now says

```text
R=-I,                  S=I.                            (TC4)
```

But the tensor product of the three exact stable-letter relations still
says `URU^*=S`.  A unitary cannot conjugate `-I` to `I`.  Equivalently the
rank-conjugacy inequality would read

```text
2||PQ||_2^2=2 <= 0.                                    (TC5)
```

Without a marked order-two sector, the first two factors already suffice.
Fixed amplifications are harmless because tensor products may be taken
after amplifying.

This proves a categorical no-go: arbitrary auxiliary generators,
noncommuting finite packets, additional relators, or a different nested D8
tree cannot repair the universal statement.  The admissible relation
`PQ=0` is not multiplicatively closed in the reflection coordinates, while
exact group-representation restrictions necessarily are.

## 2. The router secretly contains a controlled payload

There is also a useful structural diagnostic.  Set `B=I`, which is an
admissible zero-overlap specialization for every `A`.  Both desired hybrids
coincide:

```text
R=S=diag(A,I).                                         (CC1)
```

Thus the purportedly affine four-slot router already contains the nonlinear
one-sided controlled-payload operation.  Rank conservation does not remove
that gate; it is needed only after the gate has been built.

For every architecture in which the selected finite role packet generates
`M_d tensor I` and router words normalize that factor, Schur's lemma makes
each word

```text
C tensor W.                                            (CC2)
```

For a balanced role selector `p` and a balanced nonscalar involution `A`,

```text
T=p tensor A+(1-p) tensor I                            (CC3)
```

has two operator-Schmidt coefficients `1/sqrt(2)`.  Hence

```text
inf_(C,W unitary) ||T-C tensor W||_2^2 >= 2-sqrt(2).   (CC4)
```

This gives a quantitative firewall for every finite-normal-packet or
covariance-only implementation, independently of the broader tensor
refutation.

## 3. Exact countermodel to the minimal nested-D8 assembler

The most natural attempt tries to factor each payload through the common D8
swap.  In the negative spin sector let `z=diag(I,-I)` and let `j` exchange
the halves.  For commuting payload involutions `a,b`, introduce involutions
`r,s` satisfying

```text
(rj)^2=a,       (sj)^2=b,
[r,b]=[s,a]=[r,s]=1.                                  (D81)
```

Solving these equations gives

```text
r=diag(AW,W),          s=diag(BV,V),                  (D82)
```

for commuting involutions `A,B,W,V`.  With `G=WV`, the obvious output words
are

```text
rjsj=diag(AG,BG),       rs=diag(ABG,G).                (D83)
```

They are the desired blocks multiplied by one unresolved multiplicity
gauge.  That gauge is not harmless for a trace checksum.

Take multiplicity Pauli matrices `Z,X`, set

```text
A=B=-I,       W=Z,       V=I,       U=I_role tensor X. (D84)
```

Then all relations in `(D81)` hold exactly and

```text
R=-I_role tensor Z,     S=I_role tensor Z,
URU^*=S,                ||PQ||_2^2=1.                 (D85)
```

Thus a balanced transverse Pauli flips the residual gauge and makes the
conjugacy word exact at maximal forbidden overlap.  This is the explicit
matrix escape behind the abstract tensor obstruction.

## 4. Surviving endpoint

The only coherent rank-conjugacy successor is a non-tensor-closed pointed
face.  It must provide:

- one distinguished perfect tracial source extension, not an extension of
  every pair with `PQ=0`;
- global row-clock/PVM moments which are lost under the tensor construction
  `(TC1)`;
- a canonical-microstate or finite-coordinate inference routing the rank
  words only on that face.

Possible mechanisms are a trace-selected packet face, a nonmultiplicative
global row-PVM moment, or a genuinely matrix-only proper-corner
localization.  A central character by itself is insufficient, as `(TC2)`
shows.  Ordinary finite normal-packet covariance is insufficient by
`(CC4)`, and the minimal nested-D8 factorization is insufficient by `(D85)`.

This replacement is recorded as
`source-specific-pointed-rank-router-face`.  If established, it still feeds
the independent-set gap and rank-conjugacy inequality into the
nonhyperlinearity terminal.  What has been removed is the impossible
universal exact-extension promise.

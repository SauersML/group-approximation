---
rg: 2
id: matrix-phase-noncommutative-alpha-plane-route
kind: claim
title: Prove a noncommutative alpha-plane energy inequality for arbitrary block phases
distinct_from:
  matrix-phased-translations-exact-identity-scalarize: that assumes zero identity energy and diagonalizes exactly; this asks for a joint inequality when both sampled energies are nonzero.
  pauli-block-phases-have-uniform-two-matching-soundness: that uses discrete Pauli labels and a symplectic form; this allows arbitrary unitary blocks with no finite label model.
---

OPEN.  The arbitrary block-diagonal conjugator sector has one self-contained
formulation.  For `R:K->U(d)`, define

```text
I(R)=E_(x,y)||R_y R_x^*-R_x R_y^*||_2^2,                    (NC1)

A(R)=E_(x,b)||R_(x+b)R_x^*
                 -R_(x+(1+alpha)b)R_(x+alpha b)^*||_2^2,    (NC2)

F(R)=E_(x,a,b)||R_(x+b)R_x^*
                 -R_(x+a+b)R_(x+a)^*||_2^2.                (NC3)
```

For the tables `(MP1)`, these are exactly the identity-matching,
alpha-matching, and complete cross-commutator energies.  Prove, or disprove,

```text
F(R) <= C(I(R)+A(R))                                         (NC4)
```

with universal `C`, independent of `n,d`.  This would settle every
single-block-PVM orbit and leave only mixing between inequivalent `X`-orbits.

The endpoint already has a positive noncommutative Fourier formula.  With
normalized Fourier matrices

```text
M_xi=E_x (-1)^<xi,x> R_x,
```

operator-valued Parseval gives

```text
F(R)=2(1-sum_xi tr((M_xi M_xi^*)^2)).                        (NC5)
```

Thus `(NC4)` is a derandomized matrix-valued `U^2` inequality: the identity
orientation correlation plus the alpha-plane quartic correlation must control
the complete positive Fourier fourth moment.

## Closed boundary cases

- `I(R)=0`: `matrix-phased-translations-exact-identity-scalarize` gauges the
  blocks into commuting reflections and gives `(NC4)` with `C=27/2`.
- Signed Pauli `R_x`: `pauli-block-phases-have-uniform-two-matching-soundness`
  proves `(NC4)` by correcting the discrete quotient labels, killing the
  symplectic cocycle, and scalarizing the center.
- Scalar reflections: `phased-translations-reduce-to-alpha-plane-test` is the
  Kaufman--Sudan affine single-orbit inequality.

## Attempts

- **Round `(NC1)` before using `(NC2)`.**  This is false uniformly.  Pauli
  reflections realizing a fixed-degree regular anticommutation graph have
  `I(R)=O(1/N)` but constant average distance from every commuting family.
  The two energies must enter one joint square function.
- **Apply scalar single-orbit soundness to matrix coefficients.**  The sampled
  equation is linear in edge quotients `R_yR_x^*`, but those quotients obey a
  noncommutative cocycle.  Individual coefficients do not satisfy the Boolean
  parity constraint, and summing coordinatewise loses the matrix dimension.
- **Use only the long multiplicative cycle of `alpha`.**  Its spectral gap
  tends to zero.  Scalar soundness survives because of affine-orbit
  self-correction, not because that cycle expands; a valid operator proof must
  retain the four-point cocycle identities.
- **Direct Fourier Cauchy--Schwarz.**  The alpha quartic form is an involutive
  mixing of pairs of Fourier matrices.  Plain Cauchy--Schwarz bounds it by one
  and does not recover the diagonal positive fourth moment in `(NC5)`.  The
  missing input is precisely the orientation energy `(NC1)`.
- **Replace the four vertices by one correlated corrector each and cancel the
  resulting twelve factors.**  Writing `B=1+alpha`, the two corrected edges
  have six point labels on each side, built from
  `p+alpha c,p+B c,p+c`.  Exhausting all `6!` unsigned matchings (stars may be
  removed after a gauge) gives inconsistent linear equations for the four
  correction directions; the same holds a fortiori for sign-preserving
  matchings.  This was checked over `F_(2^n)` for `2<=n<=10`.  Choosing a
  different missing slot gives no new decoder: all four slot orientations
  have the same ordered offsets `(alpha,B,1)` from the target.  Thus a direct
  proof needs nested corrections or a comparison subtler than literal word
  cancellation.

## Promising joint attack

The Kaufman--Sudan self-corrector has a literal unitary-heap analogue.  Solving
one alpha constraint for the value at `t` gives

```text
C_t(b)=R_(t+alpha b) R_(t+(1+alpha)b)^* R_(t+b),              (NC6)
```

and bi-invariance shows exactly

```text
E_(t,b)||C_t(b)-R_t||_2^2=A(R).                              (NC7)
```

Their scalar proof compares two corrections by placing test words on the rows
and columns of one `4 x 4` tensor square.  For unitaries the same row/column
calculation fails only when the order of two heap factors is reversed.  Every
such reversal is a quotient-orientation error of the form `(NC1)`; because the
four affine forms are pairwise independent, its two indices are uniform, so it
can be charged to `I(R)` without a rank or field-size loss.  A successful proof
should write this tensor square directly in `L^2(M_d)`, use Pythagoras/Jensen
instead of plurality, and bound the constant number of factor reversals by
`I(R)`.  This is more specific than first diagonalizing: the row and column
constraints and orientation errors must be summed in the same square function.

### Exact `4 x 4` affine-form ledger

Change from `(x,b)` to the two endpoints `(u,v)=(x,x+b)`.  With
`B=1+alpha`, the alpha-plane forms are the rows of

```text
L = [ (1,0), (0,1), (B,alpha), (alpha,B) ].                  (NC8)
```

For

```text
Gamma = [ t  y ]
        [ z  r ],
```

set `M_ij=L_i Gamma L_j^T`.  Every row and every column of `M` is one
alpha-plane query.  Row one is the query with endpoint variables `(t,y)` and
column one is the query with endpoint variables `(t,z)`.  Thus, with the heap

```text
H(a,b,c)=a b^* c,
```

their missing-corner decodes are

```text
C_t(t+y)=H(R(M_13),R(M_14),R(M_12)),
C_t(t+z)=H(R(M_31),R(M_41),R(M_21)).                         (NC9)
```

For `i,j in {2,3,4}`, write `L_i=(p_i,q_i)`.  The random `(y,z,r)`
coefficient vector of `M_ij` is

```text
(p_i q_j, q_i p_j, q_i q_j)
 =q_i q_j (p_i/q_i, p_j/q_j, 1).                            (NC10)
```

The three ratios are `0,B/alpha,alpha/B`, which are distinct.  Therefore all
nine interior forms are pairwise independent and every pair of their values is
uniform on `K^2`.  This is the exact fact needed to charge each orientation
swap by `(NC1)`.

Let `x_ij=R(M_ij)` on the interior.  Decoding the first-row entries down their
columns and then decoding the top-left corner gives

```text
D_row = x_33 x_43^* x_23 x_24^* x_44 x_34^* x_32 x_42^* x_22.
                                                                    (NC11)
```

Decoding the first-column entries across their rows gives

```text
D_col = x_33 x_34^* x_32 x_42^* x_44 x_43^* x_23 x_24^* x_22.
                                                                    (NC12)
```

These are the two sides of the heap medial identity

```text
H(H(a,b,c),H(d,e,f),H(g,h,i))
 =H(H(a,d,g),H(b,e,h),H(c,f,i)).                            (NC13)
```

For an exact Boolean torsor `(NC13)` holds.  Quantitatively, choose any one of
the nine `x_ij`, say `G=x_22`, as gauge anchor and put `s_ij=x_ijG^*`.
For every interior index `p` and pair `p,q`, respectively,

```text
||s_p-s_p^*||_2
 =||x_pG^*-Gx_p^*||_2,                                      (NC14a)

||s_p s_q-s_q s_p||_2
 <=||x_p x_q^*-x_q x_p^*||_2
   +||s_p-s_p^*||_2+||s_q-s_q^*||_2.                        (NC14b)
```

After substituting `x_p=s_pG`, both `(NC11)` and `(NC12)` end in the same
right factor `G`.  Replace their eight starred `s` factors by unstarred ones,
then reorder one nine-letter word into the other by at most `36` adjacent
swaps.  By `(NC14a)--(NC14b)` this uses at most `8+3*36=116` primitive
orientation errors.  Pairwise independence from `(NC10)` makes the mean
square of every primitive error exactly a summand of `I(R)`.  The six
row/column replacements used to pass between `(NC9)` and `(NC11)--(NC12)` are
alpha-query errors.  Triangle inequality followed once by Cauchy--Schwarz
therefore gives the fully explicit intermediate estimate

```text
sup_t E_(y,z)||C_t(t+y)-C_t(t+z)||_2^2
 <=15000(A(R)+I(R)).                                         (NC14)
```

The unresolved step is to turn the continuous correction concentration
`(NC14)` into the complete energy `(NC3)` without the scalar proof's discrete
plurality/positive-probability argument.  Polarizing the mean correction gives
a nearby unitary table, but a contraction estimate for its test energy has not
yet been proved.

### Polar-mean identities and the exact contraction gap

Put

```text
M_t=E_b C_t(b),                 P_t=polar(M_t),               (NC15)
V_t=E_b||C_t(b)-M_t||_2^2.
```

Choose an arbitrary unitary extension on the kernel in the polar factor.
Hilbert-space variance and the fact that every `C_t(b)` is unitary give the
exact identities

```text
E_b||C_t(b)-R_t||_2^2
 =V_t+||M_t-R_t||_2^2,                                      (NC16)

V_t=1-||M_t||_2^2
    =(1/2)E_(b,c)||C_t(b)-C_t(c)||_2^2.                      (NC17)
```

Since `M_t` is an operator-norm contraction, its singular values lie in
`[0,1]`, and therefore

```text
||P_t-M_t||_2^2
 =E_j(1-s_j(M_t))^2
 <=E_j(1-s_j(M_t)^2)=V_t,                                  (NC18)

E_b||C_t(b)-P_t||_2^2
 =V_t+||M_t-P_t||_2^2 <=2V_t.                               (NC19)
```

Combining `(NC14)` and `(NC17)--(NC19)` yields pointwise polar control

```text
sup_t ||P_t-M_t||_2^2 <=7500(A(R)+I(R)),                    (NC20)

E_t||P_t-R_t||_2^2
 <=2A(R)+15000(A(R)+I(R)).                                  (NC21)
```

The four-term Lipschitz inequality then gives explicit, but noncontractive,
sampled-energy comparisons

```text
sqrt(I(P)) <=sqrt(I(R))+4 sqrt(E_t||P_t-R_t||_2^2),          (NC22)

sqrt(A(P)) <=sqrt(A(R))+6 sqrt(E_t||P_t-R_t||_2^2).          (NC23)
```

(The coefficient `6` in `(NC23)` is a safe bound: two edge products contain
four vertices, while the decoded-heap form contains three.)  Thus polar
correction is dimension-free and remains in an `O(sqrt(A+I))` neighborhood,
but these estimates alone increase the constant.  A damped polar/geodesic
step can decrease the alpha energy only if one proves a uniform gradient
inequality

```text
A(R)+I(R) <=C_PL E_t||R_t-M_t||_2^2 + controlled orientation term. (NC24)
```

Identity `(NC16)` shows exactly why consensus is insufficient: all sampled
energy may sit in the conditional variance `E_t V_t`, while the correction
gradient `R_t-M_t` vanishes.  Any contraction proof must bound that variance
by a strict fraction of the original energy after the orientation term is
included, or rule out non-code polar fixed points `P=R`.

### Qualitative ultraproduct attempt

A contradiction sequence with `I(R_n)+A(R_n)->0` gives, in the tracial/Loeb
ultraproduct, a unitary field with the sampled heap identities almost
everywhere.  Gauging at a Fubini-generic anchor makes `Q_x=R_xR_o^*` a
reflection almost everywhere, and `(NC1)` makes `Q_x,Q_y` commute for an
independent uniform pair.  Every bounded affine configuration of pairwise
independent forms therefore has a classical joint spectral model, and the
`4 x 4` ledger above is valid configurationwise.

The remaining removal statement is genuinely **contextual**: pairwise
commutation almost everywhere does not by itself put the whole Loeb field in
one abelian algebra (sparse Pauli anticommutation graphs are the warning).
One must show that the overlapping alpha-plane contexts plus `(NC14)` admit a
single measurable Boolean spectral labeling, to which the scalar
Kaufman--Sudan inequality can be applied.  Equivalently, prove nonabelian
coboundary/agreement removal for this affine-plane complex.  Assuming that
measurable noncontextualization lemma, scalar soundness forces the full
parallelogram identity almost everywhere and yields a nonconstructive uniform
modulus `F=o_(I+A)(1)`.  Without it, the Loeb argument is incomplete rather
than an automatic consequence of Fubini.

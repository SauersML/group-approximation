---
rg: 2
id: monomial-root-conjugacy-proof
kind: route
title: Classify square-zero endomorphisms of the free Leavitt module by three projective summands and apply the Hilbert hotel
target: monomial-root-elements-are-conjugate-in-the-leavitt-group
requires:
  - degree-zero-leavitt-core-characters-are-dirac-haar-mixtures
  - weighted-leavitt-opposite-root-packets-have-finite-models
---

In Steps 1--5, `V=R^12` is a right `R`-module with the standard basis
`e_0,...,e_11`, and `GL_12(R)` acts on the left; the repository's
`GL_12(R)=EL_12(R)` identifies this with `H`. Step 6 transports the
result to `G=EL_3(R)` while fixing the actual root coefficients.

## Step 1: conjugacy of square-zero endomorphisms

Let `N` be an `R`-linear endomorphism of `V` with `N^2=0` such that
`K=ker N` is a direct summand of `V` and `I=im N` is a direct summand of
`K`.  Choose complements `V=C directSum K` and `K=D directSum I`.  Then
`N|_C : C -> I` is an isomorphism (`C cap K=0` and `N(V)=N(C)`), and in
`V=C directSum D directSum I` the endomorphism `N` is the matrix with the
single entry `N|_C` in position `(I,C)`.  If `N'` is another such
endomorphism with data `(C',D',I')` and there are isomorphisms
`alpha:C->C'`, `beta:D->D'`, put `gamma=N'|_(C') alpha (N|_C)^(-1)`;
then `g=alpha directSum beta directSum gamma` is an automorphism of `V`
with `g N g^(-1)=N'`.  So two such endomorphisms are conjugate as soon as
`C ~= C'` and `D ~= D'`.

## Step 2: the three summands for a regular coefficient

Let `y=y z y` with `z in R`, and `N=y E_ij` (`i!=j`), so
`N(v)=y v_j e_i`.  Put `e=yz` and `f=zy`, both idempotents, with
`yR=eR` and `ann_r(y)=(1-f)R` (if `yr=0` then `r=(1-f)r`; conversely
`y(1-f)=y-yzy=0`).  Then

```text
K = { v : y v_j = 0 } = (1-f)R e_j directSum directSum_(l!=j) R e_l,
I = y R e_i = e R e_i,
C = f R e_j,
D = (1-f) R e_j directSum (1-e) R e_i directSum directSum_(l!=i,j) R e_l.   (1)
```

`K` is a summand of `V` and `I` of `K`, and `N|_C` is injective because
`yfr=0` forces `fr=z(yfr)=0`.  Hence Step 1 applies with

```text
C ~= fR,      D ~= (1-f)R directSum (1-e)R directSum R^10.               (2)
```

## Step 3: monomial-type coefficients give free summands

Let `y=s_u b t_v` with `b in B_m` regular, `b^-` a pseudo-inverse in
`B_m`, and put `z=s_v b^- t_u`.  Then `yzy=s_u b b^- b t_v=y`, and

```text
e=yz=s_u (b b^-) t_u,        f=zy=s_v (b^- b) t_v                        (3)
```

are idempotents of the degree-zero matrix algebra `B_(m+|u|)`, resp.
`B_(m+|v|)`.  A nonzero idempotent `g` of `B_n ~= M_(2^n)(F_2)` is
conjugate inside `B_n` to a sum of `r=rank(g)` cylinder idempotents
`s_w t_w`, and `s_w t_w R ~= R` via left multiplication by `s_w`; hence
`gR ~= R^r ~= R` by the Leavitt relation `R ~= R^2`.  Applying this to
`f`, `1-f`, `1-e` (nonzero because `b!=0` and `rank(b)<2^m`... when
`rank(b)=2^m` the summand `(1-f)R` or `(1-e)R` is `0`, which is harmless
since `D` still contains `R^10`), `(2)` gives `C ~= R` and `D ~= R`.

For `y=1` the same computation gives `C=Re_j ~= R`, `D ~= R^10 ~= R`.
By Step 1, `x_ij(y)=1+N` is conjugate to `x_ij(1)=1+E_ij` in
`GL_12(R)=H`.  This is `(MRC2)`.

## Step 4: characters

Characters are conjugation invariant, and `x_ij(1)` lies in the
degree-zero core, where every character equals the constant `w` by
`degree-zero-leavitt-core-characters-are-dirac-haar-mixtures`.  This is
`(MRC3)`.

## Step 5: the mixed order-three elements

Put `M=x_01(s_0)x_10(t_0)` and `M_0=x_01(1)x_10(1)`, both of order three,
acting on the first two coordinates `R^2` and trivially on `R^10`.  A
direct computation gives `Fix(M)={(v_0,0):v_0 in qR} ~= R` and
`(M-1)(R^2)={(s_0x,y)} ~= R^2` with `M` acting there, in the coordinates
`(x,y)`, by `(x,y) -> (y,x+y)`; while `Fix(M_0)=0` on `R^2` and `M_0`
acts on `R^2` by the same matrix.  Since `F_2[Z/3]` is semisimple, an
order-three automorphism of a projective module is determined up to
conjugacy by its fixed submodule and the isomorphism class of the
`F_4 tensor R`-module carried by the complement.  Both complements are
the same module `R^2` with the same action, and the fixed submodules
`R directSum R^10` and `R^10` are both free of rank one.  Hence `M` and
`M_0` are conjugate in `H`, giving `(MRC4)` and, with `(MRC3)`, the equal
`S_3` profiles.

## Step 6: literal transport to rank three

Use the prefix expansion `(WOP8)` with depth r=4, weights `(0,4,0)`,
and N=2^4+2=18. Label its two outer coordinates a,b and its sixteen
middle coordinates by length-four prefixes. The rectangular matrices
T_4,S_4 are the identity on the outer coordinates, so for every y in R,

```text
Phi_4(x_13(y))=x_(a,b)(y),
Phi_4(x_31(y))=x_(b,a)(y).                              (4)
```

These are literal equalities, not identifications of a coefficient
with a corner image or a sum of roots. The same theorem proves that
Phi_4 maps EL_3(R) isomorphically onto EL_18(R): its inverse lifts every
elementary generator, including those between two middle coordinates.

Choose twelve coordinates containing a,b. Relabel the rank-twelve
conjugator from Step 3 so that its distinguished ordered pair is a,b,
and extend it by the identity on the remaining six coordinates.
This is an element c of EL_18(R), since block inclusion sends every
elementary generator to an elementary generator. It satisfies

```text
c x_(a,b)(y) c^-1=x_(a,b)(1).
```

Consequently Phi_4^-1(c) belongs to EL_3(R), and (4) proves (MRC2) for
the outer root. Constant Weyl conjugation in SL_3(F_2) moves this to
every ordered pair of distinct root coordinates. Apply the identical
argument to the conjugator of the two opposite-root products in
Step 5; both factors in each product are preserved by (4). This proves
the rank-three version of (MRC4) too.

For a character of EL_3(R), use the rank-three instance of the core
classification to define w. The constant root and the constant
order-three product are nonidentity elements of that core, so their
character values are w. The transported conjugacies give (MRC3) and
the same value at the nonidentity conjugacy classes of either S_3.
Thus each restriction is exactly w*1+(1-w)*delta_e. No equality between
GL_3(R) and EL_3(R), and no arbitrary-word character classification,
has been used or proved.

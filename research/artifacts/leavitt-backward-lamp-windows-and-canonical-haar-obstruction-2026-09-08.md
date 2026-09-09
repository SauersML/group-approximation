# Finite backward lamp windows and a canonical Haar obstruction

2026-09-08. Written algebra and finite-dimensional trace calculations.
No execution, search, build, or new Lean verification is used.

The native finite-`S_3` enlargement criterion asks for capture of two
fixed observables, near centralization of `L`, and vanishing forward
Haar leakage under the native compressor. This artifact proves that
the finite backward-orbit subgroup algebras have the first two
properties exactly in the canonical representation, while their
forward Haar leakage is at least `5/6` at every stage. Their union
is nevertheless locally finite, and adjoining the compressor gives
an amenable subgroup. No arbitrary algebra enlargement is excluded.

## 1. Native coordinates and the backward embedding

Use `R=L_(F_2)(1,2)` with

```text
s=s_0, t=t_0, a=s_1, b=t_1,
ts=ba=1, ta=bs=0, st+ab=1, e=ab=1-st.
```

Write `H=GL_4(R)=EL_4(R)`, `L=diag(GL_3(R),1)` and
`K=diag(I_3,R^x)`. The established native setup is
[[native-s3-algebra-enlargement-obstructs-scalar-commutants]];
the calculations needed here are repeated below. In particular `L`
and `K` commute exactly. The compressor is

```text
u = [ s 0 0 e    ],        u^(-1) = [ t  0   0   0   ],
    [ 0 s 0 e t  ]                 [ 0  t   0   0   ]
    [ 0 0 s e t^2]                 [ 0  0   t   0   ]
    [ 0 0 0 t^3  ]                 [ e  s e s^2 e s^3].
```

Both products are identity: the only telescoping diagonal identity
needed is `e+s e t+s^2 e t^2+s^3t^3=1`. Direct multiplication gives,
for every `k in R^x`,

```text
u^(-1) diag(I_3,k) u=diag(I_3,psi(k)),
psi(k)=1+s^3(k-1)t^3
      =(1-s^3t^3)+s^3 k t^3.                         (1)
```

Orthogonality of the two corners and `t^3s^3=1` show that `psi`
is an injective group homomorphism; indeed `t^3 psi(k)s^3=k`.
Its iterates are `psi^j(k)=1+s^(3j)(k-1)t^(3j)`.

Let

```text
k_+=diag(I_3,1+a t^3),
k_-=diag(I_3,1+s^3 b),              F_0=<k_+,k_->.
```

For a binary prefix `alpha`, write `s_alpha` for its creation
word and `t_alpha` for the annihilation word in reverse order.
The added terms `s_1 t_000` and `s_000 t_1` are opposite matrix
units on the incomparable leaves `1,000`. They generate exactly
`GL_2(F_2)≅S_3`, acting as identity on the other two leaves of
the complete prefix code `{000,001,01,1}`.

Set `F_j=u^(-j)F_0u^j` for `j>=0`. Its two generators are

```text
k_(+,j)=diag(I_3,1+s^(3j)a t^(3j+3)),
k_(-,j)=diag(I_3,1+s^(3j+3)b t^(3j)).                (2)
```

All these groups lie in `K`. Define

```text
G_m=<F_0,...,F_m>,       G_infinity=union_(m>=0)G_m.
```

## 2. One finite chart for each entire window

Give the complete binary prefix code

```text
C_0=000, C_1=001, C_2=01, C_3=1
```

the structure of a four-letter alphabet. The two endpoints in (2)
are the binary prefixes `0^(3j)1` and `0^(3j+3)`. As words in
this four-letter alphabet they are respectively

```text
0^j3,        0^(j+1).                              (3)
```

Each has length `j+1` in that alphabet. Their unequal binary
lengths therefore do not prevent a common finite chart.

Fix `m>=j`. Refine both endpoints in (3) by every suffix in
`C^(m-j)`. Completeness of this suffix code gives the exact identity

```text
s_alpha t_beta
 =sum_(w in C^(m-j)) s_(alpha w)t_(beta w).          (4)
```

The matrix units `s_v t_w`, for `v,w in C^(m+1)`, span an
embedded unital constant matrix algebra

```text
D_m ≅ M_(4^(m+1))(F_2) subset R.
```

They are genuine matrix units because the code is complete and
prefix-free. Their linear independence follows by multiplying a
proposed relation on the left by `t_v` and on the right by `s_w`.
Equation (4) puts every generator of `G_m` in `D_m^x`.
For `j<m` it is a product of disjoint transvections after refinement,
rather than a single elementary matrix. Thus

```text
G_m <= GL_(4^(m+1))(F_2),                           (5)
```

so `G_m` is finite. Refining every leaf by the four code words
identifies the inclusion `D_m -> D_(m+1)` with `A -> A tensor I_4`.
These are compatible charts for all stages, not separate unrelated
finite representations.

Every finite subset of `G_infinity` lies in some finite `G_m`.
Consequently `G_infinity` is locally finite and amenable: for any
fixed finite subset, a sufficiently large `G_m` is invariant under
left translation by that subset and hence is a Følner set.

There is also an exact amenable extension. By (1),
`u^(-1)G_infinity u subset G_infinity`, so the subgroups
`u^rG_infinity u^(-r)` increase with `r>=0`. Their union `N`
is locally finite, is invariant under conjugation by `u` in both
directions, and is normal in `Gamma_0=<u,G_infinity>`.

The element `u` has infinite order. For `p=diag(I_3,0)`,

```text
u^j p u^(-j)=diag(s^j t^j,s^j t^j,s^j t^j,0).
```

These idempotents strictly decrease: the consecutive difference
has diagonal `s^j e t^j!=0`, since sandwiching by `t^j,s^j`
returns `e!=0`. Since every element of `N` has finite order,
no nonzero power of `u` belongs to `N`. Therefore

```text
Gamma_0=N semidirect <u>,        Gamma_0/N ≅ Z.     (6)
```

An extension of an amenable group by `Z` is amenable, so `Gamma_0`
is amenable. This describes only the lamp-compressor subgroup;
it does not include the remaining generators from `L`.

## 3. Exact Haar leakage for finite group algebras

Let `G,T` be finite subgroups of any discrete group `Gamma`.
Work in its canonical group von Neumann algebra with
`tau(lambda(g))=1` for `g=1` and zero otherwise. Let `E_G,E_T`
be the trace-preserving expectations onto the finite-dimensional
complex group algebras `A_G,A_T`.

The vectors `lambda(g)` form an orthonormal group basis in `L^2`.
These expectations select its coordinates in the indicated finite
subgroup. Hence, as Hilbert-space projections,

```text
E_G E_T=E_(G intersect T),
Tr_(Hilbert)(E_G E_T)=|G intersect T|.              (7)
```

Here `Tr_(Hilbert)` is an unnormalized finite-rank operator trace,
distinct from the normalized ambient trace `tau`.

Put `M=|G|`. The canonical trace on
`C[G] ≅ direct_sum_(chi) M_(d_chi)(C)` assigns mass
`d_chi^2/M` to the `chi` block, where `d_chi` is the irreducible
degree. Thus its matrix units become orthonormal when multiplied
by `sqrt(M/d_chi)`. For a Haar unitary in that block, the variance
of each resulting coordinate is

```text
(d_chi/M) integral |v_ab|^2 dv=1/M.
```

Cross-covariances vanish, also between distinct independently Haar
distributed blocks. The Haar covariance of `v in U(A_G)` on
the whole `L^2` space is therefore exactly `E_G/M`. Consequently

```text
alpha(A_G,A_T)
 :=integral_(v in U(A_G)) ||v-E_T(v)||_2^2 dv
  =1-Tr_(Hilbert)(E_T E_G)/M
  =1-|G intersect T|/|G|.                          (8)
```

In particular, if `|G|=|T|`, the forward and reverse Haar means
are equal. This calculation concerns the finite group algebras
themselves, not the expectations obtained by averaging onto their
commutants.

## 4. The conjugate S3 has trivial intersection with K

Conjugation of the two generators in Section 1 gives

```text
u k_+u^(-1)=x_14(a),
u k_-u^(-1)=x_41(b).                               (9)
```

We check the entire finite subgroup intersection, not just its
two generators. Use the matrix units inside `M_4(R)`

```text
f_11=e E_11,       f_12=a E_14,
f_21=b E_41,       f_22=E_44,       r=f_11+f_22.
```

The relations `ab=e,ba=1` show that these are a nonzero copy
of the four matrix units of `M_2(F_2)` with identity `r`.
Thus `F_(-1):=uF_0u^(-1)` consists exactly of the six elements

```text
1-r+alpha f_11+beta f_12+gamma f_21+delta f_22,
[ alpha beta; gamma delta ] in GL_2(F_2).          (10)
```

Membership in `K=diag(I_3,R^x)` requires the first diagonal
coordinate to be `1` and both off-diagonal coordinates to vanish.
Since `e,a,b` are nonzero, this forces
`alpha=1,beta=gamma=0`. Invertibility of the binary two-by-two
matrix then forces `delta=1`. Thus

```text
F_(-1) intersect K={1}.                            (11)
```

## 5. Six cosets force a fixed leakage at every stage

Set `T_m=uG_m u^(-1)` and `J_m=G_m intersect T_m`.
The finite groups `T_m,G_m` have the same order. Moreover
`F_(-1) subset T_m`, while `J_m subset K`. By (11), the six
elements of `F_(-1)` determine six distinct cosets of `J_m`
in `T_m`: equality of two such cosets would put their quotient
in `F_(-1) intersect J_m={1}`. Hence

```text
[T_m:J_m]>=6,
|J_m|/|G_m|<=1/6.                                  (12)
```

In the canonical representation of `H`, put
`A_m=C[G_m]` and `B_m=uA_m u^(-1)=C[T_m]`.
Equation (8) now proves the exact formula and bound

```text
alpha_m=integral_(v in U(A_m))||v-E_(B_m)(v)||_2^2 dv
       =1-|J_m|/|G_m| >=5/6.                       (13)
```

The reverse Haar mean is the same. Both corresponding supremum
leakages over operator-norm contractions equal `1`: choose a group
element in one of the two subgroups outside their proper intersection.
Its unitary has expectation zero onto the other group algebra.

For `m>=1`, `T_m` contains `G_(m-1)` because conjugation moves
`F_j` to `F_(j-1)`. This large-looking overlap does not imply
small Haar leakage; (12) measures the relevant relative dimension.
We do not assert the stronger intersection equality
`J_m=G_(m-1)`.

Every `A_m` contains the fixed `S_3` and commutes exactly with
`L`, since `G_m subset K`. Thus the first two requirements in
[[native-s3-algebra-enlargement-obstructs-scalar-commutants]] hold
exactly in this representation. The third fails uniformly by (13).

## 6. Fixed-stage matrix transfer and the correct diagonal quantifier

Suppose `phi_n` is a full canonical matrix microstate sequence of
`H`; normalized matrix trace is always used. Fix `m`. Suppose
there are exact representations

```text
sigma_(n,m):G_m -> U(d_n)
```

whose value on each `g in G_m` is at normalized-HS distance tending
to zero from a fixed native literal-word evaluation of `g`.
Let `U_n` be the native evaluation of `u` and put

```text
A_(n,m)=sigma_(n,m)(C[G_m]),
B_(n,m)=U_n A_(n,m) U_n*.
```

Finite-group exactification is granted as a hypothesis here, not
asserted with any uniform dependence on `m`.

For fixed `m`, canonicality gives

```text
tr(sigma_(n,m)(g)) -> 1_(g=1),
<sigma_(n,m)(g),U_n sigma_(n,m)(h) U_n*>
 -> 1_(g=u h u^(-1))                               (14)
```

for every `g,h in G_m`. The finite group bases consequently have
Gram matrices converging to identity, so they are eventually
linearly independent. The images are then faithful copies of the
full complex group algebra. Their central block trace masses tend
to `d_chi^2/|G_m|`, by the finite character formula for central
idempotents and the first limit in (14).

For a block of degree `d_chi` and physical trace mass `t_(chi,n)`,
the Haar covariance equals `t_(chi,n)/d_chi^2` times the Hilbert
projection onto that block. It therefore converges, at this fixed
finite stage, to `E_(A_(n,m))/|G_m|` in finite-rank trace norm.
The Hilbert projection overlap converges to `|J_m|`: projection
matrices onto a fixed finite list of independent vectors depend
continuously on its Gram matrix, and (14) supplies all within-list
and cross-list Gram entries. Applying the covariance calculation
from Section 3 proves

```text
alpha_(n,m) -> alpha_m >=5/6             (m fixed). (15)
```

The capture errors for `k_+,k_-` tend to zero at every fixed
stage. The Haar commutator energies with each fixed generator of
`L` also tend to zero. To see the required uniformity within the
fixed algebra, expand a contraction in the group basis. Its
coefficient Euclidean norm is at most `1+o(1)` by Gram convergence,
so its coefficient absolute sum is at most
`sqrt(|G_m|)(1+o(1))`. Each of the finitely many group-basis
commutators tends to zero because `[L,G_m]=1`. This proves uniform
commutator convergence over the contraction ball at fixed `m`.

If such exactifications are supplied for every fixed stage, choose
increasing thresholds so that, past the threshold for stage `m`,
its capture error, its finite `L` energy sum, and
`|alpha_(n,m)-alpha_m|` are all at most `1/(m+1)`.
A stepwise diagonal `m(n)->infinity` growing no faster than these
thresholds then satisfies

```text
capture error ->0,       L energy ->0,
liminf_n alpha_(n,m(n)) >=5/6.                      (16)
```

The same conclusion holds for any diagonal on which those
fixed-stage estimates are controlled in this manner. There is no
claim here that an arbitrary prescribed fast-growing `m(n)` has
the limits in (15) uniformly; canonical microstates control each
fixed finite word set, not all growing word sets at once.

The obstruction is therefore specific and quantitative. Backward
lamps really do generate a locally finite subgroup, and the
lamp-compressor subgroup really is amenable, but their canonical
finite-subgroup algebras retain a fixed Haar boundary. A different
algebra construction would still need to prove the missing forward
inclusion property. No scalar-commutant contradiction or
nonhyperlinearity theorem follows from the construction above.

# A center-normalizer rounding criterion for the native heat maps

2026-09-08. Written finite-dimensional arguments. No code, build, or
Lean verification was run. The criterion is conditional: it does not
establish hyperlinearity or nonhyperlinearity of `H=L_(F_2)(1,2)^x`.

The group `H` is infinite simple and nonsofic by the repository's
established results. We use its actual compressor `u` and the heat maps
`P_n,Q_n=Ad(U_n)P_n Ad(U_n*)` from
[the native heat-rounding obstruction](leavitt-heat-rounding-forces-unbounded-trace-distortion-2026-09-08.md).
For hypothetical full canonical microstates these satisfy

```text
delta_n=||Q_n P_n-P_n||_(infinity->2) -> 0,
rho_n=||P_n Q_n-Q_n||_(infinity->2) -> 1.             (1)
```

The second limit uses the full canonical microstate assumption. It is
not inferred from only the fixed finite certificate rows.

## 1. Exact center normalizers give weighted permutation models

Let `Z` be a unital finite-dimensional abelian subalgebra of `M_n`,
with minimal projections `p_i` of ranks `r_i`. A unitary normalizing
`Z` permutes its atoms and preserves their ranks. Replace atom `i`
by the `r_i` labels `(i,1),...,(i,r_i)`. The induced permutation
acts on the resulting `n`-point set by

```text
(i,j) -> (pi(V)(i),j).
```

This construction is a homomorphism from the unitary normalizer of
`Z` to `Sym(n)`. Its normalized Hamming metric is precisely atom
movement weighted by the physical traces `r_i/n`.

For normalizers `V,W`, the diagonal block of `V*W` on every moved
atom is zero. On the fixed atoms the real trace is at most their
total rank. Therefore

```text
d_Ham(pi(V),pi(W)) <= (1/2)||V-W||_2^2.              (2)
```

Suppose now that the finitely many generator matrices of an asymptotic
HS representation of `H` normalize some `Z_n` exactly. Every literal
word matrix then normalizes `Z_n`, and (2) sends each native relation
defect to a vanishing Hamming defect. This gives a homomorphism from
`H` into a permutation metric ultraproduct.

Any nontrivial such homomorphism would be injective by simplicity and
would make `H` sofic. Consequently, for every fixed native word `g`,

```text
mu_(g,n)=sum_(i:pi(V_n(g))(i)!=i) tr_n(p_i) -> 0.    (3)
```

The assertion is an ordinary limit: a subsequence with movement bounded
away from zero would give a nontrivial ultraproduct homomorphism.
No separation of atom permutations is inferred merely from canonical
traces of the original unitary matrices.

## 2. Reversal on center atoms fixed by the compressor

Let `A` be a unital finite-dimensional subalgebra of `M_n`, let
`E=E_A`, and suppose that `U` normalizes `Z(A)`. Put

```text
B=U A U*,       F=E_B,
delta=||F E-E||_(infinity->2),
mu=sum_(center atoms p_i moved by U) tr_n(p_i).
```

On each center atom fixed by `U`, the restricted algebra `A_i` is
a matrix factor and `B_i=U_i A_i U_i*`. The matrix-factor case of
[finite-algebra reversal](leavitt-regular-trace-cp-reversal-2026-09-08.md)
gives reverse defect at most `sqrt(2)` times forward defect in that
block, using its normalized trace.

The inputs optimizing distinct blocks can be chosen independently and
assembled into one block diagonal contraction. Thus the sum of their
forward squared defects, weighted by physical block trace, is at most
`delta^2`. The corresponding reverse contribution is at most
`2 delta^2`.

The sum of all moved atoms is also `U`-invariant. On that complement,
`(E-I)F` has `2->2` norm at most one, and `F` sends the operator
unit ball to itself. Its squared contribution is at most the trace
`mu` of the complement. Both expectations annihilate the off-diagonal
blocks between center atoms. Hence

```text
||E F-F||_(infinity->2)^2 <= 2 delta^2+mu.           (4)
```

No bound on the distortion of the central trace weights is needed.
The normalizer hypothesis, rather than a claim that two rounded
algebras are mutual commutants, is the extra input in (4).

## 3. The sufficient rounding statement for the actual H

Suppose a hypothetical full canonical microstate sequence admits
unital finite-dimensional subalgebras `A_n` with

```text
eta_n=||E_(A_n)-P_n||_(infinity->2) -> 0,            (5)
```

and that every native generator matrix normalizes `Z(A_n)` exactly.
Let `F_n=Ad(U_n)E_(A_n)Ad(U_n*)`. Comparing the heat maps with
these expectations costs at most `3 eta_n` in either direction.
Equations (3)--(4), applied to the fixed compressor word, give

```text
rho_n <= 3 eta_n
       +sqrt(2(delta_n+3 eta_n)^2+mu_(u,n)) -> 0.
```

This contradicts (1). Thus no canonical microstate sequence for `H`
can satisfy both (5) and this simultaneous center-normalizer condition.
A theorem guaranteeing these two properties for a hypothetical
sequence would prove nonhyperlinearity.

One may instead allow the finitely many generator matrices to be
changed by `o(1)` in normalized HS norm into exact normalizers of
the same `Z(A_n)`. These changes preserve every fixed native word
relation and canonical trace asymptotically. Let `U_tilde_n` be the
new compressor word and `h_n=4||U_tilde_n-U_n||_2 -> 0`.
For any expectation `E`,

```text
||Ad(U_tilde_n)E Ad(U_tilde_n*)-Ad(U_n)E Ad(U_n*)||_(infinity->2)
 <= h_n.
```

The same argument then gives

```text
rho_n <= 3 eta_n+h_n
 +sqrt(2(delta_n+3 eta_n+h_n)^2+mu_(u_tilde,n)) -> 0. (6)
```

This comparison changes only the conjugated expectations. It does not
require perturbing a heat map at a growing heat time.

## 4. What the native identities have not supplied

Commutation of the native `L,K` and their conjugating corner swap
gives relations between their adjoint heat maps. Rounding those maps
to expectations does not by itself prove that all native generators
normalize the center of one rounded algebra. Nor does commutation of
two expectations imply that their ranges are mutual commutants or
that their centers are equal. Shared external commutants and the
[diagonal embedding obstruction](leavitt-diagonal-external-commutant-obstruction-2026-09-08.md)
must still be allowed.

There is some exact center commutation available in any finite
ambient algebra. If native corner groups `H_p,H_q` are nested, their
relative commutants are oppositely nested, so their centers commute.
If the groups commute, then `Z(D_p) <= D_q` and `Z(D_q) <= D_p`,
where `D_p=pi(H_p)' intersect M`; their centers again commute.
This does not cover all conjugate corners. Even in `M_2(R)`, take
`p=e_11`, `g=I+e_12(1)`, and `q=g p g^(-1)=e_11+e_12(1)`.
Then `p q=q` but `q p=p`. Thus these two native ring idempotents
cannot both be sums from one orthogonal idempotent decomposition.
This rules out an ordinary simultaneous support-refinement argument;
it does not prove that the associated external commutant centers
fail to commute. A further native theorem would still be needed to
obtain one abelian algebra normalized by the full group.

Even approximate normalization of a fixed abelian algebra need not
admit a small exact-normalizer correction when atom ranks differ.
For example, in dimension `2m+1`, take atoms of ranks `m,m+1`.
Let `U` exchange an `m`-dimensional part of each atom and fix the
remaining one-dimensional line. For `Z=Cp+C(1-p)`, direct calculation
gives

```text
||(I-E_Z)Ad(U)|_Z||_(infinity->2)^2
 =4m/((2m+1)(m+1)) -> 0.
```

Every exact normalizer must preserve the two atoms, since their ranks
are unequal. For every such unitary `W`,

```text
||U-W||_2^2 >= 2-2/(2m+1) -> 2.
```

This example is a finite-algebra warning about normalizer correction,
not a native model of `H`. Altering the center or establishing a
special native normalization theorem could evade it. Neither such
construction is asserted here. The missing hypothesis in the
sufficient criterion is precisely the simultaneous normalization in
Section 3, in addition to the uniform expectation approximation (5).

## 5. Exact native corner centers need not commute, even in a factor

There is an exact representation of this same `H` in a finite factor
with canonical character and scalar whole-`H` relative commutant for
which two conjugate native corner centers do not commute. The
construction below and its centralizer calculation were independently
audited. No embeddability assertion is made for the resulting factor.

Use the native rank-four realization and set

```text
p=diag(I_3,0),
S=H_p=L={diag(A,1):A in GL_3(R)},
K=H_(1-p)={diag(I_3,k):k in R^x},
D=S K ~= S times K,
g=I_4+e_34,          q=g p g^(-1)=p+e_34.
```

Here `g` is an elementary transvection; the notation `u` remains
reserved for the compressor in the earlier sections. The group
centralizer is `C_H(S)=K`, and `D` is the stabilizer of the ring
idempotent `p`. The group `S` is infinite simple, and `D` normalizes
it. These are the native block-group facts proved in
[the internal centralizer artifact](leavitt-internal-kazhdan-gap-and-external-commutant-2026-09-08.md).

Let `V=H/D` be the left coset space. For `v=hD`, define
`S_v=h S h^(-1)`; this is well-defined because `D` normalizes `S`.
Write `D_v=h D h^(-1)` for the vertex stabilizer. Define an
`H`-invariant symmetric form on distinct vertices by

```text
b(v,w)=0  if S_v <= D_w or S_w <= D_v,
b(v,w)=1  otherwise,
b(v,v)=0.
```

Now form the class-two group `N` with generators `c,z_v (v in V)`
and relations

```text
c^2=1,        c central,
z_v^2=1,      [z_v,z_w]=c^(b(v,w)).                 (7)
```

This presentation has a concrete finite-support normal form, so
`c` is nonidentity. Choose any order on `V`, put
`A=direct_sum_V F_2`, and define the bilinear form

```text
F(a,b)=sum_(v>w) a_v b_w b(v,w) in F_2.
```

The group law on `A times F_2` is
`(a,t)(b,s)=(a+b,t+s+F(a,b))`. Take `z_v=(1_v,0)` and
`c=(0,1)`. Bilinearity gives associativity and the stated relations.
Conversely the relations put every word into a unique ordered
finite-support normal form. Every finitely generated subgroup of
`N` is finite, so `N` is locally finite. The permutation action of
`H` on the generators preserves (7), giving an action by
automorphisms fixing `c`. Set

```text
Gamma=N semidirect H.
```

All native identities of `H` are retained by its subgroup inclusion.

### Centralizer centers in the extension

Put `v_0=D` and `z_0=z_(v_0)`. An element `n h` of `Gamma`
centralizes `S` exactly when `h in C_H(S)=K` and `n` is fixed by
`S`. Thus

```text
C_Gamma(S)=N^S semidirect K.                       (8)
```

The image of an `S`-fixed element of `N` in `A` has finite
`S`-invariant support. An infinite simple group has no nontrivial
action on a finite set, so that support consists of vertices fixed
individually by `S`. Since `S` fixes `c` and each lamp at a fixed
vertex, the normal form gives the exact equality

```text
N^S=<c,z_v : S fixes v>.
```

For every such vertex, `S <= D_v`; the definition of `b` makes
`z_0` commute with its lamp. Also `K<=D` fixes `v_0`, so `K`
commutes with `z_0`. Equation (8) therefore proves

```text
z_0 in Z(C_Gamma(S)).                             (9)
```

Conjugation gives the same assertion for each `S_v` and its lamp
`z_v`.

These are also central elements of the full von Neumann relative
commutants. For any infinite simple subgroup `T<=Gamma`, every
finite `T`-conjugacy orbit is a singleton. Fourier coefficients of
an element commuting with `lambda(T)` are constant on these
orbits, and square summability kills all infinite orbits. Hence

```text
lambda(T)' intersect L(Gamma)=L(C_Gamma(T)).        (10)
```

In particular `lambda(z_v)` is central in the full relative
commutant of `lambda(S_v)`.

### A noncommuting pair of native corner centers

Choose any `a in R^x` with `a!=1`. The element
`h_a=diag(1,1,a,1)` lies in `S`, using `GL_3(R)=EL_3(R)`.
The `(3,4)` entry of `g h_a g^(-1)` is `a+1!=0`, so
`g S g^(-1)` is not contained in `D`. Since `g^2=1`, this also
shows `S` is not contained in `g D g^(-1)`. Therefore

```text
b(D,gD)=1,        [z_0,z_(gD)]=c!=1.               (11)
```

The two lamps lie in the respective centers for the native corner
groups `H_p` and `H_q`. In the canonical trace on `L(Gamma)`,

```text
||lambda(z_0)lambda(z_(gD))
  -lambda(z_(gD))lambda(z_0)||_2=sqrt(2).          (12)
```

### A finite factor with scalar whole-group commutant

The coset space `V` is transitive and infinite: `D` is proper,
as witnessed by `g`, and an infinite simple group has no proper
finite-index subgroup. Thus its finite-support permutation module
has `A^H=0`, giving `N^H=<c>`. Since `Z(H)=1`,

```text
C_Gamma(H)=<c>,
lambda(H)' intersect L(Gamma)=L(<c>).              (13)
```

Let `e=(1-lambda(c))/2`, a central projection of trace `1/2`, and
equip `M=e L(Gamma)` with trace `tau_M=2 tau|_M`. The unitary
representation

```text
pi(h)=e lambda(h),       h in H,
```

has the canonical character: `tau_M(pi(h))=delta_(h,1)`, since
`c h` is never the identity for `h in H`. Equation (13) gives
`pi(H)' intersect M=C e`. In particular `M` is a finite factor;
it contains the canonical infinite-dimensional `L(H)`, so it is
a type `II_1` factor.

The unitaries `x_0=e lambda(z_0)` and
`x_1=e lambda(z_(gD))` remain central in the respective full
relative commutants of `pi(H_p)` and `pi(H_q)`. Since `e lambda(c)=-e`,

```text
x_0 x_1=-x_1 x_0,
||x_0 x_1-x_1 x_0||_(2,tau_M)=2.                  (14)
```

Also `pi(g)x_0 pi(g)^*=x_1`. Thus `pi(g)` does not normalize the
center of `pi(H_p)' intersect M`; if it did, the two displayed
unitaries would belong to one abelian center and would commute.
In particular, the centers of all conjugate native corner
commutants cannot be contained in a common abelian algebra in
this representation.

The example respects the actual `H`, its canonical character, its
native corner groups, and all its group-word identities. It shows
that simplicity, character rigidity, the commuting complementary
corners, and factoriality of the ambient representation do not alone
imply common abelian corner centers. It does not furnish matrix
microstates or uniform expectation rounding: no Connes-embeddability
claim is made for `M` or `L(Gamma)`, even conditionally on
hyperlinearity of `H`. Local finiteness of the kernel `N` is not
being used as an unproved amenable-kernel closure principle. A
special matrix-approximation argument or a choice of a different
embedding remains possible; the criterion in Section 3 is still
conditional.

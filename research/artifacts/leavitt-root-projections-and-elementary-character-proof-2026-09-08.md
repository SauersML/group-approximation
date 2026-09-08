# Root fixed projections give an elementary full-character proof

2026-09-08. Written algebra and finite-trace arguments. No numerical
experiment, build, or new Lean verification is asserted.

Let `R=L_(F_2)(1,2)` and `H=R^x`. The established prefix-code
identification and elementary-group theorem give

```text
H = GL_4(R) = EL_4(R).
```

Fix this identification using the four depth-two cylinders. Let
`R_0` be the degree-zero ring, the increasing union of
`B_m=M_(2^m)(F_2)` with the usual diagonal inclusions. Inside the
displayed `EL_4(R)`, put

```text
U_ij={I+a E_ij : a in R_0},    i!=j,
u=I+E_12.
```

The main new statement is that in every tracial GNS representation of
`H`, the fixed projections of all twelve groups `U_ij` are equal to
the fixed projection of the entire group. Its trace is exactly
`phi(u)`. The proof uses square-zero matrices over finite fields and
equal traces of nested projections; it does not use a classification
of characters of the degree-zero core or finite-simple-group
character bounds.

Combining this projection theorem with the explicit corner argument
below proves

```text
phi = phi(u) * 1 + (1-phi(u)) * delta_1,
0 <= phi(u) <= 1.                                      (1)
```

This supplies another written proof of the full character simplex.
It leaves embeddability of the regular character open.

## 1. The precise conjugacy class used in the argument

For every positive integer `r`, a complete binary prefix code with
`r` leaves realizes `R^r ~= R` as right modules. This assertion is
used only for positive ranks.

Consider a nonzero square-zero matrix `N` over `F_2` on `F_2^d`,
with rank `r` and with `d-2r>0`. A finite-field Jordan basis splits
the scalar-extended right module into

```text
image I ~= R^r,   moving complement C ~= R^r,
fixed homology D ~= R^(d-2r),
```

where `N:C -> I` is an isomorphism and `N` vanishes on `I+D`.
All three displayed modules are nonzero free modules. Compress each
to `R`, choosing the image isomorphism to intertwine `N|C`. This
identifies `I+N` with one elementary Jordan block plus one fixed
free summand. The same description holds for the chosen `u` in
`GL_4(R)`, whose image and moving complement have rank one and
whose fixed homology has rank two.

Consequently their images in `H` are conjugate. To see that the
conjugator is an element of `H`, use the fixed prefix-module
isomorphisms from each total free module to `R`; compose them with
the constructed intertwiner. This gives an automorphism of the
right module `R`, hence left multiplication by a unit of `R`.
There is no claim that a zero homology summand can be compressed
to a nonzero one.

Define the row and column groups

```text
W_i^row={I+sum_(j!=i) a_j E_ij : a_j in R_0},
W_j^col={I+sum_(i!=j) a_i E_ij : a_i in R_0}.           (2)
```

They are infinite elementary abelian two-groups. Every nonidentity
element of any group in (2) is conjugate in `H` to `u`.
Indeed, put its finitely many coefficients in a common `B_m`, and
write `t=2^m`. Its nilpotent part is a nonzero square-zero scalar
matrix of size `4t`, of rank at most `t`: it has just one block
row, or one block column. Thus its rank is positive and its fixed
homology dimension is at least `2t>0`. The preceding construction
applies. In particular every nonidentity element of each `U_ij`
is conjugate to `u`.

The conjugacies here take place in the full group `H`, not
necessarily in its degree-zero subgroup.

## 2. Equal fixed projections, before any character classification

Let `phi` be any normalized positive-definite class function on `H`,
and let `(pi,M,tau)` be its tracial GNS realization, with faithful
normal trace on `M=pi(H)''`. Put `b=phi(u)`.

For any one of the locally finite groups `L` in (2), or any `U_ij`,
take an increasing sequence of finite subgroups `L_m` exhausting it.
The averages

```text
P_(L_m)=|L_m|^(-1) sum_(x in L_m) pi(x)
```

are decreasing orthogonal projections, with strong limit `P_L`
equal to the projection onto the `L`-fixed vectors. Section 1 gives

```text
tau(P_(L_m))=|L_m|^(-1)+(1-|L_m|^(-1))*b.
```

The orders tend to infinity, so normality of the trace implies

```text
tau(P_L)=b,             0<=b<=1.                       (3)
```

Since `U_ij` lies in both `W_i^row` and `W_j^col`, their fixed
projections satisfy

```text
P_(W_i^row) <= P_(U_ij),
P_(W_j^col) <= P_(U_ij).
```

All three have trace `b`. A positive projection difference of zero
faithful trace vanishes. Hence these three projections are equal.
The bipartite incidence graph with row vertices `i`, column vertices
`j`, and edges `i!=j` is connected for four indices. It follows that
every projection just considered is one common projection `P`.

Now let `h=x_ij(a)` be any elementary generator of `EL_4(R)`, with
`a` in the full ring `R`. Choose `k` distinct from `i,j`.
The generator `h` commutes with `U_ik`, by multiplication of matrix
units. Therefore `pi(h)` commutes with its finite averages and with
`P_(U_ik)=P`. All elementary generators commute with `P`, so `P`
is central in `M`.

The representation on `P` kills every `U_ij`. Its kernel is a
normal subgroup of the simple group `H` containing `u!=1`, hence
is all of `H`. Thus

```text
pi(g)P=P for all g in H.                              (4)
```

Conversely every `H`-fixed vector is `U_12`-fixed. Therefore `P`
is exactly the `H`-fixed projection, and its trace is `phi(u)`.
In particular this proves the full group's trivial weight directly.

If `b<1`, the complementary normalized character is

```text
chi(g)=tau((1-P)pi(g))/(1-b),
chi(u)=0.                                             (5)
```

The next two sections prove that the single equality in (5) already
forces `chi=delta_1`; no assertion about all core character values
is needed first.

## 3. One root of trace zero forces vanishing in proper corners

Write the ring generators as `s_0,s_1,t_0,t_1`, with
`t_i s_j=delta_ij` and `s_0t_0+s_1t_1=1`. Every nonzero `a in R`
has a monomial sandwich `bac=1`. Here is a direct construction.
Expand all ghost lengths to a common `N`, so

```text
a=sum_(|beta|=N) P_beta(s_0,s_1)t_beta.
```

At least one collected formal polynomial is nonzero. List its
distinct words `alpha_1,...,alpha_l`. A sufficiently long prefix
`gamma` of a non-eventually-periodic binary sequence makes the
words `alpha_i gamma` pairwise incomparable. Prefix cancellation
then gives `t_(alpha_1 gamma) a s_(beta gamma)=1`.

Let `p` be a nonzero proper diagonal cylinder projection and take
`h in H_p\{1}`, where `H_p={1-p+v : v in (pRp)^x}`. A finite
prefix refinement writes

```text
h=G=diag(A,I_l),       A!=I_m,       l>=2.
```

Choose `a=(A-I)_(ij)!=0` and a sandwich `bac=1`. Let `z` be one
spare coordinate. For a ghost prefix `d=t_alpha`, set

```text
k_d=I+E_(zi)db,       G_d=k_d G k_d^(-1).
```

For distinct equal-length prefixes `alpha,beta`, direct block
multiplication gives

```text
G_d^(-1)G_(d')=I+e_z v,
v=(d+d')b row_i(A-I),
v_j c s_alpha=1.                                      (6)
```

Thus `v:R^m -> R` has a right inverse column `r`. Its nilpotent
map has image `e_zR`, moving complement `rR`, and fixed homology
`ker(v)+R^(l-1)`. Since `ker(v)+R ~= R^m`, the second spare
coordinate makes the homology free of positive rank `m+l-2`.
Choose an intertwiner on these three summands exactly as in
Section 1. This conjugates (6) to `u` in `H`, and consequently
its character is zero by (5).

Taking arbitrarily many distinct equal-length ghost prefixes gives
arbitrarily many orthonormal vectors `pi(G_d)` in the tracial
Hilbert space. Every vector has trace `chi(h)`. Averaging `q` of
them gives `|chi(h)|<=q^(-1/2)`. Hence

```text
chi(h)=0 for every h in H_p\{1}.                      (7)
```

## 4. Localization extends root-zero regularity to the whole group

For any `g in H`, choose finite prefix expressions for `g` and its
inverse, with all prefix lengths at most `D` and with at most `M_0`
terms in total. For a cylinder `e=e_alpha` at depth `n>D`, the
left supports of `g e` and the right supports of `e g^(-1)` are
contained in at most `M_0` cylinders, each of length at least `n-D`.
Together with `e`, their union is a diagonal projection `p` of
Bernoulli measure at most `(M_0+1)2^(D-n)`.

For sufficiently large `n`, this is a proper projection and

```text
e<=p,       ge=pge,       eg^(-1)=eg^(-1)p.
```

It follows by writing `k-1=e(k-1)e` that
`H_e` and `g H_e g^(-1)` both lie in `H_p`. The same `p` works
for every `k in H_e`. The measure only counts cylinder supports;
no measure preserved by the group action is assumed.

If `g!=1`, at every depth some `H_e` fails to centralize `g`.
Otherwise choose in each corner the two-child order-three unit
`q_e` represented by `[[0,1],[1,1]]`. The element `q_e-e` is
invertible in `eRe`. Commutation with `1-e+q_e` forces both
off-diagonal Peirce blocks of `g` at `e` to vanish. Thus `g`
commutes with every cylinder projection. Each `ege` is a unit
centralizing `(eRe)^x ~= H`, whose center is trivial by simplicity.
So `ege=e` for every cylinder at this depth, giving `g=1`.

Choose such an `e` at a depth where the preceding proper support
bound holds. Its conjugation orbit of `g` is infinite: a finite
orbit gives a homomorphism from the infinite simple group `H_e`
to a finite symmetric group, which must be trivial and would make
the orbit a singleton. For arbitrarily many distinct conjugates
`g_i=k_i g k_i^(-1)`, with `k_i in H_e`, one has

```text
g_i g_j^(-1)=k_i [g(k_i^(-1)k_j)g^(-1)] k_j^(-1)
            in H_p\{1}                 for i!=j.
```

Equation (7) makes their tracial Hilbert-space vectors orthonormal.
The same averaging argument proves `chi(g)=0`. This proves
`chi=delta_1`, and (1) follows from (4)--(5), including the case
`b=1` where faithfulness already gives `P=1`.

## 5. Dependency and approximation boundary

The algebraic inputs are the prefix identities, `GL_4(R)=EL_4(R)`,
and simplicity of `H`, recorded in
[the unit-group identification](../leavitt-gl-equals-el-and-perfect-unit-group.md)
and [the simplicity proof](../binary-leavitt-elementary-group-is-simple-proof.md).
The corner construction is included above so that the proof does not
depend on a core-character classification indirectly through a route.
Its two localization steps agree with the separately audited
full-character proof in the research tree.

Everything here holds in arbitrary finite tracial von Neumann algebras,
including the group algebra of the regular representation. It therefore
does not rule out regular matrix microstates or prove a positive
dimension-independent relation gap. The improvement is removal of the
finite-core character theorem from the full-group proof, together with
the explicit identification of all root fixed projections and the
single scalar `phi(u)` as the entire trivial weight.

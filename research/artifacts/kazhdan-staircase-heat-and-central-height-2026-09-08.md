# A canonical Kazhdan realization of the staircase expectations

2026-09-08. Written finite-representation and matrix proof. No
computation, build, or new Lean verification is asserted.

An abstract staircase of nested block algebras can be averaged by
finite groups that change with its number of levels. Here the
staircase is the exact commutant of representations of one fixed
property-(T) group, with canonical limiting character and one fixed
finite generator list. This supplies uniformly bounded Kraus rank at
each fixed approximation tolerance, despite the full staircase
asymmetry and central-height behavior.

All matrix traces below are normalized. The norm `infinity->2` tests
the whole operator unit ball.

## 1. Projective augmentation factors and their characters

Put `Gamma=SL_3(Z)`. For each integer `n>=2`, choose distinct primes
`p_1,...,p_n`, with `p_n->infinity` as `n->infinity`. The primes may
depend on `n`; subscripts suppress that additional dependence. Let
`G_l=SL_3(F_(p_l))` and let `sigma_l` be its complex permutation
representation on projective points, with constants removed. Its degree is

```text
r_l=(p_l^3-1)/(p_l-1)-1=p_l^2+p_l >= 6.             (1)
```

The projective action is two-transitive: extend representatives of
each ordered pair of distinct lines to a basis, then adjust the image
of the third basis vector to make the resulting map have determinant
one. A commuting matrix for the permutation action is constant on its
two orbits on ordered pairs. Thus its commutant has dimension two.
Constants occur once, so their complement is a single nontrivial
irreducible representation.

For a non-scalar `g in SL_3(F_p)`, every fixed projective point is a
line in an eigenspace over `F_p`. No eigenspace has dimension three.
The maximum number of such lines occurs for dimensions two and one,
and is `p+2`. Consequently

```text
|Tr(sigma(g))|=|#{fixed projective points}-1|<=p+1,
|tr(sigma(g))|<=1/p.                               (2)
```

The reduction map

```text
Gamma -> product_(l=1)^n G_l                       (3)
```

is surjective. The Chinese remainder theorem gives an integer
elementary matrix with any specified parameter in one factor and
parameter zero in all the others. Elementary matrices generate each
special linear group over a field.

## 2. Tail tensors realize the exact nested commutants

Choose Hilbert spaces `V_l` for `sigma_l` and put

```text
V=V_1 tensor ... tensor V_n,       D=product_(l=1)^n r_l,
a_j=product_(l=1)^j r_l,          a_0=1,
rho_j=sigma_(j+1) tensor ... tensor sigma_n,
pi_n(g)=direct_sum_(j=0)^(n-1) I_(a_j) tensor rho_j(g).
                                                        (4)
```

Each summand in (4) acts on a copy of `V`, so `d_n=nD`. Product-group
irreducibility and (3) make every `rho_j` irreducible as a
representation of `Gamma`. They are pairwise inequivalent: for
`j<k`, the factor `G_(j+1)` acts nontrivially on `rho_j` and trivially
on `rho_k`. Complete reducibility therefore gives the actual
commutant, in these fixed tensor coordinates,

```text
A_n=pi_n(Gamma)'
   =direct_sum_(j=0)^(n-1)
       (B(V_1 tensor ... tensor V_j) tensor I_(V_(j+1) tensor ... tensor V_n))
   ~=direct_sum_(j=0)^(n-1) M_(a_j) tensor I_(D/a_j).
                                                        (5)
```

Every tail in (4) contains the last factor `sigma_n`. For fixed
`g!=1` in `Gamma`, `g` is not scalar over `Q`: an integer scalar of
determinant one in dimension three is the identity. At least one
off-diagonal entry or diagonal difference is consequently a nonzero
integer. Its reduction is nonzero outside a finite set of primes.
Using (2) and normalized character multiplicativity gives, eventually,

```text
|tr_(d_n)(pi_n(g))|
 <=(1/n) sum_(j=0)^(n-1) |tr(rho_j(g))|
 <=|tr(sigma_n(g))|<=1/p_n -> 0.                    (6)
```

Thus these exact representations have the canonical limiting
character of the same fixed group `Gamma`. This assertion concerns
`Gamma`; no joint canonical character involving the block shift
introduced next is asserted.

## 3. Exact forward and reverse expectation norms

Number the equal physical blocks by `0,...,n-1`. Let `U_n` send block
`j+1` to block `j`, and block `0` to block `n-1`, using the identity
map on their common tensor space `V`. Put

```text
B_n=U_n A_n U_n*,       E_n=E_(A_n),       F_n=E_(B_n).
```

On block `j<n-1`, the algebra `B_n` is
`M_(a_(j+1)) tensor I_(D/a_(j+1))`, which contains that block of
`A_n`. On the last block, `B_n` is scalar. Both expectations erase
off-diagonal physical blocks. Their restrictions to each diagonal
block are nested-algebra expectations, so `E_n,F_n` commute.

The difference `F_n E_n-E_n` is zero except on the last block,
where it is minus the projection onto the traceless part of that
block's `A_n`. This proves, including equality by a traceless unitary
on that block,

```text
||F_n E_n-E_n||_(infinity->2)=1/sqrt(n).             (7)
```

Each `r_l` is even. Choose a traceless self-adjoint unitary `Z_l`
on `V_l`. Define a unitary `X_n` whose block `j<n-1` is

```text
I_(V_1 tensor ... tensor V_j) tensor Z_(j+1)
                      tensor I_(V_(j+2) tensor ... tensor V_n),
```

and whose last block is the identity. Then `F_n X_n=X_n`, while
`E_n X_n` is zero on the first `n-1` blocks and is the identity on
the last. The reverse difference is an orthogonal projection on
each of those first blocks, so contractions give the matching upper
bound. Therefore

```text
||E_n F_n-F_n||_(infinity->2)
 =||E_n F_n(X_n)-F_n(X_n)||_2=sqrt(1-1/n).           (8)
```

## 4. A uniform gap for one fixed finite generator list

Use the symmetric twelve-element list

```text
S={I+E_ij,I-E_ij: 1<=i!=j<=3}.
```

Let `kappa_0>0` be a Kazhdan constant for this list, supplied by
[Kassabov, Kazhdan Constants for SL_n(Z), Theorem A](https://arxiv.org/abs/math/0311487v1).
Set

```text
T_n=(1/2)id+(1/(2|S|)) sum_(s in S) Ad(pi_n(s)),
gamma=min(1/2,kappa_0^2/(4|S|))>0.                  (9)
```

The fixed space of this exact adjoint representation is precisely
`A_n`. For `Y` perpendicular to `A_n`, the Kazhdan inequality gives

```text
< (I-T_n)Y,Y >
 =(1/(4|S|)) sum_(s in S) ||pi_n(s)Ypi_n(s)*-Y||_2^2
 >=gamma ||Y||_2^2.                                (10)
```

Laziness makes `T_n` positive on `L^2`, so

```text
spec(T_n) subset [0,1-gamma] union {1},
||T_n^k-E_n||_(2->2)<=(1-gamma)^k.                  (11)
```

In particular no negative endpoint of the spectrum interferes with
the rank-controlled powers. The maps `T_n^k` are self-adjoint,
bistochastic and UCP, with at most `13^k` Kraus operators. This
bound counts the identity and the twelve adjoint words at each step;
no assertion that all these Kraus operators are independent is needed.

The continuous heat maps of this fixed generator list are

```text
H_(n,t)=exp(-t(I-T_n)).
```

They are self-adjoint bistochastic UCP maps, by their Poisson
expansion. Equation (10) gives

```text
||H_(n,t)-E_n||_(2->2)<=exp(-gamma t),
||H_(n,2t)-H_(n,t)||_(infinity->2)<=exp(-gamma t).
                                                        (12)
```

For `0<eta<1`, put

```text
k(eta)=ceil(log(2/eta)/(-log(1-gamma))),
t(eta)=gamma^(-1) log(2/eta).
```

For every `n` and every `t>=t(eta)`, equations (11)--(12) give

```text
||H_(n,t)-T_n^(k(eta))||_(infinity->2)<=eta,
Kraus_rank(T_n^(k(eta)))<=13^(k(eta)).               (13)
```

Thus the same rank bound works at this fixed tolerance for all
dimensions and all sufficiently long heat times. The bound depends
on the tolerance; (13) does not give one rank bound with error tending
to zero. Nor does it bound the exact Kraus rank of the heat itself.

If `J_n=Ad(U_n)` and `K_(n,t)=J_n H_(n,t) J_n^(-1)`, the
expectation comparisons and three-term telescoping give

```text
||K_(n,t) H_(n,t)-H_(n,t)||_(infinity->2)
 <=1/sqrt(n)+3exp(-gamma t),

||H_(n,t) K_(n,t)(X_n)-K_(n,t)(X_n)||_2
 >=sqrt(1-1/n)-3exp(-gamma t).                      (14)
```

Every choice `t_n->infinity` therefore realizes the one-sided
asymmetry using actual fixed-generator heat maps.

## 5. Central weights, large corners, and an explicit height

Let `p_j` denote the central projection onto physical block `j`.
Its physical trace is `t_j=1/n`, and its simple degree in `A_n`
is `a_j`. The ratios relevant to physical versus normalized regular
central trace, up to a common factor, are

```text
w_j=t_j/a_j^2=1/(n a_j^2),
h_j=log(w_j)=-log(n)-2 sum_(l=1)^j log(r_l).        (15)
```

They are strictly decreasing. Their distortion is

```text
R_(A_n)=max_j(w_j)/min_j(w_j)=a_(n-1)^2
       >=6^(2(n-1)) -> infinity.                  (16)
```

This divergence cannot be confined to central blocks of vanishing
physical trace. If a nonzero central corner retains `m` levels, the
largest and smallest retained indices differ by at least `m-1`.
Since every `r_l>=6`, its distortion is at least `6^(2(m-1))`.
Thus, for any fixed `R>=1`, every central projection `p` satisfying
`R_(p A_n)<=R` obeys

```text
tr(p)<= [1+log(R)/(2log(6))]/n -> 0.                (17)
```

Corner trace normalization multiplies all its weights by one common
factor and does not change this ratio.

Define the self-adjoint central element

```text
z_n=sum_(j=0)^(n-1) [(n-1-2j)/(2(n-1))] p_j.       (18)
```

It is an increasing function of the strictly decreasing log weights
`h_j`: both its coefficients and `h_j` decrease with `j`. Direct
summation gives

```text
tr(z_n)=0,       ||z_n||_op=1/2,
||z_n||_2^2=(n+1)/(12(n-1)) >=1/12.                 (19)
```

The `n-1` ordinary adjacent differences under the cyclic block shift
have absolute value `1/(n-1)`, and the wraparound difference has
absolute value one. Hence

```text
||[U_n,z_n]||_2^2
 =(1/n)[(n-1)/(n-1)^2+1]=1/(n-1) -> 0.             (20)
```

These central heights commute exactly with `pi_n(Gamma)` and are
fixed exactly by all the heat maps. They have macroscopic variance
and asymptotically commute with the same `U_n` producing (7)--(8).

## 6. What this rules out and what remains outside its scope

Equations (6), (12)--(14), and (17)--(20) coexist in exact finite
representations of the fixed Kazhdan group `SL_3(Z)`. Therefore
these analytic and central-weight properties, even taken together,
cannot imply that the Kraus rank needed at one fixed positive
approximation tolerance tends to infinity with the staircase depth.
They also do not turn the fixed-rank compactness theorem into a
modulus along growing rank: the rank in (13) increases as `eta->0`.

This is stronger than realizing the staircase with an unrelated
finite averaging group at each depth. It includes a canonical trace
for one fixed source and a uniform gap for one fixed generator list.
The full native Leavitt group requires additional authenticated
relations coupling its subgroup, compressor, complementary subgroup,
and generating roots. No such joint realization, joint canonical
trace, or fixed native word for `U_n` is supplied here.

In particular this is a counterexample to forcing an unbounded rank
requirement at fixed tolerance from the listed analytic data, not to conditional-expectation
rounding. Rounding succeeds uniformly by (12), and neither
hyperlinearity nor nonhyperlinearity of the native group follows.

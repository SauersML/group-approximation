# Canonical Kazhdan models with unbounded commutant trace distortion

2026-09-08. Written exact representation-theoretic countermodel.
No computation, build, or new Lean verification is asserted.

This constructs exact representations of the fixed group `Gamma=SL_3(Z)`.
Their normalized characters converge to the regular character,
and a fixed Kazhdan averaging operator converges uniformly to
their commutant expectations. Nevertheless, the ambient versus
regular trace distortion of those commutants tends to infinity
on two sectors of physical trace `1/2`.

The conclusion concerns these actual commutant algebras. It does
not exclude other bounded-distortion algebras approximating the
same expectations, and is not a model of the full Leavitt group.

## 1. An explicit growing irreducible degree

For a prime `q`, let `K_q=SL_3(F_q)`. It acts on the projective
points of `F_q^3`. The number of points is

```text
v_q=(q^3-1)/(q-1)=q^2+q+1.
```

The action is two-transitive. Given two ordered pairs of distinct
projective points, choose independent representatives for each
pair and extend each pair to a basis. The linear map sending the
first basis to the second can be made determinant one by rescaling
the image of the third basis vector, without changing either of
the prescribed projective images.

The complex permutation representation therefore splits as the
trivial representation plus one nontrivial irreducible `rho_q`,
of degree

```text
r_q=v_q-1=q^2+q.
```

For completeness, a linear map commuting with a permutation
action has matrix entries constant on its orbits on ordered
pairs of points. Two-transitivity gives exactly two such orbits,
so the commutant has complex dimension two. Constants supply one
irreducible summand of multiplicity one. Complete reducibility
for finite unitary representations and the formula that commutant
dimension is the sum of squared multiplicities force its
orthogonal complement to be a single irreducible summand.

## 2. Exact canonical representations of one fixed group

Choose distinct primes `p_q` and `q`, with both tending to infinity,
and put `G_q=SL_3(F_(p_q))`. Reduction gives a surjection

```text
Gamma -> G_q times K_q.
```

Indeed, the Chinese remainder theorem supplies elementary
matrices with independently prescribed parameters modulo the
two primes. Elementary matrices generate both special linear
groups over fields.

Define the exact unitary representation

```text
pi_q(g)=lambda_(G_q)(g mod p_q)
          tensor (1_(K_q)^(direct-sum r_q) direct-sum rho_q)(g mod q)
```

in dimension `n_q=2 r_q |G_q|`. If `g!=1` is a fixed integer
matrix, its reduction modulo `p_q` is nonidentity for all
sufficiently large `q`: some nonzero entry of `g-I` is divisible
by only finitely many primes. The regular factor then has trace
zero. Consequently

```text
tr_(n_q) pi_q(g) -> delta_(g,1).
```

In particular the limiting generated tracial algebra is the
canonical `L(Gamma)`, which is a factor. One elementary check
of the latter statement is as follows. A finite conjugacy class
would give a finite-index centralizer. Such a centralizer
contains a nonzero power of every integer elementary
transvection. Commuting with those powers forces the matrix
to commute with all off-diagonal matrix units over `Q`, hence
to be scalar. The only scalar in `SL_3(Z)` is the identity.

## 3. Trace distortion on two macroscopic sectors

Let `d_alpha` run over the irreducible degrees of `G_q`, and put
`D_q=pi_q(Gamma)'`. Surjectivity onto the product and the regular
multiplicities of `G_q` give the represented algebra

```text
D_q ~= direct_sum_alpha (M_(r_q d_alpha) tensor I_(d_alpha))
       direct_sum
       direct_sum_alpha (M_(d_alpha) tensor I_(r_q d_alpha)).
```

Each indicated block has physical trace weight
`d_alpha^2/(2|G_q|)`. Each family therefore has total physical
trace `1/2`.

For a represented block `M_a tensor I_b`, the ratio of its
physical trace weight to `a^2` is proportional to `b/a`.
The distortion between the ambient and intrinsic regular
central weights is consequently

```text
R_(D_q)=max(b/a)/min(b/a)=r_q^2 -> infinity.           (1)
```

More explicitly, the two intrinsic regular weights are

```text
nu_(alpha,0)=r_q^2 d_alpha^2/((r_q^2+1)|G_q|),
nu_(alpha,1)=d_alpha^2/((r_q^2+1)|G_q|).
```

Their ratios to the corresponding physical weights are
`2r_q^2/(r_q^2+1)` and `2/(r_q^2+1)`. The second ratio tends
to zero on a family of physical trace exactly `1/2`.

This distortion also survives deleting a vanishing physical
trace of central blocks. In fact any central projection
`e_q in Z(D_q)` of physical trace greater than `1/2` retains
at least one block from each family. The two surviving values
of `b/a` are still `1/r_q` and `r_q`, and normalizing the
trace on the retained corner does not change their ratio.
Thus `R_(e_q D_q)=r_q^2` on its support space. Removing
`o(1)` trace centrally cannot remove (1).

## 4. Uniform Kazhdan heat convergence still holds

Take the symmetric generating set
`S={I+E_ij,I-E_ij:1<=i!=j<=3}`. A positive Kazhdan constant
`kappa_0` for this set is supplied by Martin Kassabov,
[*Kazhdan Constants for SL_n(Z)*, Theorem A](https://arxiv.org/abs/math/0311487v1).
Only positivity of that constant is used. Form the lazy adjoint
averages

```text
T_q=(1/2)id+(1/(2|S|))sum_(s in S) Ad pi_q(s).
```

The fixed space is exactly `D_q`. On its orthogonal complement,
the Kazhdan inequality and the exact adjoint representation give

```text
<(I-T_q)X,X>
 =(1/(4|S|))sum_s ||pi_q(s)Xpi_q(s)^*-X||_2^2
 >=kappa_0^2 ||X||_2^2/(4|S|).
```

As `T_q` is a positive self-adjoint contraction, one can take
`gamma=min(1/2,kappa_0^2/(4|S|))>0`, independently of `q`.
Its spectrum is contained in `[0,1-gamma] union {1}`, and
the invariant projection is the trace-preserving expectation
onto `D_q`. Hence

```text
||T_q^k-E_(D_q)||_(2->2)<=(1-gamma)^k.
```

Choosing any `k_q->infinity` gives uniform approximation of
these positive bistochastic maps by their actual conditional
expectations, including in the weaker `infinity->2` norm.
The maps can therefore be rounded successfully while the
distortion of their commutants diverges on macroscopic sectors.

This refutes a general inference from exact canonical Kazhdan
models to bounded distortion of their own commutants. It does
not refute the existential assertion that some different
bounded-distortion subalgebras approximate these maps, nor any
assertion using the full native Leavitt compressor relations.
No nonhyperlinearity conclusion follows from this countermodel.

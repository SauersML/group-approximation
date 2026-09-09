# Central convolution Markov channels round to normal-coset expectations

Date: 2026-09-08. Written proof; no computation is used. The
result concerns a restricted class of stochastic averaging
channels and does not settle general heat rounding.

## 1. The theorem

Let `G` be a finite group of order `n`, with normalized counting
measure. Let `mu:G->[0,1]` have total mass one and satisfy

```text
mu(g^-1)=mu(g),       mu(hgh^-1)=mu(g).
```

Thus `mu` is symmetric and central. Put

```text
(Kf)(x)=sum_g mu(g) f(g^-1 x),
||f||_2^2=(1/n)sum_x |f(x)|^2,
delta=||K^2-K||_(infinity->2).
```

The matrix of `K` is real, symmetric, nonnegative, and doubly
stochastic. If

```text
delta < sqrt(pi)/20,
```

then there is a normal subgroup `N` of `G` such that

```text
(E_N f)(x)=(1/|N|)sum_(h in N) f(hx),
||K-E_N||_(infinity->2) <= ||K-E_N||_(2->2)
                       <= (4/sqrt(pi))*delta.         (1)
```

The result includes zero defect and places no bound on `n`,
the number of irreducible representations, or their degrees.
For abelian `G`, the bound improves to `2delta`, with threshold
`delta<1/10`, and both norms in (1) are equal.

## 2. Transitive symmetry removes the probability weight

We use the complex commutative little-Grothendieck theorem:
for a bounded linear map `T:C(X)->H`, with `X` finite and `H`
a complex Hilbert space, there is a probability measure `nu`
on `X` such that

```text
||Tf||_H <= (2/sqrt(pi))*||T||_(infinity->H)
            * (sum_x nu(x)|f(x)|^2)^(1/2).            (2)
```

This is Theorem A in Kalenda--Peralta--Pfitzner,
[On optimality of constants in the Little Grothendieck Theorem](https://arxiv.org/html/2002.12273),
arXiv:2002.12273v3. The theorem states the complex constant
`2/sqrt(pi)` explicitly. This is the only imported analytic
estimate in the proof.

Suppose `T:C(G)->L^2(G)` commutes with every right translation
`R_h f(x)=f(xh)`. Apply the square of (2) to `R_h f` and
average over `h`. Equivariance and the unitary action on the
target make the left side equal to `||Tf||_2^2`, while

```text
(1/n)sum_h sum_x nu(x)|f(xh)|^2 = ||f||_2^2.
```

Consequently

```text
||T||_(2->2) <= (2/sqrt(pi))*||T||_(infinity->2).       (3)
```

Left convolution commutes with right translations, so (3)
applies to `T=K^2-K`. Set

```text
epsilon=(2/sqrt(pi))*delta < 1/10.
```

Then `||K^2-K||_(2->2)<=epsilon`. The averaging argument uses
the exact transitive symmetry, rather than a bound on individual
eigenvectors or any dimension-dependent net.

## 3. The high irreducibles are closed under tensor products

For an irreducible unitary representation `pi` of `G`, centrality
and symmetry give

```text
sum_g mu(g) pi(g)=lambda_pi I,       lambda_pi in [-1,1].
```

The matrix coefficients of these irreducibles decompose `C(G)`
orthogonally, and `K` acts on the whole coefficient space of
`pi` by `lambda_pi`. Thus

```text
|lambda_pi^2-lambda_pi| <= epsilon.
```

The scalar estimate

```text
|z-1_[1/2,1](z)| <= 2|z^2-z|       for z in [-1,1]
```

shows that every irreducible is either low, with
`|lambda_pi|<=2epsilon`, or high, with
`lambda_pi>=1-2epsilon`. Define the high class by
`lambda_pi>=1/2`. It contains the trivial representation and
is closed under duals, because the `lambda_pi` are real.

Let `pi,rho` be high. For any vector `zeta` in their tensor
product use

```text
pi(g) tensor rho(g)-I
 = (pi(g)-I) tensor rho(g)+I tensor (rho(g)-I).
```

The squared triangle inequality and averaging give

```text
sum_g mu(g)||((pi(g) tensor rho(g))-I)zeta||^2
 <= 4[(1-lambda_pi)+(1-lambda_rho)]||zeta||^2
 <= 16epsilon ||zeta||^2.                            (4)
```

Here the first squared term before the factor two averages
to `2(1-lambda_pi)||zeta||^2`, because the second tensor
factor is unitary; the other term has the analogous value.

The averaged tensor operator is self-adjoint, and its
Dirichlet form is one half the left side of (4). Therefore

```text
sum_g mu(g)(pi(g) tensor rho(g)) >= (1-8epsilon)I.
```

On every irreducible constituent `sigma`, this operator is
the scalar `lambda_sigma`. It follows that

```text
lambda_sigma >= 1-8epsilon > 2epsilon.
```

The strict inequality uses `epsilon<1/10`. Such a constituent
cannot be low, so it is high. This proves closure under all
irreducible constituents of tensor products. Centrality is
essential to this exact conclusion: the averaging operator is
a scalar on every constituent.

## 4. The coefficient algebra is a normal quotient

Let `A` be the linear span in `C(G)` of all matrix coefficients
of high irreducibles. It contains constants. Products of two
matrix coefficients are coefficients of the tensor product,
so section 3 proves closure under multiplication. Complex
conjugation passes to the dual representation, proving
closure under adjoints. Thus `A` is a unital `*`-subalgebra
of `C(G)`, invariant under both left and right translations.

For completeness, define `x~y` when `f(x)=f(y)` for every
`f in A`. A finite unital function algebra equals the full
algebra of functions constant on these equivalence classes:
it separates distinct classes, and polynomial interpolation
in finitely many separating functions produces each class
indicator.

Let `N` be the class of the identity. Translation invariance
makes `~` invariant under left and right translations. If
`a,b in N`, left translation by `a` gives `a~ab`, so
`e~ab`. Left translation by `a^-1` gives `a^-1~e`.
Thus `N` is a subgroup. Applying left translation by `h` and
right translation by `h^-1` shows it is normal. Finally,

```text
x~y  <=>  e~x^-1y  <=>  x^-1y in N.
```

Hence `A` is precisely the algebra of functions constant on
`N`-cosets. Its orthogonal projection is `E_N`.

On the other hand, by the orthogonal matrix-coefficient
decomposition, the projection onto `A` is exactly the high
spectral projection of `K`. The scalar estimate in section 3
therefore gives

```text
||K-E_N||_(2->2) <= 2epsilon = (4/sqrt(pi))*delta.
```

Since `||f||_2<=||f||_infinity` for normalized counting
measure, this also bounds the mixed norm and proves (1).

## 5. Abelian kernels and the matrix-channel realization

If `G` is abelian, every irreducible character has modulus
one and normalized `L^2` norm one. Characters therefore
attain the operator norm of every Fourier multiplier, both
as a `2->2` map and as an `infinity->2` map. In particular,

```text
||K^2-K||_(2->2)=delta.
```

The preceding proof applies directly with `epsilon=delta`,
giving threshold `delta<1/10` and distance at most `2delta`.
The high characters form a subgroup of the dual, and `N` is
its annihilator. No optimality of the constant two is claimed.

Identify `C(G)` with the diagonal algebra in `M_n(C)`. If
`d(X)` is the vector of diagonal entries, define

```text
P_K(X)=diag(K(d(X))).
```

Nonnegativity of the stochastic matrix gives complete
positivity, for example by the Kraus operators
`sqrt(K_ij) E_ji` in the convention `sum v*Xv`.
Row and column sums give unitality and trace preservation;
symmetry makes the channel self-adjoint on normalized `L^2`.

Taking diagonals is a contraction from matrix operator norm
to function supremum norm, and every bounded function occurs
as the diagonal of a diagonal matrix with the same norm.
Consequently the mixed norm of the matrix-channel defect is
exactly `delta`. The same argument gives

```text
||P_K-E_(B_N)||_(infinity->2)=||K-E_N||_(infinity->2),
B_N={diag(f): f is constant on N-cosets}.
```

Indeed, `E_(B_N)` kills off-diagonal entries and averages the
diagonal entries within each coset. As a represented matrix
algebra,

```text
B_N = direct_sum_(G/N) C I_(|N|).
```

Its representation multiplicity is `|N|`, which can be
arbitrarily large. When `|N|>1`, this algebra does not contain
an ambient maximal abelian subalgebra. Thus the result covers
rounding targets beyond the pointwise-fixed-MASA and Schur
settings, while preserving the original matrix dimension.

## 6. What the theorem does not settle

For a general symmetric stochastic kernel, small mixed-norm
defect need not place every eigenvalue near zero or one.
For example, for `n>=2`, take

```text
K_n = [[3/4,1/4],[1/4,3/4]] direct_sum I_(n-2).
```

It has an eigenvalue `1/2`, but

```text
||K_n^2-K_n||_(infinity->2)=(1/4)sqrt(2/n) -> 0.
```

This does not refute rounding: its distance from `I_n`, the
singleton-partition expectation on functions, is exactly
`(1/2)sqrt(2/n)`, twice the defect. It diagnoses why the
transitive norm upgrade cannot simply be omitted.

For noncentral convolution, transitivity still supplies (3),
but Fourier blocks need not be scalar. The tensor calculation
then controls nearly invariant vectors; it does not supply
the exact constituent closure used in section 4. No extraction
of a partition for arbitrary symmetric kernels, and no
conclusion about native full-kernel feasibility or
nonhyperlinearity, is claimed.

Repository duplicates and the primary source in section 2
were checked on 2026-09-08. The proof is recorded for its
precise scope and constants, with no claim of priority.

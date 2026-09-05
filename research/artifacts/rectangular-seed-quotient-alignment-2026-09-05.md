# Rectangular Schreier seeds must match the quotient content

This gives a quantitative selection constraint for the rectangular
certificate `(MSC7)` in
`moving-subgroup-schreier-correction-has-no-index-loss`. It also gives
opposite, sharp constructions for aligned and coprime congruence levels.
It does not construct subgroup holonomy from QRC5 curvature data.

## 1. A robust common-constituent capacity bound

Let `G` have Kazhdan pair `(S,kappa)` in the convention of `(MSC7)`.
Let `rho:G->U(d)` be genuine, let `N<=G` have finite index, and let
`pi:N->U(k)` be genuine. Write `Pi=Ind_N^G pi`. Decompose these finite
dimensional unitary representations into irreducibles and put

```text
R=sum_sigma dim(sigma) min(m_rho(sigma),m_Pi(sigma)).       (QA1)
```

Thus `R` is their largest common subrepresentation dimension. For arbitrary
rectangular maps `A_t:C^d->C^k`, use the unaltered induced ambient space
and define

```text
J_0 x=sum_t delta_t tensor A_t x,
H=J_0^*J_0,
zeta=||H-I||_(1,d),
beta=max_s ||Pi(s)J_0-J_0 rho(s)||_HS/sqrt(d).
```

Then

```text
R/d >= 1-zeta-beta^2/kappa^2.                            (QA2)
```

There is no subgroup-index factor. Unlike the elementary capacity
`rank(H)<=mk`, this bounds the amount of matching representation content.

Here is a complete proof. On `Hom(C^d,H_Pi)`, the action

```text
T -> Pi(g) T rho(g)^*
```

is a genuine unitary representation for the unnormalized HS inner
product. Let `T_0` be the orthogonal projection of `J_0` onto its invariant
vectors, namely the genuine intertwiners. Property `(T)` gives

```text
||J_0-T_0||_HS^2 <= beta^2 d/kappa^2.
```

Schur's lemma implies `rank(T_0)<=R`: on each common irreducible its rank
is the irreducible dimension times the rank of a map between multiplicity
spaces. Let `E` project onto `ker(T_0)`. Its rank is at least `d-R`, and

```text
||J_0-T_0||_HS^2
 >= ||(J_0-T_0)E||_HS^2
 = Tr(EH)
 >= rank(E)-||H-I||_1
 >= d-R-d zeta.
```

Combining the inequalities proves `(QA2)`.

The zero-error converse is exact: `beta=zeta=0` is possible if and only
if `R=d`. Necessity follows from `(QA2)`. For sufficiency, choose an
equivariant isometry `J:C^d->H_Pi` and take its coset coordinate maps as
the `A_t`. Thus the seed-selection condition at an exact input is

```text
m_rho(sigma)
 <= dim Hom_N(Res_N sigma,pi)  for every sigma.           (QA3)
```

Indeed Frobenius reciprocity identifies the right side with
`m_Pi(sigma)`. This differs from the existing universal relative-ucp host
result: no exact prescribed-core corner is assumed here, and `(QA2)`
quantifies how much representation content every approximate frame needs.

There is also a robust version for arbitrary input unitaries `U_s` on
the same space. Put

```text
eta=max_s ||U_s-rho(s)||_(2,d),
beta_U=max_s ||Pi(s)J_0-J_0 U_s||_HS/sqrt(d).
```

Because `||U_s-rho(s)||_op<=2`, trace duality gives

```text
||J_0(U_s-rho(s))||_HS^2
 <= ||U_s-rho(s)||_HS^2+4||H-I||_1
 <= d(eta^2+4zeta).
```

Consequently

```text
R/d >= 1-zeta-(beta_U+sqrt(eta^2+4zeta))^2/kappa^2.      (QA4)
```

This estimate does not require an operator norm bound on `J_0`, nor any
lower bound on the singular values of its Gram matrix. It concerns the
original induced representation before the auxiliary trivial padding
allowed in the proof of `(MSC7)`.

## 2. Coprime congruence levels cannot provide small seeds for regular inputs

Take `G=SL_5(Z)`, a prime `p`, and

```text
Q=SL_5(F_p),
rho=lambda_Q composed with reduction modulo p,
d=|Q|,
N=Gamma(q)=ker(SL_5(Z)->SL_5(Z/qZ)),
gcd(p,q)=1.
```

The restriction `N->Q` is surjective. Explicitly, for every field scalar
`a`, choose an integer `b` with `b=0 mod q` and `b=a mod p`. The elementary
matrix `I+b E_ij` belongs to `Gamma(q)` and reduces to `I+a E_ij`.
Elementary matrices generate `SL_5(F_p)` by row elimination. This proves
the needed surjectivity directly, for any positive integer `q` coprime
to `p`.

The irreducible representations of `Q`, pulled back to `N`, therefore
remain irreducible and pairwise inequivalent. If `a_sigma` is the
multiplicity of such a restricted irreducible in `pi`, then

```text
m_Pi(sigma)=a_sigma,
sum_(sigma in Irr(Q)) dim(sigma) a_sigma <= k.
```

The regular representation has `m_rho(sigma)=dim(sigma)`. Hence

```text
R=sum_(sigma in Irr(Q)) dim(sigma) min(dim(sigma),a_sigma)
 <= k.
```

Applying `(QA2)` yields, for every seed and every rectangular frame,

```text
k/d >= 1-zeta-beta^2/kappa^2.                           (QA5)
```

In particular, `k=o(d)` is incompatible with `beta,zeta->0`, regardless
of the index `[G:Gamma(q)]`. Increasing a coprime congruence level does
not fix this. For input tuples within `eta->0` of these regular tuples,
the same conclusion follows from `(QA4)`.

This obstruction is not concentrated in the trivial sector: that sector
has dimension one in `lambda_Q`. Replacing `lambda_Q` by its orthogonal
complement to the constant vector gives precisely the same proof, with
input dimension `|Q|-1` and again `R<=k`.

As `p->infinity`, the full regular representations are canonical exact finite-quotient
approximations of `SL_5(Z)`. Every fixed nonidentity integer matrix stays
nonidentity modulo all sufficiently large primes. Left translation by a
nonidentity element on `Q` has no fixed points, so its normalized regular
trace is zero and its squared normalized HS distance from the identity
is two. For the mean-zero variant, the corresponding values are
`-1/(|Q|-1)` and `2|Q|/(|Q|-1)`, tending to zero and two.
No finite-prime computation is involved.

## 3. At an aligned congruence level one dimension suffices exactly

For the same regular input, instead take

```text
N=Gamma(p),       pi=1_N,       k=1.
```

The induced representation is exactly the permutation representation
on `G/N=Q`, namely `lambda_Q`. Index the coordinates of `C^d` by the
coset representatives and let

```text
A_t x=x_t.
```

Then `sum_t A_t^* A_t=I`. If `s t=t' n(s,t)`, triviality of `pi` and
the left-regular convention give

```text
pi(n(s,t))A_t=A_t=A_(t')rho(s).
```

Thus `zeta=beta=0`; this is an explicit one-dimensional exact seed and
an exact Parseval frame. The same construction restricted to the
mean-zero invariant subspace gives a one-dimensional seed there too.

The two cases expose a concrete selection requirement: a small seed
must be taken at a subgroup whose restrictions match the representation
content of the matrix tuple. Total induced dimension, tiny curvature
rank, and large subgroup index alone do not enforce that match. The
aligned construction does not recover a suitable quotient or holonomy
from arbitrary QRC5 output; that remains the missing arithmetic step.

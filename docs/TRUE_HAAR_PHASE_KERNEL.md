# TRUE lane: the Haar law of a common-Cartan phase kernel

Date: 2026-08-10

This note continues `docs/TRUE_CARTAN_MONOMIAL_GATE.md`.  A common Cartan
does more than produce an abelian kernel: the phases of that kernel are
forced to be Haar-distributed characters, equivariantly for the sofic
quotient.  This identifies the exact finite-window object which still has to
be rounded.  It does **not** assert that the rounding is automatic.

## 1. Monomial ultraproduct setup

Let `Gamma` be countable and suppose that a faithful regular-trace embedding

`rho:Gamma -> product_omega Mon(d_n)`                    `(HPK1)`

has been obtained, for example from the common-Cartan hypotheses and the
Birkhoff estimate `(CTM1)--(CTM11)`.  Here

`Mon(d_n)=T^(d_n) semidirect Sym(d_n)`.

Let `A` be the tracial ultraproduct of the diagonal algebras and let

`theta:Gamma -> product_omega Sym(d_n)`                 `(HPK2)`

be the permutation-part homomorphism.  Put `K=ker(theta)` and
`Q=theta(Gamma)`.  As in Theorem 3 of the Cartan note, `Q` is sofic and `K`
is abelian.  We identify `A` with `L-infinity(X,mu)` for its Loeb probability
space.  The permutation ultraproduct acts on `X` by measure-preserving
transformations.

For `k in K`, the permutation part tends to the identity in Hamming metric.
Deleting it changes the corresponding monomial matrices by `o(1)` in
normalized Hilbert--Schmidt norm.  Consequently

`rho(k)=a_k in U(A)`,                                  `(HPK3)`

and `k |-> a_k` is a homomorphism from `K` to
`L-infinity(X,T)`.

## 2. The phase field is Haar on the dual

**Theorem 1 (Haar-dual phase law).**  In the setup above there is a measurable
map

`chi:X -> dual(K)`                                     `(HPK4)`

such that, after discarding one null set,

`a_k(x)=chi_x(k)` for every `k in K`.                  `(HPK5)`

Its pushforward measure is Haar probability on `dual(K)`.  Moreover `(HPK4)`
is equivariant for the conjugation action of `Q`: if `g in Gamma`,
`q=theta(g)`, and `k in K`, then

`chi_(q x)(g k g^(-1))=chi_x(k)`                       `(HPK6)`

for almost every `x`.  The action on the right is independent of the chosen
lift `g` of `q`.

**Proof.**  Since `K` is countable, the homomorphism identities

`a_(kl)=a_k a_l`, `a_1=1`                              `(HPK7)`

hold simultaneously off one null set.  Thus `(HPK5)` defines a character of
`K` at almost every point, giving `(HPK4)`.

Let `nu=chi_*mu`.  The embedding has the regular trace, so

`integral_(dual(K)) eta(k) dnu(eta)`
` =integral_X a_k dmu=tau(rho(k))=1_(k=1)`.            `(HPK8)`

The right side is the Fourier transform of Haar probability on `dual(K)`.
Finite linear combinations of the characters `eta |-> eta(k)` are uniformly
dense in `C(dual(K))`; hence probability measures are determined by these
coefficients.  Therefore `nu` is Haar.

Conjugation by `rho(g)` preserves `A`.  Its diagonal phase cancels in this
conjugation, so its action on `A` is exactly the Loeb action of the
permutation part `q`.  Hence

`rho(g) a_k rho(g)^(-1)=a_(gkg^(-1))`.                 `(HPK9)`

Writing `(HPK9)` pointwise gives `(HPK6)`.  If two lifts differ by an element
of `K`, their conjugation actions on `K` agree because `K` is abelian; this
also proves lift independence.  End proof.

Thus a common-Cartan counterexample cannot use an arbitrary collection of
canceling phases.  It must carry an equivariant copy of the full Haar dual
of its phase kernel.

## 3. The finite-window shadow

Choose diagonal representatives `a_(n,k):[d_n]->T` for the elements `(HPK3)`
and permutation representatives `sigma_(n,g)`.  The theorem has the following
entirely finitary shadow.  For every fixed `k,l in K` and `g in Gamma`,

`d_n^(-1) sum_j |a_(n,kl)(j)-a_(n,k)(j)a_(n,l)(j)|^2 ->0`, `(HPK10)`

`d_n^(-1) sum_j a_(n,k)(j) -> 1_(k=1)`,                `(HPK11)`

and, with the harmless inverse determined by the permutation convention,

`d_n^(-1) sum_j |a_(n,gkg^(-1))(j)`
`                 -a_(n,k)(sigma_(n,g)^(-1)j)|^2 ->0`. `(HPK12)`

Equations `(HPK10)--(HPK12)` say that the coordinates are asymptotic
character labels, Haar-generic on every finite Fourier window, and
asymptotically transported by the quotient chart.

The original monomial representatives also supply phase functions
`c_(n,g):[d_n]->T` for every `g in Gamma`.  With the convention used below,
their multiplication defects say

`d_n^(-1) sum_j |c_(n,h)(j)c_(n,g)(sigma_(n,h)j)`
`                    -c_(n,gh)(j)|^2 ->0`.             `(HPK12a)`

The restriction of this phase cocycle to the asymptotically trivial
permutation kernel is the character field `(HPK10)--(HPK12)`.  Thus the
finite completion problem concerns the whole cocycle `(HPK12a)`, with the
Haar kernel law retained.

The word **asymptotic** is load-bearing.  The finite coordinate labels need
not themselves be characters, and `(HPK10)` is an `L^2` equality rather than
equality outside a small set.  Pointwise circle rounding does not change one
notion into the other; `docs/PHASES.md`, Sections 6a--6d, proves the precise
obstruction.  The cocycle-stability criterion `(CS1)--(CS8)` is one sufficient
way to cross this gap, not a consequence of `(HPK10)--(HPK12)`.

## 4. Exact finite-window Fourier-completion gate

Here is the exact output that would suffice.  It is useful because it
separates the missing rounding statement from the already solved Cartan and
trace estimates.

**Theorem 2 (finite phase completion implies soficity).**  Suppose that for
arbitrarily accurate finite windows there are finite sets `Y_n`, maps

`sigma_n:Gamma -> Sym(Y_n)`,
`z_(n,g):Y_n -> mu_(m_n)`                              `(HPK13)`

with possibly growing `m_n`, such that for every fixed `g,h`:

1. `sigma_(n,g)sigma_(n,h)=sigma_(n,gh)` off `o(|Y_n|)` points;
2. with the convention
   `M_(n,g)e_y=z_(n,g)(y)e_(sigma_(n,g)y)`,

   `z_(n,h)(y) z_(n,g)(sigma_(n,h)y)=z_(n,gh)(y)`      `(HPK14)`

   off `o(|Y_n|)` points; and
3. the monomial traces satisfy

   `|Y_n|^(-1) sum_(y in Fix(sigma_(n,g))) z_(n,g)(y)
      ->1_(g=1)`.                                     `(HPK15)`

Then `Gamma` is sofic.

**Proof.**  Let the monomial datum act on

`Omega_n=Y_n times mu_(m_n)`

by

`Pi_(n,g)(y,u)=(sigma_(n,g)y,z_(n,g)(y)u)`.            `(HPK16)`

The two failures in `(HPK13)--(HPK14)` are exactly the two ways in which
`Pi_(n,g)Pi_(n,h)` can differ from `Pi_(n,gh)`, so multiplication holds off
`o(|Omega_n|)` points.

Let `r_(n,g)` be the density of `y` for which `sigma_(n,g)y=y` and
`z_(n,g)(y)=1`.  These and only these base points give fixed points in every
fiber of `(HPK16)`.  If `t_(n,g)` denotes the trace in `(HPK15)`, then

`r_(n,g) <= |t_(n,g)|+(1-r_(n,g))`,

because all remaining diagonal summands have total absolute mass at most
`1-r_(n,g)`.  Hence

`r_(n,g) <= (1+|t_(n,g)|)/2`.                          `(HPK17)`

For `g!=1`, `(HPK15)` makes the right side tend to `1/2`.  Thus `(HPK16)`
moves at least `1/2-o(1)` of its points.  Taking a fixed diagonal product
power makes its fixed-point density at most `(1/2+o(1))^L`, while the
multiplication error grows by at most the factor `L`.  First choose `L` and
then a sufficiently accurate window.  This gives the standard asymptotically
free sofic approximations.  End proof.

Theorem 2 does not assume a uniform bound on `m_n`; exact equality off a
small set removes the shrinking root-spacing problem.  The unresolved step
is precisely

`L^2 phase cocycle with Haar kernel law (HPK10)--(HPK12a)`
`  ==> combinatorial finite-phase chart (HPK13)--(HPK15)`. `(HPK18)`

This is the phase-kernel form of the normal-IRS rounding problem.  Manzoor's
normal-Dirac formulation shows why an unconditional proof of `(HPK18)` would
settle hyperlinear versus sofic rather than follow from a generic IRS density
statement.

## 5. A positive split finite-rank case

There is one group-theoretic regime in which the phase kernel can already be
removed without `(HPK18)`.

**Theorem 3 (split finite-rank abelian kernel).**  If

`Gamma=K semidirect_alpha Q`,                         `(HPK19)`

where `K` is finitely generated abelian and `Q` is sofic, then `Gamma` is
sofic.

**Proof.**  Let `Hol(K)=K semidirect Aut(K)`.  The map

`(k,q) |-> ((k,alpha(q)),q)`
`Gamma -> Hol(K) times Q`                              `(HPK20)`

is an injective homomorphism.

The holomorph of a finitely generated abelian group is residually finite.
Indeed, writing `K=Z^r directSum T` with `T` finite, `Hol(K)` has a
finite-index subgroup isomorphic to a subgroup of the integral affine group
`Z^r semidirect GL_r(Z)`, which embeds in `GL_(r+1)(Z)`.  Integral linear
groups are residually finite directly: reduce modulo a prime which does not
divide a chosen nonzero entry of `A-1`.  Residual finiteness passes from a
finite-index subgroup to the whole group by taking the finite-index normal
core and intersecting the finitely many conjugates of a separating subgroup.
Thus `Hol(K)` is residually finite and hence sofic.  Products and subgroups of
sofic groups are sofic, so `(HPK20)` proves the claim.  End proof.

This theorem also applies whenever `Hol(K)` is known to be sofic, without a
finite-generation assumption.  It does not apply to a nonsplit extension:
the unrestricted wreath embedding needed for an arbitrary extension has the
same dangerous extension orientation.

## 6. Kun--Thom calibration

The split hypothesis alone is not enough.  The explicit quotient
`(AB1)--(AB3)` in `docs/NOTEPAD.md` is

`P=reduced Z[G/Gamma] semidirect G`,                  `(HPK21)`

where `G` is residually finite but `P` is nonsofic.  Its abelian kernel is
not finitely generated as an abelian group.  Strict compression forces
`G/Gamma` to be infinite: a proper inclusion between the conjugate
subgroups `t Gamma t^(-1)<Gamma` is impossible at finite index, since the
two conjugates have equal index in `G`.  Therefore the augmentation kernel
in `(HPK21)` has infinite rank, exactly outside Theorem 3.

Pontryagin duality identifies

`dual(reduced Z[G/Gamma])=T^(G/Gamma)/T`,              `(HPK22)`

with quotient Haar measure and the shifted `G`-action.  Thus Theorem 1
specializes to the same algebraic dual action already isolated after
`(AB1)--(AB3)`; it does not silently add a periodic model.  If `(HPK21)` had
regular-trace common-Cartan microstates, their finite shadows would satisfy
`(HPK10)--(HPK12)`, while its proved nonsoficity says that they could not be
upgraded to `(HPK13)--(HPK15)`.

This is the required stress test.  Any proof of `(HPK18)` must use a
hypothesis genuinely forced by **all** hyperlinear models, not finite rank,
splitness, residual finiteness of the quotient, or Haar genericity alone.

## 7. Current boundary

The common-Cartan route now has three exact layers:

1. Birkhoff monomialization gives an abelian phase kernel over a sofic
   quotient (`CTM1--CTM19`);
2. the regular trace forces that kernel to appear as the Haar character
   field `(HPK4)--(HPK12)`;
3. combinatorial finite-phase completion `(HPK13)--(HPK15)` gives a sofic
   approximation.

Only the implication between layers 2 and 3 is missing.  The amenable case
is supplied by Burton--Chaudkhari--Juschenko--Muliarchyk, while the general
case cannot be obtained by averaging over a finite window without paying its
Følner boundary.  A successful general proof must exploit the normal `0/1`
law or the simultaneous prefix-path structure beyond the Haar Fourier
moments recorded here.

Primary source pins:

* Burton--Chaudkhari--Juschenko--Muliarchyk,
  *Hyperlinear approximations to amenable groups come from sofic
  approximations*, arXiv:2311.09202.
* Aareyan Manzoor, *There Is An Equivalence Relation Whose von Neumann
  Algebra Is Not Connes Embeddable*, arXiv:2502.06697v2.

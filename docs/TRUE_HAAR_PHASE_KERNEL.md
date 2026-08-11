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

### The extension class becomes a measurable coboundary

The phase field also remembers the extension, not only its kernel.  Choose a
normalized section `s:Q->Gamma` and define

`v(q,r)=s(q)s(r)s(qr)^(-1) in K`.                      `(HPK9a)`

Let `u_q` be the permutation ultraproduct represented by `theta(s(q))`.
There is a unique `b_q in U(A)` such that

`rho(s(q))=b_q u_q`, `b_1=1`.                         `(HPK9b)`

Write `beta_q=Ad(u_q)|A`.  Since the permutation parts multiply exactly in
the ultraproduct, multiplication of `(HPK9b)` gives

`b_q beta_q(b_r)=a_(v(q,r)) b_(qr)`.                  `(HPK9c)`

Pointwise, with the usual action convention, this is

`b_q(x)b_r(q^(-1)x)`
`  =chi_x(v(q,r))b_(qr)(x)`.                          `(HPK9d)`

Thus the `T`-valued 2-cocycle obtained by evaluating the extension cocycle
against the Haar character at `x` is a measurable coboundary on the Loeb
`Q`-space.  Changing the section changes both sides by the corresponding
1-coboundary, so the assertion is intrinsic.

This is stronger than Haar genericity.  A finite rounding must approximate
the character field, its quotient transport, and the primitive `b_q`
simultaneously.  Rounding the Haar labels while discarding `(HPK9c)` loses
the multiplication law of the total group.

### A Bockstein criterion for bounded-exponent kernels

Suppose now that `K` has exponent `m`.  Then `a_k^m=1` for every `k`, so
`(HPK9c)` implies that

`lambda_q=b_q^m`                                      `(HPK9e)`

is a measurable `T`-valued 1-cocycle:

`lambda_q beta_q(lambda_r)=lambda_(qr)`.              `(HPK9f)`

Indeed, raise `(HPK9c)` to the `m`th power inside the abelian algebra `A`.
The factor `a_(v(q,r))^m` disappears.

For the coefficient sequence

`1 -> mu_m -> T --(z |-> z^m)--> T -> 1`,

the class of `lambda` has a connecting class

`partial_m[lambda] in H^2(Q action X,mu_m)`.           `(HPK9f')`

Exactness says that this class vanishes precisely when `[lambda]` is
`m`-divisible in measurable `H^1`.  Because measurable circle-valued
0-cochains have measurable `m`th roots, vanishing is also equivalent to an
exact cocycle root as in `(HPK9g)` below.

**Theorem 2 (vanishing phase Bockstein implies soficity).**  In the common-Cartan
setup, assume `K` has finite exponent `m`.  If there is a measurable
1-cocycle `r_q in U(A)` satisfying

`r_q^m=lambda_q` for every `q in Q`,                  `(HPK9g)`

then `Gamma` is sofic.

**Proof.**  Put

`p_q=b_q r_q^(-1)`.                                   `(HPK9h)`

Equations `(HPK9e)--(HPK9g)` give `p_q^m=1`, and division of `(HPK9c)` by
the cocycle identity for `r` gives

`p_q beta_q(p_r)=a_(v(q,r))p_(qr)`.                   `(HPK9i)`

Using `(HPK6)` for covariance and `(HPK9i)` for multiplication, the formula

`rho'(k s(q))=a_k p_q u_q`                            `(HPK9j)`

is a homomorphism: the product of the formulas for `k s(q)` and `l s(r)` is
the formula for
`k (s(q)l s(q)^(-1)) v(q,r) s(qr)`.  Its diagonal phases all lie in
`mu_m`.  Represent these
finite-spectrum diagonal elements by `mu_m`-valued functions at the matrix
levels.  Equality in the tracial ultraproduct then means equality away from
`o(d_n)` coordinates, because distinct `m`th roots have a fixed positive
separation.  The skew action

`mu_m^(d_n) semidirect Sym(d_n) -> Sym([d_n] times mu_m)` `(HPK9k)`

therefore turns `(HPK9j)` into a permutation-ultraproduct homomorphism.

It is injective.  If `q!=1`, its base permutation `u_q` is nonidentity in
the metric ultraproduct by the definition of `Q`; the skew permutation moves
at least the same positive proportion.  If `q=1` and `k!=1`, Haar regularity
gives `integral_X a_k=0`.  If `r` is the measure of `{x:a_k(x)=1}`, then

`r <= |integral_X a_k|+(1-r)=1-r`,

so `r<=1/2`; the skew action of `a_k` moves at least half of its points.
Hence every nonidentity element has positive permutation length.  Fixed
finite-window diagonal product amplification converts this
positive-separation model to the usual asymptotically free normalization:
on a prescribed finite set, take the minimum of the finitely many positive
lengths and then choose one product power.  End proof.

Conversely, a `mu_m`-valued primitive `p_q` for `(HPK9c)` exists exactly when
`(HPK9g)` does: set `r_q=b_qp_q^(-1)`.  Therefore the obstruction is the
class of `lambda` modulo `m`th powers in measurable degree-one cocycles.  It
is the Bockstein residue of the evaluated extension class, not a choice of
section or of the primitive `b`.

This is the measurable-action, degree-one counterpart of the
`H^1(L,T)` ambiguity isolated in the earlier theorem “virtual divisibility
equals projective realizability” in `docs/NOTEPAD.md`.  There the same
coefficient sequence distinguishes a circle-valued trivialization from a
finite-phase trivialization of a degree-two multiplier; here `(HPK9f')`
distinguishes them for the section primitive of the common-Cartan phase
extension.

In particular the criterion holds whenever `lambda` is a measurable
coboundary.  If

`lambda_q=f beta_q(f)^(-1)`,                           `(HPK9l)`

choose a measurable `m`th root `h` of `f` and put
`r_q=h beta_q(h)^(-1)`.  Then `r` is a 1-cocycle and `r_q^m=lambda_q`.
More generally it is enough that the class of `lambda` in measurable
`H^1(Q action X,T)` be `m`-divisible.  Thus a cocycle-superrigidity theorem
which makes `lambda` cohomologous to a character of `Q` finishes this gate
whenever that character is `m`-divisible; for a perfect `Q` it is trivial.
No such superrigidity statement is known here for the arbitrary Loeb action
produced by a common-Cartan model.

The theorem is deliberately conditional.  Although `U(A)` is pointwise
divisible, roots chosen independently for the functions `lambda_q` need not
satisfy the 1-cocycle law.  Claiming otherwise would incorrectly solve the
finite-kernel extension problem.  The cocycle-stability argument
`(CS1)--(CS8)` is one finite-level mechanism which can force the needed
divisibility after approximation.

The obstruction is already nonzero on one point.  Let `Q=C_m` act trivially
and let `lambda:Q->T` send a generator to a primitive `m`th root.  Every
1-cocycle is then a character, and the `m`th power of every character of
`C_m` is trivial.  Hence `lambda` has pointwise roots as a function but no
root in `Z^1(Q,T)`.  This is the carry class of
`1->C_m->C_(m^2)->C_m->1` after evaluating the kernel by a faithful
character.

There is one immediate case where the condition is automatic.  If the phase
exact sequence `(CTM17)` itself splits and its kernel has exponent `m`, choose
the section to be a homomorphism.  Then `v=1`, `(HPK9c)` says that `b` is a
1-cocycle, and `(HPK9g)` holds with `r=b`.  Hence:

**Corollary (split bounded-exponent phase kernel).**  A regular-trace
common-Cartan model whose permutation-kernel exact sequence splits and whose
kernel has bounded exponent can exist only for a sofic group `Gamma`.

The common-Cartan hypothesis is essential here.  There are split
bounded-exponent-abelian-by-residually-finite nonsofic groups in
`(AB4)--(AB5)`; the corollary says precisely that their given abelian kernel
cannot occur as the full phase kernel of such a model.

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
Haar kernel law retained.  Equivalently, after choosing a section, it asks
for a combinatorial finite-order version of the primitive `(HPK9b)--(HPK9d)`.

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

**Theorem 3 (finite phase completion implies soficity).**  Suppose that for
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

Theorem 3 does not assume a uniform bound on `m_n`; exact equality off a
small set removes the shrinking root-spacing problem.  The unresolved step
is precisely

`L^2 phase cocycle with Haar kernel law (HPK10)--(HPK12a)`
`  ==> combinatorial finite-phase chart (HPK13)--(HPK15)`. `(HPK18)`

This is the phase-kernel form of the normal-IRS rounding problem.  Manzoor's
normal-Dirac formulation shows why an unconditional proof of `(HPK18)` would
settle hyperlinear versus sofic rather than follow from a generic IRS density
statement.

In section language, `(HPK18)` asks to replace the measurable primitive
`b_q` of `(HPK9c)` on each finite window by a finite-order primitive for which
the same equation is literally true away from a small exceptional set.  It
is not enough to approximate each `b_q` in chordal `L^2`: the spacing of the
finite phase group can shrink at the same rate, so metric closeness need not
imply equality in Hamming measure.

## 5. A positive split finite-rank case

There is one group-theoretic regime in which the phase kernel can already be
removed without `(HPK18)`.

**Theorem 4 (split finite-rank abelian kernel).**  If

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
in `(HPK21)` has infinite rank, exactly outside Theorem 4.

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

For the bounded-exponent quotient following `(AB3)`, the stress test is even
sharper.  It is a split extension by an infinite-dimensional
`Z/mZ`-module, yet it is nonsofic.  The split bounded-exponent corollary does
not contradict this: it proves that no regular common-Cartan embedding can
have that displayed module as its entire permutation kernel.  A hypothetical
common-Cartan hyperlinear embedding would have to produce a different
abelian kernel and a nondivisible Bockstein residue `(HPK9e)--(HPK9g)`.

## 7. Current boundary

The common-Cartan route now has four exact layers:

1. Birkhoff monomialization gives an abelian phase kernel over a sofic
   quotient (`CTM1--CTM19`);
2. the regular trace forces that kernel to appear as the Haar character
   field `(HPK4)--(HPK12)`;
3. for bounded-exponent kernels, the Bockstein residue
   `(HPK9e)--(HPK9g)` is the exact obstruction to fixed-alphabet completion;
4. combinatorial finite-phase completion `(HPK13)--(HPK15)` gives a sofic
   approximation.

Only the general implication from layer 2 to layer 4 is missing.  The
bounded-exponent criterion settles it when the residue in layer 3 is
divisible.  The amenable case
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

# Unbounded marked discriminant ratios imply FALSE

Date: 2026-08-11

## 1. Statement

Let

`P=<S | R>`                                                `(MDD1)`

be a finite presentation and let

`1!=w in Rad_sof(P)`.                                     `(MDD2)`

For every nonempty finite exact `P`-set `X`, use the notation of
`TRUE_EXACT_COVER_MONOMIAL_DISCRIMINANT.md`: `A_X` is the integral
phase-relator matrix, `B_(w,X)` is evaluation around the lifted `w`-loops,
and

`Lambda_(w,X)^2`
` =sup_(y in W_X minus L_X)`
`   dist(T_X y,Z^X)^2 /`
`   min_(c in D_(K_X))(`
`      d_(gamma_X(c))(y)^2+rho_(K_X)(c)^2).`            `(MDD3)`

The denominator is exactly `dist(y,Z^(X times R))^2`; it is not an
estimate.

**Theorem (marked discriminant divergence criterion).**  If

`sup_(X finite exact P-set) Lambda_(w,X)=infinity`,       `(MDD4)`

then there is a hyperlinear nonsofic group.  More precisely, there is a
homomorphism

`Phi:P -> product_omega U(d_n)`                          `(MDD5)`

into a normalized-Hilbert--Schmidt matrix ultraproduct such that
`Phi(w)!=1`; its image is hyperlinear and nonsofic.

Thus, for a fixed nontrivial sofic-radical word, proving FALSE is reduced to
making the completely finite ratio `(MDD3)` unbounded.  One does not need
to find discriminant representatives whose marked word phases are already
macroscopic before amplification.

## 2. From the lattice ratio to character ratios

For a phase table `theta` on an exact chart `X`, let `pi_theta` be its
monomial representation of the free group on `S`, and write

`chi_theta(g)=tr_X(pi_theta(g))`,                       `(MDD6)`

where `tr_X` is normalized matrix trace.  Put

`delta_theta(g)=1-Re chi_theta(g)`,
`a(theta)=sum_(r in R) delta_theta(r)`,
`b(theta)=delta_theta(w)`.                              `(MDD7)`

The exact-cover calculation gives

`C_mon(w,X)=sup_(theta:a(theta)>0)b(theta)/a(theta)`    `(MDD8)`

and the chordal/geodesic comparison gives

`(4/pi^2)Lambda_(w,X)^2 <= C_mon(w,X)`
`             <=(pi^2/4)Lambda_(w,X)^2.`               `(MDD9)`

Hence `(MDD4)` supplies charts `X_n` and phase tables `theta_n` such that,
with `a_n=a(theta_n)` and `b_n=b(theta_n)`, one has

`b_n/a_n -> infinity`.                                 `(MDD10)`

The convention in `(MDD8)` causes no pathology: integral holonomy
factorization says `a_n=0` implies `b_n=0`.  We may therefore choose
`a_n>0`.  Since `0<=b_n<=2`, equation `(MDD10)` also implies `a_n->0`.

## 3. Positive tensor amplification

Replace `pi_(theta_n)` by its conjugate double

`sigma_n=pi_(theta_n) directSum conjugate(pi_(theta_n)).` `(MDD11)`

Its normalized character is the real number

`psi_n(g)=Re chi_(theta_n)(g)`,                         `(MDD12)`

so `(MDD7)` is unchanged:

`1-psi_n(w)=b_n`,
`sum_(r in R)(1-psi_n(r))=a_n`.                        `(MDD13)`

There are two cases.

If `limsup b_n>0`, pass to a subsequence with `b_n>=eta>0` and do not
amplify.  The relator Hilbert--Schmidt defects tend to zero because

`||sigma_n(r)-1||_2^2=2(1-psi_n(r))`,                 `(MDD14)`

while the same formula keeps `w` a fixed distance from the identity.

Otherwise `b_n->0`.  Put

`m_n=ceil(1/b_n)`                                     `(MDD15)`

and let `rho_n=sigma_n^(tensor m_n)`.  Since `a_n->0`, every
`psi_n(r)` is eventually in `[0,1]`.  For `0<=t<=1`,

`1-t^m <= m(1-t)`.                                    `(MDD16)`

Consequently

`sum_(r in R)(1-psi_n(r)^(m_n))`
` <=m_n a_n`
` <=a_n/b_n+a_n ->0`.                                 `(MDD17)`

On the marked word,

`1-psi_n(w)^(m_n)`
` =1-(1-b_n)^(m_n) >=1-e^(-1).`                       `(MDD18)`

Equations `(MDD14)`, applied to the tensor-power characters, show that the
`rho_n` asymptotically kill every relator in normalized Hilbert--Schmidt
norm while keeping `w` a fixed positive distance from the identity.

## 4. The hyperlinear nonsofic image

The matrices assigned to the free generators define a homomorphism from
the free group to the tracial matrix ultraproduct.  Equation `(MDD17)` (or
the first case above) kills the normal closure of `R`, so it factors as
`Phi` in `(MDD5)`.  Equation `(MDD18)` says `Phi(w)!=1`.

Let `Q=Phi(P)`.  It is hyperlinear, being a subgroup of a tracial matrix
ultraproduct.  If `Q` were sofic, then the quotient homomorphism

`P -> Q`                                                `(MDD19)`

would kill every element of `Rad_sof(P)`, in particular `w`.  This
contradicts `Phi(w)!=1`.  Therefore `Q` is nonsofic.  End proof.

The construction stays inside the same model class.  A direct sum with the
complex-conjugate monomial representation is monomial on the disjoint union
of two copies of `X_n`, and a tensor power is monomial on the Cartesian
power of that finite `P`-set.  Hence the output in `(MDD5)` is represented
by exact-chart monomial microstates, not merely by arbitrary unitary
microstates.

**Corollary (exact monomial-sector equivalence).**  Under `(MDD1)--(MDD2)`,
the following are equivalent.

1. `sup_X Lambda_(w,X)=infinity`.
2. There are exact finite-chart monomial representations which kill every
   relator asymptotically in normalized Hilbert--Schmidt norm and retain
   `w` at positive normalized Hilbert--Schmidt distance.
3. There is an exact-chart monomial hyperlinear image of `P` which retains
   `w` and is therefore nonsofic.

**Proof.**  The theorem, together with the preceding closure observation,
proves `1=>2=>3`.  For `2=>1`, let `a_n,b_n` be as in `(MDD7)`.  The
relator condition gives `a_n->0`, while retention gives `liminf b_n>0` by
`(MDD14)`.  Thus `b_n/a_n->infinity`; equations `(MDD8)--(MDD9)` force
`sup_X Lambda_(w,X)=infinity`.  End proof.

## 5. Exact remaining finite target

Combining the theorem with `(MDD3)`, it is sufficient to exhibit exact
finite `P`-sets `X_n` and points `y_n in W_(X_n)` for which

`dist(T_(X_n)y_n,Z^(X_n))^2 /`
`min_(c in D_(K_(X_n)))(`
` d_(gamma_(X_n)(c))(y_n)^2+rho_(K_(X_n))(c)^2)`
` ->infinity.`                                         `(MDD20)`

This is weaker than the earlier unamplified requirement that the numerator
be macroscopic and the denominator vanish after normalization.  Any
divergence rate works: tensor powers supply the missing macroscopic scale.

The `p=53` rank-two pullback is therefore useful in exactly the following
way.  It makes every denominator well in the harmonic dangerous quotient a
binary quadratic closest-vector problem.  To prove FALSE from that chart
family, one must additionally evaluate the two integral functionals coming
from the fixed radical filling vectors and prove that their numerator in
`(MDD20)` outruns the least paired well.  The rank-two calculation alone
does not establish this divergence.

## 6. Relation to the universal radical constants

`TRUE_RADICAL_DOMINATION_CONSTANTS.md` proves abstractly that a word lies
outside the hyperlinear radical exactly when its finite-dimensional
character domination constant is infinite.  The result here is its exact
monomial/discriminant specialization:

`sup_X Lambda_(w,X)=infinity`
` => C_fd(P,w;R)=infinity`
` => w notin Rad_hyp(P)`.                              `(MDD21)`

The substantive new reduction is the first implication with the explicit
finite formula `(MDD3)`, together with the observation that no separate
macroscopic marked-class hypothesis is required.

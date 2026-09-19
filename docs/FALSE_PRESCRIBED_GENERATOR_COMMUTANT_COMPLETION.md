# Prescribed diffuse generators extend inside finite regular commutants

Date: 2026-08-11

## 1. Outcome

There is a general prescribed-generator theorem which closes the external
group problem `(QBE29)` from
`FALSE_RADICAL_BS_Q_BIMODULE_EXTENSION.md`.

Let `(F_n)` be finite groups and let `a_n in F_n`.  Assume that, for every
fixed nonzero integer `m`,

`|C_(F_n)(a_n^m)|/|F_n| ->0`.                         `(PGC1)`

Let `Lambda` be a countable sofic group and let `t in Lambda` have infinite
order.  Then there are multiplicities `r_n` and asymptotic homomorphisms

`Phi_n:Lambda -> U(L(F_n)' tensor M_(r_n))`             `(PGC2)`

in normalized Hilbert--Schmidt norm such that

`Phi_n(t)=R_(F_n)(a_n) tensor 1_(r_n)`                 `(PGC3)`

exactly at every level.  Here `L(F_n)'` is the commutant of the left
regular representation and `R_(F_n)` is right translation.

For

`F_n=SL_3(Z/p^n Z)`,
`a_n=diag(1+p,1,(1+p)^(-1))`,                          `(PGC4)`

condition `(PGC1)` holds.  Taking `Lambda=SL_d(Z)` and `t=I+e_12` proves

`epsilon_n^(L)->0`                                    `(PGC5)`

for the amplified version of `(QBE29)`, with the prescribed compressor
`R(a_n)^(-1)` after replacing `a_n` by `a_n^(-1)` if required by the
orientation convention.

Thus the frozen-clock block can satisfy all abstract `Q times L` group
relations while retaining its exact coefficient-`Q` covariance and its
macroscopic fold.  The remaining gate is narrower: make these external
microstates implement the required monomial substitutions on the Laurent
square-zero tangent module and the base elementary group.

## 2. Plancherel spectral concentration

Write `Irr(F)` for the irreducible complex representations of a finite
group `F`.  The left regular decomposition is

`ell^2(F)=directSum_(pi in Irr(F)) V_pi tensor C^(d_pi)`,
`d_pi=dim V_pi`,                                       `(PGC6)`

and

`L(F)'=directSum_pi 1_(V_pi) tensor M_(d_pi)(C)`.      `(PGC7)`

The normalized trace assigns weight

`w_pi=d_pi^2/|F|`                                     `(PGC8)`

to the `pi` block.  On that block, right translation by `a` is unitarily
equivalent to the contragredient of `pi(a)`.  Let

`m_(pi,a)(j)=tr_(d_pi)(pi(a)^j)=chi_pi(a^j)/d_pi`.     `(PGC9)`

Column orthogonality gives the exact second-moment identity

`sum_pi w_pi |m_(pi,a)(j)|^2`
` =(1/|F|)sum_pi |chi_pi(a^j)|^2`
` =|C_F(a^j)|/|F|`.                                  `(PGC10)`

Under `(PGC1)`, for every fixed `j!=0`, the normalized spectral measure of
`pi(a_n)` has `j`th moment tending to zero in Plancherel probability.
By a diagonal choice of integers `J_n->infinity` and tolerances
`eta_n->0`, there are sets

`Good_n subset Irr(F_n)`, `sum_(pi in Good_n)w_pi->1`, `(PGC11)`

such that for every `pi in Good_n`,

`|m_(pi,a_n)(j)|<=eta_n`, `0<|j|<=J_n`.               `(PGC12)`

Trigonometric polynomial approximation on the circle now implies that the
spectral measures in `(PGC12)` converge uniformly, over `Good_n`, to Haar
measure in any metric inducing weak convergence.  On the compact circle
this includes quadratic transport distance.  Equivalently, their
eigenvalues can be matched in normalized mean squared chordal distance to
any other empirical measures converging to Haar.

## 3. Sofic microstates in every sufficiently large dimension

Fix a finite multiplication window `E subset Lambda` and `epsilon>0`.
Soficity supplies a finite permutation microstate

`sigma:E->Sym(N)`                                      `(PGC13)`

with Hamming multiplicativity defect at most `epsilon`.  Include the
nontrivial powers

`t,t^2,...,t^J`                                       `(PGC14)`

in the separation window.  Since these powers are distinct, the fixed-point
fractions of `sigma(t)^j`, `0<|j|<=J`, can be made at most `epsilon`.
Therefore the empirical spectral measure of the permutation matrix
`sigma(t)` has its first `J` nonzero moments at most `epsilon`.

For every sufficiently large dimension `D`, take as many orthogonal copies
of `(PGC13)` as fit in `D` and fill the remaining fewer than `N` dimensions
by identities.  Denote the resulting unitary microstate by

`sigma_D:E->U(D)`.                                    `(PGC15)`

The remainder has relative dimension at most `N/D`.  Hence, uniformly for
large `D`,

1. all multiplication defects in `E` are at most the original defect plus
   `O(sqrt(N/D))` in normalized HS norm; and
2. the spectral measure of `sigma_D(t)` is as close to Haar as desired by
   first choosing `J` large and `epsilon` small, then taking `D/N` large.

This elementary repetition argument is why no lower bound on the
irreducible dimensions of `F_n` is needed below: the free multiplicity
`r_n` makes every block dimension `d_pi r_n` large.

## 4. Matching the prescribed generator block by block

Amplify `(PGC7)` by `M_(r_n)`.  On the `pi` block the prescribed unitary is

`U_(pi,n)=contragredient(pi(a_n)) tensor 1_(r_n)`.     `(PGC16)`

Its spectral measure is the same as that of `pi(a_n)`.  Choose `r_n` so
large that Section 3 constructs the required window microstate in every
dimension `d_pi r_n`.

For `pi in Good_n`, both `U_(pi,n)` and the tentative matrix
`sigma_(d_pi r_n)(t)` have spectral measures close to Haar.  Match their
eigenvalues and conjugate the whole tentative microstate so that

`||sigma_(d_pi r_n)(t)-U_(pi,n)||_2=o(1)`             `(PGC17)`

uniformly on `Good_n`.  Replace the matrix assigned to `t` by
`U_(pi,n)` exactly.  If a tested word has length at most `ell`, telescoping
shows that this replacement increases its normalized HS defect by at most

`ell ||sigma_(d_pi r_n)(t)-U_(pi,n)||_2=o(1)`.        `(PGC18)`

On the bad blocks `Irr(F_n) minus Good_n`, assign arbitrary unitaries to
the other elements and retain `(PGC16)` for `t`.  Every unitary relation
has norm defect at most two there.  Their total trace weight tends to zero
by `(PGC11)`, so their contribution to squared normalized HS defect is
`o(1)`.

Taking the direct sum over all `pi` proves the desired microstate on the
chosen finite window, with `(PGC3)` exact.  A diagonal sequence over
increasing windows proves `(PGC2)`.

## 5. The congruence centralizer estimate

Fix an odd prime `p`, put `q=1+p`, and let

`F_n=SL_3(Z/p^n Z)`, `a_n=diag(q,1,q^(-1))`.           `(PGC19)`

Fix `m!=0`.  The lifting-the-exponent formula gives, for all sufficiently
large `n`,

`v_p(q^m-1)=1+v_p(m)=:v_m<n`.                         `(PGC20)`

Conjugate `a_n^m` by

`u_x=1+x e_12`, `x in Z/p^n Z`.                       `(PGC21)`

The `(1,2)` entry of `u_x a_n^m u_x^(-1)` differs from that of `a_n^m` by
a unit multiple of

`x(q^m-1)`.                                           `(PGC22)`

As `x` varies, `(PGC22)` assumes exactly `p^(n-v_m)` values.  Thus the
conjugacy class of `a_n^m` has at least that cardinality, and

`|C_(F_n)(a_n^m)|/|F_n|`
` <=p^(-(n-v_m))->0`.                                 `(PGC23)`

This is `(PGC1)`.  The same proof applies to `a_n^(-1)`.

## 6. Application to the radical clock block

Use the coefficient representation from
`FALSE_RADICAL_BS_Q_BIMODULE_EXTENSION.md`, amplified by `r_n`.  The common
coefficient group acts by `L_n(Q_n) tensor 1`, while the external group
acts through `(PGC2)` in its commutant.  Therefore every cross-commutator
between `Q` and `L` is exactly zero.

Choose the orientation in which the compressor `t` is assigned

`Phi_n(t)=R_n(c_0)^(-1) tensor 1`.                    `(PGC24)`

Equations `(QBE17)--(QBE20)` remain exact after amplification, and
`(QBE6)` still gives fold displacement squared two.  The theorem above
makes every fixed abstract relator of `SL_d(Z)` tend to zero.

What remains is not another abstract group-relation search.  The matrices
for the other external generators must be coupled to representations of
the monomial-labelled tangent elements so that

`Phi_n(s) D_n(z) Phi_n(s)^* ~=D_n(alpha_s(z))`         `(PGC25)`

for the finitely many tangent and base-elementary generators in each fixed
window.  The current block proves `(PGC25)` exactly for the coefficient
`Q_n` action and for the distinguished compressor on the marked element.
The unsolved part is simultaneous Laurent-monomial covariance for all
external generators.

This separates the final extension cleanly:

* coefficient-square-zero algebra: exact;
* coefficient `Q`: exact;
* abstract external `L` relations with prescribed compressor: asymptotically
  solved;
* full monomial/base-elementary covariance: open.

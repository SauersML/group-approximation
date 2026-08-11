# TRUE lane: a quantitative Cartan-to-monomial gate

Date: 2026-08-10

This note proves a dimension-free conversion from approximate preservation of
one common matrix diagonal to a common monomial model.  It then identifies the
one extra condition under which the monomial model can be stripped to a sofic
approximation.  The result is a genuine sufficient criterion for
hyperlinear-to-sofic transfer, but the criterion is not proved for arbitrary
hyperlinear groups.  In particular, this note does **not** claim to solve the
main open problem.

## 1. Average Cartan displacement

Let `D_d` be the diagonal masa in `M_d(C)`, let `E_D` be the trace-preserving
conditional expectation onto `D_d`, and write `p_j=e_(j,j)`.  For `U in U(d)`
define

`kappa_D(U)=sum_(j=1)^d ||U p_j U^* - E_D(U p_j U^*)||_(2,d)^2`.  `(CTM1)`

Here `||.||_(2,d)^2=d^(-1)Tr(.^*.)`.  If `U=(u_(i,j))`, then

`kappa_D(U)=1-d^(-1) sum_(i,j)|u_(i,j)|^4`.             `(CTM2)`

Thus `0<=kappa_D(U)<=1`, and `kappa_D(U)=0` exactly when `U` normalizes the
diagonal, equivalently when `U` is monomial in this basis.

The following estimate is the useful new point.

**Theorem 1 (dimension-free Birkhoff monomialization).**  For every
`U in U(d)` there is a monomial unitary `M` normalizing `D_d` such that

`||U-M||_(2,d)^2 <= 2 kappa_D(U)`.                      `(CTM3)`

The same statement holds for an arbitrary masa after unitary conjugacy.

**Proof.**  Put `B_(i,j)=|u_(i,j)|^2`.  The matrix `B` is doubly stochastic.
Choose a Birkhoff decomposition

`B=sum_s lambda_s P_(sigma_s)`, `lambda_s>=0`, `sum_s lambda_s=1`. `(CTM4)`

Taking its Frobenius inner product with `B` gives

`sum_(i,j) B_(i,j)^2`
` =sum_s lambda_s sum_j B_(sigma_s(j),j)`.              `(CTM5)`

Consequently some permutation `sigma` satisfies

`sum_j |u_(sigma(j),j)|^2 >= sum_(i,j)|u_(i,j)|^4`.    `(CTM6)`

Choose phases `zeta_j` so that
`conjugate(u_(sigma(j),j)) zeta_j=|u_(sigma(j),j)|`, and let

`M e_j=zeta_j e_(sigma(j))`.                            `(CTM7)`

Since `0<=|u_(sigma(j),j)|<=1`, equations `(CTM6)` and `(CTM2)` give

`Re tau_d(U^*M)=d^(-1)sum_j |u_(sigma(j),j)|`
` >=d^(-1)sum_j |u_(sigma(j),j)|^2`
` >=1-kappa_D(U)`.                                     `(CTM8)`

Therefore

`||U-M||_(2,d)^2=2-2 Re tau_d(U^*M)<=2 kappa_D(U)`,

which is `(CTM3)`.  End proof.

The constant is independent of `d`; no entrywise or operator-norm control is
being assumed.

## 2. Multiplication survives in the permutation parts

Let `M_g` be monomial and let `sigma_g` denote its underlying permutation.
If `M` and `N` have underlying permutations `sigma` and `rho`, then every
column on which `sigma` and `rho` differ contributes exactly `2` to the
unnormalized squared Frobenius distance.  Hence

`2 d_Ham(sigma,rho) <= ||M-N||_2^2`.                   `(CTM9)`

Suppose `phi:G->U(d)` is a finite unitary table.  Apply Theorem 1 to obtain
`M_g` for all entries of the table, and put

`e_g=||phi(g)-M_g||_2 <= sqrt(2 kappa_D(phi(g)))`.      `(CTM10)`

Bi-invariance of normalized Hilbert--Schmidt distance gives

`||M_g M_h-M_(gh)||_2`
` <= e_g+e_h+||phi(g)phi(h)-phi(gh)||_2+e_(gh)`.        `(CTM11)`

Combining `(CTM9)` and `(CTM11)` shows that a common approximately invariant
masa is enough to transfer every multiplication estimate to the underlying
permutations.  This is stronger than separately diagonalizing the generators:
the same masa is used for the whole table.

## 3. The phase gate for separation

Multiplication is not the last issue.  If `j` is fixed by `sigma_g`, write

`M_g e_j=zeta_(g,j)e_j`.                               `(CTM12)`

Then

`Re tau_d(M_g)=d^(-1) sum_(j in Fix(sigma_g)) Re zeta_(g,j)`. `(CTM13)`

Cancellation among the phases can make this trace zero even when every point
is fixed.  The elementary `C_4` example with phases `+i` and `-i` is the
finite-level calibration; conjugate tensoring makes characters nonnegative
but does not by itself remove fixed-point phase cancellation.

The obstruction persists all the way to the normal `0/1` limit.  Let
`C_4=<g>` and let `V=1 directSum chi`, where `chi(g)=i`.  The normalized
character of `W=V tensor conjugate(V)` is

`psi=(1,1/2,0,1/2)` on `(1,g,g^2,g^3)`.               `(CTM13a)`

Therefore the exact representations `W^(tensor m)` have normalized
characters `psi^m`, which converge to the regular character `delta_1` of
`C_4`.  Every one of these representations is diagonal in one common tensor
basis, so its Cartan displacement is identically zero.  Nevertheless the
underlying permutation of every represented group element is the identity.
Thus even

`exact representation + kappa_D=0 + character -> normal 0/1`              `(CTM13b)`

does not make the naively stripped permutations separating.  Of course
`C_4` itself is sofic; the example proves that a successful theorem is allowed
to replace the given unitary tables, but cannot merely discard their phases.

There is, however, an exact positive criterion.

**Theorem 2 (Cartan plus a fixed-phase half-plane implies soficity).**  Let
`Gamma` be a countable hyperlinear group.  Suppose it has hyperlinear tables

`phi_n:Gamma->U(d_n)`                                  `(CTM14)`

and masas `D_n` with the following properties for every fixed `g,h in Gamma`:

1. `||phi_n(g)phi_n(h)-phi_n(gh)||_2 -> 0`;
2. `tau_(d_n)(phi_n(g))->1_(g=1)`;
3. `kappa_(D_n)(phi_n(g))->0`;
4. after choosing the monomial approximants `M_(n,g)` from Theorem 1, for
   every `g!=1` there is `c_g>0` such that, eventually,

   `Re zeta_(n,g,j) >= c_g`

   for every fixed point `j` of the underlying permutation `sigma_(n,g)`.

Then `Gamma` is sofic.

**Proof.**  Equations `(CTM10)--(CTM11)` and `(CTM9)` show that the maps
`g |-> sigma_(n,g)` are asymptotically multiplicative in normalized Hamming
distance.  For `g!=1`, Cauchy--Schwarz and `(CTM10)` give

`|tau(M_(n,g))-tau(phi_n(g))| <= e_(n,g) -> 0`.         `(CTM15)`

Using `(CTM13)` and hypothesis 4,

`c_g |Fix(sigma_(n,g))|/d_n`
` <= Re tau(M_(n,g)) -> 0`.                            `(CTM16)`

Thus every nonidentity element moves asymptotically every point.  These are
the two defining estimates for a sofic approximation.  End proof.

For a finite soficity test one only needs the minimum of the finitely many
constants `c_g` appearing in that test.

## 4. What this changes in the finite-prefix program

The finite-prefix construction `(FPC1)--(FPC12)` in `docs/NOTEPAD.md`
produces coherent unitary word paths on one asymptotically full corner.  The
present theorem says that its remaining joint matching problem would be
finished by two concrete outputs:

1. a masa of the corner whose displacement `(CTM1)` tends to zero for every
   completed generator; and
2. a choice of the Birkhoff matchings `(CTM6)` for which fixed-point phases
   stay in a common open half-plane on the witness window.

The first output gives multiplication by `(CTM11)`, while the second turns
trace separation into moved-point separation by `(CTM16)`.  These are
logically independent.  Approximate Cartan invariance alone does not control
phase cancellation—even in the exact normal-limit example `(CTM13a)`—and a
phase condition without one common Cartan does not produce coherent
permutations.

This also gives a stopping rule for prospective TRUE proofs.  A proposed
random-basis, matrix-unit, or atom-matching argument must estimate
`kappa_D`, not merely diagonalize each generator separately.  After that it
must still address `(CTM13)`; citing nonnegative normalized characters is not
enough.

## 5. Exact remaining question

The useful strengthened target is now:

> Given finite-dimensional characters converging to the normal `0/1`
> character `1_N` of `F/N`, can one replace the tables, without changing the
> tested character losses, by tables satisfying hypotheses 3 and 4 of
> Theorem 2?

A positive answer proves every hyperlinear group sofic.  Theorem 1 removes
the matrix-to-monomial part once the common Cartan has been constructed; the
unproved work is construction of that Cartan together with noncancelling
fixed phases.  For nonamenable quotients no dimension-free construction of
those two objects is currently established here.

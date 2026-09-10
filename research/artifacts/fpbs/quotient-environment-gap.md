# A spectral gap for the stationary critical quotient environment

This is a comparison deduction, not a proof of Benjamini--Schramm or
a claim of priority. The operator below acts on random rooted marked
environments, not on the vertices of a single realized quotient graph.
The quotient and Palm construction are proved in
`critical-quotient-sprinkling.md`. This completes the calculation proposed
in `notes/fpbs-critical-quotient-environment-gap-2026-09-09.md`.

## 1. Probability space and statement

Let G=Cay(Gamma,S) be the fixed d-regular nonamenable Cayley graph. Write
R for its nonlazy walk operator on l2(Gamma), r=||R||<1, and
rho=(1+r)/2. All percolation labels, independent vertex priorities and
signs are realized on a single vertex Bernoulli space (Omega,P), using
the disjoint half-edge construction in `spectral-spike.md`, Section 2.
On its mean-zero L2 space the nonlazy Koopman average A satisfies

    <F,(I-A)F>_P >= (1-r) Var_P F.                       (1)

This follows from the direct sum of finite-stabilizer representations
proved there; nonamenability supplies r<1 by Kesten's criterion.

Contract the finite critical clusters C to the loopless multigraph Q,
retaining every edge between different cells with its multiplicity.
Write m(C)=|C|, B(C)=deg_Q(C), kappa=E_P[1/m(C_o)], and
Z=E_P[B(C_o)/m(C_o)]. If h>0 is the edge isoperimetric constant, then
h m<=B<=d m and h<=Z<=d.

Keep the original vertex decorations, internal finite cell graphs, and
boundary incidences as marks on Q, modulo isomorphism. Do not mark the
original root vertex inside the root cell. Equivalently, the observables
used below are measurable equivariant functions of the environment and
a distinguished cell, constant when the original root moves within that
cell. This convention ensures that rerooting changes only the cell.
One may forget marks and restrict to the resulting observable subspace.

The unimodular quotient law is P_dagger, obtained from the original root
law by the density 1/(kappa m). Its degree bias nu is the stationary law:

    E_nu phi = E_P[(B/m) F]/Z,     F(omega)=phi(Q,C_o).   (2)

Let K move the distinguished cell across one uniformly selected boundary
edge, counting multiplicity, without changing any marks. Then K is a
self-adjoint Markov contraction on L2(nu), and

    <phi,(I-K)phi>_nu >= (1-r) Var_nu phi.                (3)

Consequently L=(I+K)/2 has spectrum in [0,rho] on L2_0(nu).
All statements concern the stationary environment law; no fixed
realization spectral gap is being inferred from (3).

## 2. Reversibility and the energy identity

For adjacent cells C,D let a(C,D) count their boundary edges.
Unimodularity of P_dagger applied to
a(C,D) phi(Q,C) psi(Q,D) gives

    E_nu[phi K psi]
      = E_dagger sum_D a(C,D) phi(Q,C) psi(Q,D) / E_dagger B
      = E_nu[psi K phi].

For signed bounded functions apply mass transport to positive and
negative parts; integrability follows from E_dagger B<infinity.
Taking phi=1 proves stationarity. Conditional Jensen gives the L2
contraction and hence its extension from bounded observables.

For bounded phi, put F_x=phi(Q,C_x) and
H(x)=sum_{y:y~x}(F_x-F_y)^2. Same-cell edges contribute zero, including
closed original edges whose endpoints are in the same critical cell.
The quotient Dirichlet form from (2) is

    E_nu[phi(I-K)phi]
      = (1/(2Z)) E_P[(1/m(C_o)) sum_{x in C_o} H(x)].

The original Cayley mass transport
T(x,y)=1{y in C_x} H(x)/m(C_x) has outgoing sum H(x) and incoming sum
m(C_y)^(-1) sum_{x in C_y} H(x). Thus

    E_nu[phi(I-K)phi]
      = (1/(2Z)) E_P H(o)
      = (d/Z) <F,(I-A)F>_P.                             (4)

Here H is bounded by 4d||phi||_infinity^2. There is no requirement of
a finite second moment of m or B.

## 3. Variance comparison and L2 extension

The variance minimization formula and B/m<=d imply

    Var_nu phi
      = inf_a E_P[(B/m)(F-a)^2]/Z
      <= (d/Z) E_P[(F-E_P F)^2]
      = (d/Z) Var_P F.                                  (5)

Equations (1), (4), and (5) prove (3) for bounded observables. Truncating
an arbitrary real L2(nu) observable gives L2 convergence, convergence
of variance, and convergence of its Dirichlet form since I-K is bounded.
Hence (3) holds on all of L2(nu). Complex observables follow by their
real and imaginary parts. The spectral assertion follows from
self-adjointness, the Markov norm bound ||K||<=1, and (3).

## 4. What the gap does and does not say about sprinkling

The same space can retain all original labels and the independent signs
and priorities, so (3) applies simultaneously to every fixed sprinkling
parameter t. Set q=c+(1-c)t. Let theta_nu(t) be the nu-probability that
the root quotient cell lies in an infinite sprinkled component, and
let Y_n be the stationary lazy quotient walk. Define

    f_n(t)=P_nu(C_o connected to Y_n by sprinkled edges,
                the sprinkled component of C_o is finite).

Give a finite sprinkled component the sign of its original vertex of
minimum priority, and give infinite components zero. Finite quotient
components contain finitely many original vertices. The sign observable
is cell-constant, has mean zero and variance 1-theta_nu(t). The walk
depends only on Q and its independent step choices, not these signs.
Conditioning on percolation, priorities and walk therefore proves that
f_n(t) is its L-moment. In particular it has a positive spectral measure
supported on [0,rho], and

    0 <= f_n(t) <= (1-theta_nu(t)) rho^n.                 (6)

If the sprinkled configuration has a unique infinite component almost
surely, write J=1{C_o in that component}-theta_nu(t). The full
connectivity moments satisfy exactly

    a_n(t)=theta_nu(t)^2 + <J,L^n J>_nu + f_n(t).         (7)

The last two terms are spectral moments on [0,rho]. Formula (7) allows
an atom of arbitrarily small positive mass theta_nu(t)^2 at 1.
Moreover (2) gives

    (h/Z) theta(q) <= theta_nu(t) <= (d/Z) theta(q),

so theta_nu(t) tends to zero as t decreases to zero, by critical
finiteness and continuity under the monotone coupling. Thus this
inherited gap does not, by this calculation, contradict uniqueness for
every positive sprinkling parameter. It returns the spectral-atom
obstruction already identified for the original Cayley walk.

## 5. Verification scope

`scripts/replay_quotient_environment_gap.py` tests the normalization and
spectral comparison on all nontrivial connected-cell partitions of four
small regular graphs. It uses exact rational arithmetic and a Schur
complement positive-semidefiniteness check, with known original gaps.
Its output is `quotient-environment-gap-replay.json`. These finite
checks do not verify the infinite probability-space argument. Cairn's
parser, linter and dependency compilation are recorded separately in
`quotient-environment-gap-validation.json`.

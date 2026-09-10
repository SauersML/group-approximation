# Next calculation: the stationary quotient environment

This is a research calculation to audit, not an established Cairn route
and not a proof of Benjamini--Schramm. It follows the obstruction in
`research/artifacts/fpbs/critical-quotient-sprinkling.md`: generic
unimodularity and expansion lose essential information about the fixed
Cayley graph.

Let P be the original Bernoulli label law on the fixed d-regular Cayley
graph. For its critical quotient, write m(C)=|C|, B(C)=deg_Q(C),
kappa=E_P[1/m(C_o)], and Z=E_P[B(C_o)/m(C_o)]. Thus h<=Z<=d. Start from
the Palm quotient root law P_dagger, then bias it by B to obtain the
stationary root law nu for simple random walk on Q. For a bounded
observable phi of the rooted marked quotient put F(omega)=phi(Q,C_o).

The formulas to check carefully are

    E_nu phi = E_P[(B(C_o)/m(C_o)) F]/Z,

    <phi,(I-K)phi>_nu
      = (1/(2Z)) E_P sum_{s in S} (F(omega)-F(s.omega))^2,

where K moves the quotient root across a uniformly chosen boundary edge,
retaining edge multiplicity. The second identity should follow by spreading
each cell's boundary transport uniformly over its m vertices. Open
critical edges contribute zero because F is constant on that cell.

If these identities hold on the intended marked probability space, the
Bernoulli-shift spectral gap gives a promising comparison. Let g>0 be
the gap of the nonlazy Cayley walk on mean-zero Bernoulli observables.
Then the right side of the energy identity is at least

    (d g/Z) Var_P(F).

Meanwhile the bounded density B/m<=d gives

    Var_nu(phi) <= (d/Z) Var_P(F).

Together they would yield gap(K)>=g, initially for bounded observables
and then by L2 approximation. The positive lower bound B/m>=h makes the
two root laws comparable on cell observables. This concerns the Markov
operator on RANDOM ROOTED ENVIRONMENTS, which must be kept separate from
the quenched walk operator on the vertices of one realization.

Audit points: specify the quotient marks so F is measurable, equivariant,
and independent of the choice of root inside a critical cell; verify the
mass transport and reversibility with parallel edges; handle the L2
extension; determine whether the resulting gap supplies anything beyond
the previously proved spectral-atom decomposition. In particular, a
spectral gap by itself does not exclude an arbitrarily small atom at 1 in
the full connectivity moment measure. A valid proof of this comparison
would still require an additional argument to resolve the original goal.

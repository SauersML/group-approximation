# Independent edge resampling and an averaged-projection resolvent bound

Date: 2026-09-10. These are written operator deductions with finite exact
checks, not a solution of Benjamini--Schramm or a claim of priority.
The distinction between averaging over a cluster and summing over it
is essential throughout.

## 1. Finite product-space identity

Let G=(V,E) be a finite graph and let P_omega be the orthogonal projection
that replaces a function by its mean on each open cluster. Put
Q_p=E_p P_omega, for independent Bernoulli-p edges and 0<p<1.
Use the unnormalized graph Laplacian

    L_G=sum_{e={x,y}} (delta_x-delta_y)(delta_x-delta_y)^*.

All order inequalities below are in the positive-semidefinite order.
No sign assertion about an inverse connectivity matrix is made.

**Theorem 1.** The following identity and inequality hold:

    D_p := -p(1-p) Q_p' - Q_p + Q_p^2
         = sum_{A subset E, |A|>=2} (|A|-1) P_hat(A)^* P_hat(A)
         >= 0.                                             (1)

Here P_hat(A)=E[P_omega chi_A(omega)] and chi_A is the normalized
Bernoulli product character
prod_{e in A}(omega_e-p)/sqrt(p(1-p)).

**Proof.** For fixed other edges let P_0,P_1 be the projections before
and after opening e. Their ranges are nested. Their difference
Delta_e=P_0-P_1 is consequently an orthogonal projection. More explicitly,
it is zero if the endpoints were connected and otherwise is the
rank-one merger projection proved in `creative-branches.md`, Section 2.1.
Thus Delta_e^2=Delta_e.

Entrywise differentiation of the finite product expectation gives

    -Q_p'=sum_e E_{E\{e}} Delta_e.

For any deterministic f, expand the vector-valued function P_omega f
in the orthonormal product basis. Orthogonality gives

    E||P_omega f-Q_p f||^2
      = sum_{A nonempty} ||P_hat(A)f||^2
      = <f,(Q_p-Q_p^2)f>.

The last equality uses P_omega^2=P_omega. Conditioning all coordinates
except e and summing their conditional variances gives, by the same
product expansion,

    sum_e p(1-p) E_{E\{e}} ||Delta_e f||^2
      = sum_A |A| ||P_hat(A)f||^2
      = <f,-p(1-p)Q_p' f>.

Subtract the previous two identities and use polarization to obtain
(1). This proves the Hilbert-valued product variance inequality needed
here, rather than treating a scalar variance estimate as an operator
bound. No derivative and operator limit have been interchanged. QED.

## 2. A finite-volume resolvent bound with a positive remainder

**Theorem 2.** For 0<p<1,

    Q_p <= [I + p L_G/(2(1-p))]^{-1}.                     (2)

In fact, with R_p=Q_p^{-1}-I,

    ((1-p)/p) R_p
      = L_G/2 + integral_0^p Q_u^{-1} D_u Q_u^{-1}/u^2 du. (3)

**Proof.** The event that every edge is closed gives
Q_p>=(1-p)^{|E|} I, so inversion and differentiation are valid in this
finite-dimensional calculation. Congruencing (1) by Q_p^{-1} gives

    R_p' = [R_p + Q_p^{-1}D_p Q_p^{-1}]/[p(1-p)].

The product rule, without any assumption that Q_p commutes with its
derivative, yields

    d/dp [((1-p)/p) R_p] = Q_p^{-1}D_p Q_p^{-1}/p^2 >= 0.

At p=0 every cell is a singleton. Opening one edge removes the projection
(delta_x-delta_y)(delta_x-delta_y)^*/2. Hence
Q_p=I-p L_G/2+O(p^2), R_p=p L_G/2+O(p^2), and D_p=O(p^2).
The integrand in (3) is therefore bounded near zero. Integration proves
(3), and dropping its positive integral followed by inversion proves
(2). QED.

This is a bound for Q_p(x,y)=E[1{x connected to y}/|C_x|].
It is not a bound for the unnormalized two-point matrix T_p.

## 3. Infinite graphs and the critical consequence

Let G now be any countable bounded-degree graph. Define P_omega on l2(V)
by averaging on finite open clusters and by zero on infinite clusters.
This is the orthogonal projection onto square-summable functions that
are constant on every open cluster. Define Q_p=E P_omega.

**Theorem 3.** Inequality (2) holds on l2(V), with the bounded graph
Laplacian L_G. It does not require criticality or cluster finiteness.

**Proof.** Exhaust E by finite edge sets E_n and leave all other vertices
isolated. The resulting P_{omega,n} are a decreasing sequence of
orthogonal projections. Their ranges have intersection exactly the
space of l2 functions constant on every full open cluster; on an infinite
cluster such a constant must vanish. The projections therefore converge
strongly to P_omega. The contraction bound and dominated convergence
give Q_{p,n}->Q_p strongly.

The finite-edge Laplacians L_n converge strongly to L_G and have uniformly
bounded norms. For a=p/(2(1-p)), the resolvent identity and
||(I+aL_n)^{-1}||<=1 give strong convergence of the right sides of (2).
Apply the finite theorem and pass to the limit in each quadratic form.
QED. The infinite theorem uses this strong-limit argument; it does not
assert operator-norm differentiability of infinite-volume Q_p.

For a nonamenable d-regular Cayley graph, let r be the norm of its
nonlazy regular walk, so L_G>=d(1-r)I and r<1. Consequently

    ||Q_p|| <= 2(1-p) / [2(1-p)+p d(1-r)] < 1, p>0.      (4)

In particular this holds at p_c. The graph-dependent spectral positivity
used here is Kesten's criterion, already used in `spectral-spike.md`.
A qualitative gap for Q_p can also be obtained from its strictly positive
nearest-neighbor entries; (2)-(3) give the explicit order comparison and
identify the positive product-noise remainder. We do not present the
mere existence of a gap as a new percolation theorem.

## 4. Independent ghost marks: the bound persists, the subtraction does not

Mark each vertex independently with probability s. Let P_{omega,eta}
average on unmarked clusters and vanish on every cluster containing a
mark. Its expectation has kernel, for finite clusters,

    Q_{p,s}(x,y)=E_p[(1-s)^{|C_x|}/|C_x|; x connected to y].

Infinite clusters contribute zero, including at s=0 under the projection
convention in Section 3. Then

    Q_{p,s} <= [I + p L_G/(2(1-p)) + s I/(1-s)]^{-1}
              =: R_{p,s},                       0<=s<1.   (5)

To prove this first in finite volume, more generally activate each of a
finite family of linear constraints independently with odds t w_i,
where w_i>=0. Project onto the intersection of the active kernels.
Adding a constraint again deletes an orthogonal projection Delta_i.
For its probability a_i(t)=t w_i/(1+t w_i),
t a_i'=a_i(1-a_i). The nonidentical-coordinate version of the product
expansion in Theorem 1 therefore gives

    -t Q_t' >= Q_t-Q_t^2.

It follows that d[(Q_t^{-1}-I)/t]/dt>=0. At t=0 the limit is
sum_i w_i Delta_i(empty). For an edge equality constraint its empty
loss is the edge Laplacian divided by two; for a vertex zero constraint
it is delta_v delta_v^*. Set t=1, edge odds p/(1-p), and vertex odds
s/(1-s) to obtain (5). Exhausting both edges and vertex constraints
proves the infinite statement exactly as in Section 3.

At criticality, the quantity required for the stronger L2 conjecture is

    T_pc = lim_{s downarrow 0} (Q_{pc,0}-Q_{pc,s})/s        (6)

as increasing positive quadratic forms. For each finite cluster the
coefficient (1-(1-s)^m)/(s m) increases to 1. Critical finiteness then
identifies the limit with the full critical connectivity form.

Separate upper bounds in (5) DO NOT imply an upper bound on the
difference in (6). The following exact countercheck rules out that step
even in the smallest nontrivial finite graph. Take a single edge,
p=1/2 and s=1/4. Then

    Q_{p,0}=R_{p,0}=[[3/4,1/4],[1/4,3/4]],
    Q_{p,s}=[[33/64,9/64],[9/64,33/64]],
    R_{p,s}=[[33/56,9/56],[9/56,33/56]].

The diagonal of Q_{p,0}-Q_{p,s} is 15/64, whereas the diagonal of
R_{p,0}-R_{p,s} is 9/56. Since 15/64>9/56, the proposed difference
upper bound fails on delta_v. Infinitesimally the same failure reads
T_p(v,v)=1>(R_{p,0}^2)(v,v)=5/8.

This countercheck does not refute critical L2 boundedness or a more
refined argument using (1). It refutes the particular subtraction or
differentiation inference from the separate resolvent upper bounds.

## 5. Relation to the unresolved targets

The quotient environment gap from `quotient-environment-gap.md` used
only a finite FIID partition on the fixed Cayley graph, the original
Bernoulli action gap, and the cell boundary-to-mass comparison. Its proof
also applies to the heavy-tailed vertical FIID partition of
`exploration.md`, Section 4. Thus that environment gap cannot exclude
the existing obstruction to size-weighted dyadic summability.

The present product-noise calculation uses independence of the actual
retained edges. The vertical countermodel has ||Q||=1: its convolution
kernel along each Z fiber has nonnegative entries of row sum one, and
long interval test functions approach that row sum. It therefore cannot
satisfy (2) for the full nonamenable ambient Laplacian at any p>0.
This explicitly distinguishes the edge product law from an arbitrary
FIID partition. Nevertheless a bound on Q, including (2), does not by
the calculation here bound E[|C| P_omega]=T_pc. The ghost countercheck
locates the missing operator comparison precisely. The universal
dyadic estimate, critical L2 conjecture, and Benjamini--Schramm goal
remain OPEN.

## 6. Exact checks and Cairn scope

`scripts/replay_projection_resolvent.py` checks the projection merger
identity, the full matrix product-variance remainder, both inverse and
resolvent order bounds, the ghost bound, and the failed subtraction.
All calculations use exact rational arithmetic on MSI. The replay
passed 15 graph/parameter pairs (462 edge configurations), 387
higher-order product coefficients, and 144 edge/ghost configurations.
Results are `projection-resolvent-replay.json`.

The corresponding unchanged Cairn parser, linter and dependency-graph
check is recorded in `projection-resolvent-validation.json`. These are
finite checks and graph validation, not formal verification of the
infinite-dimensional proofs.

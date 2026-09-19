# Tapered curvature halos: a positive construction and an SL5 boundary floor

There is a genuine improvement over a sharp fixed-radius halo: averaging
nested word halos produces a small-trace positive contraction that is
almost central **in operator norm**. However, even in `SL_5(Z)` this does
not give a retained subspace whose normalized-HS boundary is controlled
by the curvature size. The obstruction below applies to every taper,
every radius schedule, and every spectral cutoff capturing the curvature.
It also survives `o(d)` padding. It is not a counterexample to flexible
stability: changing the relevant generator by its small error angle
corrects the example exactly.

## 1. A tapered positive halo really is almost central

Let `U_s`, for a finite symmetric generator alphabet `S`, be unitaries
on `C^d`; inverse symbols are evaluated as inverse unitaries. Let `P`
be a projection and define

```text
P_l=join_(|w|<=l) U(w) P U(w)^*,       l>=0.
```

The sequence is increasing, and free-word multiplication gives

```text
P_(l-1) <= U_s P_l U_s^* <= P_(l+1)       for l>=1,
0 <= U_s P_0 U_s^* <= P_1.
```

For a positive integer `L` put

```text
A_L=(1/L) sum_(l=0)^(L-1) P_l.
```

Then

```text
0<=A_L<=I,       A_L P=P,
tr(A_L)<=tr(P_(L-1))<=B_(L-1) tr(P),
||[A_L,U_s]||_op<=1/L                 for every s,         (TCH1)
```

where `B_l` is the number of words of length at most l. To prove the
last estimate, summing the preceding projection inequalities gives

```text
A_L-P_(L-1)/L <= U_s A_L U_s^*
                  <= A_L+(P_L-P_0)/L.
```

Both error terms are bounded between zero and `I/L`. The difference is
self-adjoint, so its operator norm is at most `1/L`.

Consequently, if `tr(P_j)->0`, choose `L_j->infinity` sufficiently slowly
that `B_(L_j)tr(P_j)->0`. Then `A_(L_j)` has vanishing trace, equals
the identity on the curvature support, and its operator-norm commutators
tend to zero. This construction needs no group relations, exactification,
or cohomological assumption.

Its limitations are equally explicit: `A_L` is a positive contraction,
not a projection. The matrices obtained by multiplying generators by
`I-A_L` are not unitaries. A claim about their boundary being small
*relative to a prescribed defect scale* needs an additional estimate.

## 2. Exact irreducible SL5 actors in unbounded dimensions

Fix a finite symmetric generating Kazhdan set `S` for `SL_5(Z)` and a
constant `kappa>0` in the convention

```text
dist(x,H^G)<=kappa^(-1) max_(s in S)||pi(s)x-x||.
```

There are exact irreducible finite-dimensional representations
`rho_j:SL_5(Z)->U(d_j)` with `d_j->infinity`. An explicit construction
uses the action of `SL_5(F_p)` on projective lines of `F_p^5`, pulled
back by reduction from `SL_5(Z)`.

Here are the elementary details. Reduction is onto because elementary
matrices generate the special linear group over a field and all their
coefficients lift to integers. The action on projective lines is doubly
transitive: send two independent vectors to representatives of any other
ordered pair of distinct lines, and correct the determinant by scaling
one of the remaining three basis vectors. Thus the permutation action
has exactly two orbits on ordered pairs of lines. Its complex commutant
has dimension two (matrices are constant on those pair orbits). The
constant functions form one trivial summand, so their orthogonal
complement is irreducible. Its dimension

```text
d_p=(p^5-1)/(p-1)-1
```

tends to infinity. This is a symbolic family, not a finite-prime search
or enumeration.

The group also has ordinary `H^2(G,H)=0` for every unitary Hilbert
representation. This follows from Bader--Sauer Theorem A on the
noninvariant part, and Theorem C plus the compact-dual formula on the
invariant part. The same source supplies property `(T)` here. See
[Bader--Sauer, arXiv:2308.06517v3, Theorems A and C and equation (1)](https://arxiv.org/html/2308.06517v3).
Thus the example below lies in the actual higher-cohomology arithmetic
class; it is not based on a rank-one or amenable replacement.

## 3. A tiny curvature angle on one vector

Start with a fixed finite presentation `<S|R>` of `SL_5(Z)` and adjoin
a redundant generator with its defining relation:

```text
G=<S,b | R,b=1> = SL_5(Z).
```

Choose a unit vector `xi_j` in the irreducible representation space,
let `P_j` be its rank-one projection, and take positive angles
`theta_j->0`. Define

```text
U_(s,j)=rho_j(s)                   for s in S,
U_(b,j)=I+(exp(i theta_j)-1)P_j.
```

The original actor relators are exact; only `b=1` has curvature. With
`gamma_j=|exp(i theta_j)-1|`, its normalized norms and support are

```text
delta_j=gamma_j/sqrt(d_j),
||U_(b,j)-I||_1=gamma_j/d_j=delta_j/sqrt(d_j),
tr(P_j)=1/d_j,
(U_(b,j)-I)(I-P_j)=0.                                  (TCH2)
```

Thus this is already in the concentrated residual sector produced by
the Hilbert-cohomology correction theorem. One may take
`theta_j=d_j^(-1/2)`, giving `delta_j~d_j^(-1)`, or make the angles
arbitrarily smaller without changing the geometry of the support.

The tuple itself has an exact same-dimension correction: replace
`U_(b,j)` by `I`, leaving the actor unchanged. Its correction cost is
exactly delta. The purpose of this example is to test support removal,
not to claim instability.

## 4. Every small taper capturing the curvature has a boundary floor

Let `A_j` be **any** positive contractions with

```text
tr(A_j)->0,
||(I-A_j)xi_j||->0.                                    (TCH3)
```

These hypotheses hold for the tapered halos in Section 1, for projections
containing `P_j`, and for sufficiently accurate spectral-cut support
removals. There is no restriction on how `A_j` is constructed.

Write `a_j=<xi_j,A_j xi_j>` and `t_j=tr(A_j)`. Irreducibility makes
the invariant vectors of the exact conjugation representation
`Ad(rho_j)` precisely the scalar matrices. The following normalized
matrix inequality retains the single prescribed vector:

```text
|a_j-t_j|
 =d_j |tr((P_j-I/d_j)(A_j-t_j I))|
 <=sqrt(d_j-1)||A_j-t_j I||_2.
```

Property `(T)` applied to this exact representation therefore gives

```text
max_(s in S)||[A_j,rho_j(s)]||_2
 >= kappa ||A_j-t_j I||_2
 >= kappa |a_j-t_j|/sqrt(d_j-1)
 = (kappa-o(1))/sqrt(d_j).                              (TCH4)
```

This applies to positive contractions before any spectral cutoff. It
also applies to every small projection capturing the curvature, so a
different threshold, a random threshold, or an arbitrarily long slowly
growing halo cannot evade it.

For the concrete choice `theta_j=d_j^(-1/2)`, the floor is larger than
the defining defect by order `sqrt(d_j)`. In particular no such taper
can have HS commutator boundary `o(delta_j)`, or even `O(delta_j)`.

The support-capture assumption is forced if the method seeks small
operator curvature on the complement. Indeed

```text
||(U_(b,j)-I)(I-A_j)||_op
 =gamma_j ||(I-A_j)xi_j||.
```

Requiring this to be `o(delta_j)` forces the rightmost vector norm to be
`o(1/sqrt(d_j))`, which is stronger than `(TCH3)`. Thus the method
cannot evade the boundary floor while retaining the intended off-support
operator estimate.

For a projection `Q_j`, its two off-diagonal unitary blocks have equal
HS mass, and

```text
||[Q_j,rho_j(s)]||_2^2
 =2||Q_j rho_j(s)(I-Q_j)||_2^2.
```

Hence the same floor, up to `sqrt(2)`, applies to the actual boundary
leakage that a polar reconnection must repair.

## 5. Padding does not erase this bound

Allow an enlarged space of dimension `D_j=d_j+m_j`, where `m_j=o(d_j)`,
and arbitrary unitary padded actor matrices

```text
rho_j(s) direct_sum Z_(s,j).
```

The auxiliary `Z_(s,j)` need not themselves satisfy group relations.
Let `V_j:C^(d_j)->C^(D_j)` be the original-summand inclusion. If
`0<=A_j<=I` has normalized trace tending to zero in dimension `D_j`
and nearly fixes `V_j xi_j`, put `T_j=V_j^*A_j V_j`. Then

```text
tr_(d_j)(T_j)<= (D_j/d_j)tr_(D_j)(A_j)->0,
<xi_j,T_j xi_j>->1.
```

Moreover

```text
[T_j,rho_j(s)]
 =V_j^*[A_j,rho_j(s) direct_sum Z_(s,j)]V_j,
||[T_j,rho_j(s)]||_(2,d_j)
 <=sqrt(D_j/d_j)
   ||[A_j,rho_j(s) direct_sum Z_(s,j)]||_(2,D_j).
```

Apply Section 4 to `T_j`. The padded boundary is still at least
`(kappa-o(1))/sqrt(d_j)`. This permits tapers mixing the original and
new coordinates; it is not restricted to block-diagonal tapers.

If the method also changes the padded actor generators by HS distance
at most `eta_j`, the commutator estimate changes by at most `2 eta_j`.
Thus lowering this boundary to `o(1/sqrt(d_j))` requires an actor
modification of at least `(kappa/2-o(1))/sqrt(d_j)`. That amount tends
to zero, so unrestricted flexible surgery remains possible. What fails
is obtaining the required boundary for free from concentration and
tapering, while retaining the initial actor or changing it only at its
much smaller curvature scale.

## 6. An arbitrary defect-only scale reset is still insufficient

The objection is not confined to insisting on the original delta. Let
`f:(0,1)->(0,infinity)` be **any** prescribed dimension-independent
reset modulus with `f(delta)->0` as `delta->0`. Choose the angles in
Section 3 so small that

```text
f(gamma_j/sqrt(d_j))<=1/d_j.
```

This is possible for each dimension because gamma tends continuously to
zero with the angle. The support geometry and the boundary lower bound
in `(TCH4)` are unchanged. Thus no taper capturing this curvature has
boundary bounded by `f(delta_j)`, despite already having trace-norm
curvature `o(delta_j)` and a vanishing-rank exact support.

This disproves a support-removal guarantee controlled solely by the
original defining defect, for every reset modulus tending to zero. It
does not disprove a reset that also depends on the support rank or on
the generator perturbation budget. Such a reset can be much larger than
delta and still tend to zero, but its iteration needs a cumulative
ledger, for example the orthogonal frozen-support theorem. Neither the
word-halo rank bound nor `(TCH1)` supplies exact subgroup-relator
compatibility for the reconnected generators.

## 7. The new quadratic-rank normal form changes the repair interface

The later result `two-kazhdan-correction-has-quadratic-rank-curvature`
uses the larger tangent space of sequences with
`delta_j||X_j||_op->0`. It removes the tiny-angle error energy used in
Sections 3--6. Those examples therefore do not refute that theorem or
demonstrate that its *output* necessarily retains the same support.
Here is the precise interface after applying the new theorem.

### Uniform preparation is available at each fixed tolerance

For each fixed `epsilon>0`, the new subsequence theorem implies constants
`C_epsilon<infinity` and `delta_0>0`, depending only on the presentation
and epsilon, such that every tuple with positive HS defining defect
`delta<delta_0` admits a tuple `V` and projection `P` satisfying

```text
max_s ||V_s-U_s||_2 <= C_epsilon delta,
tr(P)<=C_epsilon delta^2,
max_r (||(V(r)-I)(I-P)||_2+||(I-P)(V(r)-I)||_2)
 <=epsilon delta.                                     (TCH5)
```

Proof: otherwise, for each positive integer j choose an input with
`0<delta_j<1/j` for which no output has both bounds with constant j
and the displayed epsilon residual. Apply the quadratic-rank theorem
to that sequence. Its subsequence has finite generator-correction and
support-rank constants and eventually satisfies the epsilon estimate.
For sufficiently large indices j those constants are less than j,
contradicting the choice. Thus uniform fixed-epsilon preparation is not
an additional missing hypothesis. This argument makes no assertion that
one rank constant works while epsilon tends to zero.

### Block-normalizer rounding already proves the analytic repair step

Let `ell=max_(r in R)|r|`, taking `ell>=1`. Apply `(TCH5)` with
`epsilon=1/4`. Suppose, for this prepared tuple, one could find an
enlarged projection `R_0>=P` with

```text
tr(R_0)<=B delta^2,
max_s ||[R_0,V_s]||_2 <=eta delta,
eta=1/(4 ell).                                        (TCH6)
```

Let `Q_0=I-R_0`. For each generator independently, polar-round the two
square compressions `R_0 V_s R_0` and `Q_0 V_s Q_0` to unitaries on
their respective blocks. Their direct sum is a unitary `W_s` commuting
exactly with `R_0`. No actor representation or stability theorem is
being assumed in this construction.

Write `b_s=||R_0 V_s Q_0||_2`. The two off-diagonal blocks have equal
HS mass, so `||[R_0,V_s]||_2^2=2b_s^2`. On a square contraction,
polar completion costs at most its unitarity deficiency: for singular
values `0<=sigma<=1`, `(1-sigma)^2<=1-sigma^2`. Therefore

```text
||(W_s-V_s)Q_0||_2^2<=2b_s^2,
||W_s-V_s||_2^2<=4b_s^2,
||(W_s-V_s)Q_0||_2<=eta delta,
||W_s-V_s||_2<=sqrt(2) eta delta.                       (TCH7)
```

Now telescope a relator with prefixes evaluated in `V` and suffixes in
`W`. Every `W` suffix preserves `Q_0`, so every term is bounded by the
retained-column error in `(TCH7)`. Inverse generator letters obey the
same bound since `W_s` commutes with `Q_0`. Thus

```text
||(W(r)-V(r))Q_0||_2<=ell eta delta.
```

As `Q_0<=I-P`, `(TCH5)` gives

```text
||(W(r)-I)Q_0||_2<=delta/4+ell eta delta=delta/2.
```

Replacing the `R_0` block by the trivial representation makes the defining
defect at most `delta/2`. This proves the one-step implication without
circular use of a genuine actor. The entire missing geometric input is
the small-boundary enlarged support `(TCH6)`; small rank by itself only
gives `||[R_0,V_s]||_2<=sqrt(2B)delta`, whose constant does not provide
the needed contraction.

If `(TCH6)` were uniform with finite B, and earlier frozen blocks were
preserved, the orthogonal-support theorem would give the exact correction
bound

```text
max_s||rho(s)-U_s||_2
 <= [2(C_(1/4)+sqrt(2)/(4ell))+(4/sqrt(3))sqrt(B)] delta. (TCH8)
```

Here the smooth corrections sum geometrically and the cumulative frozen
rank is at most `(4B/3)delta^2`.

### Frozen blocks and normalization

Uniform preparation can be applied to the active complement of a frozen
trivial block. If its relative dimension is q, then its normalized defect
is `delta/sqrt(q)`. A smooth active correction of size
`C delta/sqrt(q)` has original-normalized size `C delta`. Crucially,
the quadratic rank estimate also cancels exactly:

```text
q B (delta/sqrt(q))^2 = B delta^2.
```

The same cancellation holds for the required boundary estimate. The
polar completions can be chosen to act as identity on every previously
frozen block. Thus no moving-basis or hidden normalization loss occurs.
Taking `(4B/3)delta^2<1/2` keeps the active fraction above one half, and
taking `sqrt(2)delta<delta_0` keeps all active inputs in the uniform
preparation range throughout the iteration.

### This universal no-padding interface is actually false for SL5

The endpoint in `(TCH8)` is **same-dimension** HS stability. It is
stronger than flexible stability. Becker--Lubotzky prove that every
infinite hyperlinear property-`(T)` group fails same-dimension normalized-HS
stability; see [Group stability and Property (T), arXiv:1809.00632v2](https://arxiv.org/abs/1809.00632v2).
Since `SL_5(Z)` is infinite, residually finite and Kazhdan, it lies in
that class.

Consequently there cannot be a universal preparation-and-enlargement
method satisfying `(TCH5)--(TCH6)` for this group with frozen blocks and
uniform constants. Uniform preparation `(TCH5)` is proved above, and
the polar and telescoping estimates are elementary, so the universal
no-padding support-repair conclusion is what fails. It should not be
listed as an unrefuted route to `SL_5(Z)` stability.

The live arithmetic interface must allow genuine dimension addition or
a dilation with a controlled corner, rather than only deleting subspaces
and replacing them by trivial representations inside the original
dimension. The existing frozen-support criterion is still a correct
conditional theorem, but applying it universally to this infinite
Kazhdan host would contradict the published instability theorem.

## Conclusion of this attack

Slow word halos do yield almost central positive support contractions in
operator norm. For an actual all-Hilbert-H2-vanishing arithmetic group,
however, every small taper retaining the curvature vector obeys a
Kazhdan boundary floor independent of the curvature angle. This survives
arbitrary cutoff schedules and sublinear padding and rules out every
defect-only boundary reset modulus.

The surviving affirmative target must use the error angles themselves,
or must modify actors with a separately controlled rank/error ledger and
exact two-cell compatibility. Hilbert H2 vanishing plus a tapered halo
does not yet supply that target or an exact endpoint. No non-hyperlinear
group is claimed here.

All constructions and estimates are analytic. No local code, build,
numerical job, commit, or branch was used.

# Liu Sections 3-5: block construction and uniformity audit

Date: 2026-09-20. This is a bounded mathematical audit of the supplied
56-page version of Jihao Liu, *Nonhyperlinear groups exist*, specifically
Proposition 3.1, Theorems 3.2, 4.3, 5.1, and Lemmas 5.2-5.4 (printed
pages 5-29). It is not a certification of the full paper, an independent
proof of nonhyperlinearity, or an instruction to promote Cairn status.

The mathematical results and construction audited in Sections 1-3 are
Jihao Liu's, from [*Nonhyperlinear groups exist*, September 20, 2026](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Proposition 3.1, Theorems 3.2, 4.3 and 5.1, and Lemmas 5.2-5.4.
Rechecking, restating, and encoding these arguments in Cairn does not
constitute a new discovery of those results or their proof mechanisms.

Local source examined:
`/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq/lit/liu-nonhyperlinear-2026-09-20.pdf`.
The PDF metadata records creation on September 20, 2026. Equations were
read from the PDF text; pages 18 and 23 were also rendered and inspected
to disambiguate the block Cholesky formulas and parameter square roots.
In particular, page 23 says `gamma = sqrt(t)`, not `gamma = t`.

Outcome: no concrete gap or circular use of commutant internality was
located in these sections. The local estimates below were rederived,
including their normalization and their dependence on the number of
outcomes. The important limits are uniform in ranks and outcome counts
but not uniform in the retained-trace tolerance. The imported finite von
Neumann algebra comparison statements were checked against primary
sources; their background proofs were not independently rebuilt here.
Sections 6-8, the group construction, and the final contradiction are
outside this audit.

## 1. Exact interfaces and quantifiers

Fix a nonprincipal ultrafilter `omega`, positive dimensions `d_n`, a fixed
integer `h >= 1`, and arbitrary coordinate unitaries `u_(j,n)` for
`1 <= j <= h`. Let

```text
M = prod_omega (M_(d_n), tr_(d_n)),
C = {u_1,...,u_h}' cap M,
T_n(x) = x/2 + (1/(4h)) sum_j (u_(j,n)x u_(j,n)*
                                      + u_(j,n)*x u_(j,n)),
E_n(x) = (1/(4h)) sum_j ||[u_(j,n),x]||_(2,d_n)^2.
```

The quotient gap assumption is

```text
< (I-T)xi,xi > >= a ||xi||_2^2
for xi in L2(M) orthogonal to L2(C), with one fixed a in (0,1).
```

This is a gap on the trace Hilbert space of the algebra ultraproduct.
It is not a gap on the entire Hilbert ultraproduct of the coordinate
Hilbert-Schmidt spaces. Unless a block denominator is explicitly stated,
all squared matrix and rectangular norms divide by the original `d_n`.

### Proposition 3.1

There is one sequence of powers `ell_n ->_omega infinity` such that
`Phi_n = T_n^(ell_n)` induces `E_C` on **every** uniformly
operator-norm-bounded sequence. For every coordinate sequence of unital
*-subalgebras `A_n`,

```text
[A_n]_omega = C iff ||Phi_n - E_(A_n)||_(infinity->2,n) ->_omega 0.
```

For a homomorphism from a finitely generated Kazhdan group, a displacement
constant `kappa` for the given list gives `a = kappa^2/(4h)`.

The quantifier order is `for each fixed coordinate sequence and specified
omega with gap a, there exists one sequence ell_n, for every bounded
witness sequence and every algebra sequence A_n`. The powers may depend
on the entire original unitary sequence and on the ultrafilter. The
proposition does not supply a universal power schedule determined only
by `a,h`, an effective schedule, or uniformity over different input
models. It does give the operator-unit-ball norm needed to handle
witnesses and candidate algebras selected after that one schedule.

### Theorem 3.2

Put `L = 36/a^2`. There exist projections `e_n` and positive numbers
`eta_n`, with `tr(1-e_n) ->_omega 0` and `eta_n ->_omega 0`, such that
for **every coordinate n and every projection p <= e_n** satisfying

```text
E_n(p) <= tr(p)/(4L),
```

there is a projection `f` in the same matrix algebra with

```text
||f-p||_2^2 <= L E_n(p),
tr(p)/4 <= tr(f) <= 9 tr(p)/4,
E_n(f) <= eta_n tr(f).
```

The choices `e_n,eta_n` precede the choice of `p`. There is no lower
bound on `tr(p)` and no assertion that `f <= e_n`.

### Theorem 4.3

For each fixed `h >= 1` and `epsilon > 0`, there is
`delta = delta(h,epsilon) > 0` such that for all `d,m >= 1`, all
unitaries `u_1,...,u_h`, and every POVM `a_1,...,a_m` with
`sum_i E_u(a_i) <= delta`, an `m`-outcome PVM `q_i` exists in the
**same** `M_d` with

```text
sum_i E_u(q_i) <= epsilon,
sum_i ||q_i-a_i||_2^2 <= 5000 sum_i tr(a_i-a_i^2) + epsilon.
```

Zero outcomes are permitted. There is no spectral-gap or group-relation
hypothesis. The purity deficit may have a fixed positive limit while the
output energy tends to zero. The modulus is existential, not effective.

### Lemma 5.2

For any finite list of projections `f_i`, put `S_i = sum_(k<=i) f_k`,
`D_i^(mu) = (I+mu S_i)^(-1)`, and
`B_i^(mu) = D_(i-1)^(mu)-D_i^(mu)`, with `mu > 0`. Then

```text
B_i^(mu) >= 0,                 rank B_i^(mu) <= rank f_i,
E_u(D_l^(mu)) <= mu sum_(i<=l) E_u(f_i),                (5.1)
E_u(D_m^(mu)) + sum_i E_u(B_i^(mu))
    <= 72 mu sum_i E_u(f_i),                          (5.2)
sum_i ||[u_j,D_(i-1)^(mu)] f_i||_2^2
    <= C_mu sum_i ||[u_j,f_i]||_2^2.                  (5.3)
```

`C_mu` is finite and depends only on `mu`. Under bounded total projection
trace and vanishing total energy, for **each fixed** continuous function
`psi` on `[0,infinity)` having a finite limit at infinity,

```text
sum_i ||[u_(j,n),psi(S_(i-1,n))] f_(i,n)||_2^2
    ->_omega 0.                                      (5.4)
```

There is no uniform assertion over functions with growing oscillation.

### Lemma 5.3

For every decreasing positive-contraction chain
`I=D_0 >= D_1 >= ... >= D_m >= 0`, set `B_i=D_(i-1)-D_i`.
For every fixed continuous `g:[0,1]->C` and `rho>0`, there is
`K_(g,rho)<infinity`, independent of dimensions, chain length and chain,
such that every projection `e` satisfies

```text
sum_i tr((I-e) g(D_(i-1)) B_i g(D_(i-1))* )
    <= 2 K_(g,rho) tr(I-e) + 2 rho^2.                 (5.9)
```

Consequently this sum tends to zero when `tr(I-e_n)->_omega 0`,
holding `g` fixed and taking `rho->0` after the ultralimit. The same
conclusion holds for positive summands dominated by a fixed multiple of
the displayed amplitudes. No bounded overlap of their support
projections is assumed.

### Lemma 5.4

Suppose `P_0,...,P_m` is a PVM and `w_1,...,w_h` are unitaries reducing
every `P_i`. For fixed `0 < theta <= 1` and numbers `xi_i >= 0`, assume

```text
E_w(q) >= theta tr(q)-xi_i
for every projection q <= P_i with rank q <= rank(P_i)/2,
for every i >= 1.                                    (5.11)
```

With `xi=sum_(i>=1) xi_i`, there are `R_i<=P_i`, `R_0=I-sum_(i>=1)R_i`,
and two unitaries `z_j^+,z_j^-` per original generator, all reducing the
new partition, such that

```text
tr(R_0)-tr(P_0) <= 8 xi/theta,
sum_(i>=1) E_w(R_i) <= xi/7,
sum_(j,+/-) ||z_j^+/- - w_j||_2^2 <= 16 h xi/7.
```

Every nonzero retained block has scalar gap `theta^2/64` for the
doubled list, using the block's normalized trace and energy denominator
`4(2h)=8h`. The defects are charged once per original block.

### Theorem 5.1

For every `epsilon>0`, there is `c=c(a,h,epsilon)>0` and coordinate
partitions `R_(0,n),...,R_(m_n,n)` together with unitaries `z_(j,n)^+/-`
in the original `M_(d_n)` such that they reduce the partition,

```text
sum_(j,+/-) ||z_(j,n)^+/- - u_(j,n)||_2^2 ->_omega 0,
lim_omega tr(R_(0,n)) <= epsilon,
```

and every nonzero retained block has scalar gap `c` for the doubled
list. Neither block count nor rank ratios are restricted. This theorem
does not assert a positive gap uniform as `epsilon->0`, nor a gap for
compressions of the unchanged original generators.

## 2. Dependency graph and the circularity check

```text
quotient spectral gap
   |-- Proposition 3.1: averaging lifts E_C uniformly
   `-- Theorem 3.2: common repair corner, relative all-projection bound

spectral coarea + finite-algebra projection comparison
   `-- Theorem 4.3: same-dimension, all-label equivariant POVM rounding

block Cholesky + resolvent identities
   `-- Lemma 5.2: total and localized covariance

monotone inverse identity + uniform function approximation
   `-- Lemma 5.3: sum of range leakages

finite pruning + Cheeger + two-unitary realization
   `-- Lemma 5.4: remove additive defects

Theorem 3.2 + Theorem 4.3 + Lemmas 5.2,5.3,5.4
   `-- Theorem 5.1: physical expanding blocks at fixed trace tolerance
         `-- Section 6 matching/internality (not audited here)
```

Theorem 3.2 uses the spectral estimates underlying Proposition 3.1; it
does not require an already internal commutant. The auxiliary commutant
in Theorem 4.3 is an arbitrary finite von Neumann algebra. A MASA is
chosen in that algebra, but no coordinate lift of that MASA is assumed.
Only one projection commuting with the already internal label algebra
is lifted by explicit pinching. Thus the argument does not assume the
Section 6 internality conclusion in order to construct its blocks.

## 3. Equation-level checks

### 3.1 Uniform averaging and all-rank projection repair

The norm transfer identity (3.3) is valid because coordinate maximizers
on the operator unit ball are themselves bounded representatives.
Conversely any quotient contraction has contraction representatives,
using singular-value clipping. It is therefore a supremum statement,
not merely convergence on a countable list. The descending sets in
(3.4) impose finitely many inequalities at each stage. Choosing the
largest available stage gives one averaging sequence valid for every
subsequently selected bounded witness.

The crucial repair step is (3.7)-(3.10). For fixed target `eta`, first
fix `K,zeta`. A maximum-rank bad projection `q` obeys

```text
eta zeta sqrt(tr(q)) <= delta_(k,n).
```

Remove the span of words of length at most `2k+2` applied to its range.
The removed trace is at most
`(2h+1)^(2k+2) delta_(k,n)^2/(eta^2 zeta^2)`.
For any projection `p` on its orthogonal complement, the word spans
of length `k+1` generated by `p` and `q` are orthogonal. Both
`D_n(v)` and `T_n^k D_n(v)` are supported on those spans. Their squared
Hilbert-Schmidt norms consequently add for `v=p+q`. If `p` were bad,
`p+q` would be a larger bad projection, a contradiction. This verifies
uniformity even at rank one; no division by an uncontrolled small
trace occurs.

The small-displacement alternative in (3.10) permits `f=p` directly.
Otherwise telescoping gives
`||T_n^K(p)-p||_2 <= (2/a)||D_n(p)||_2`, and positivity of `D_n` as a
Hilbert-space contraction gives `||D_n(p)||_2^2<=E_n(p)`.
The spectral cut estimate is valid without `p` commuting with the
average: in its eigenbasis the coefficient
`lambda^2(1-b)+(1-lambda)^2 b`, `0<=b<=1`, bounds the cut error with
factor 9. Thus the distance constant is `9*(2/a)^2=36/a^2`.
The rank bounds follow from distance at most half the input's 2-norm.
The coarea estimate (3.13), with
`r^K+zeta <= eta^2/576`, gives
`E_n(f) <= eta tr(p)/4 <= eta tr(f)`.

The final diagonalization uses only fixed-target constructions.
Outside its first ultrafilter set the choice `e_n=0` leaves only the
zero input, so the theorem's “every n” statement is also covered.

### 3.2 Rounding a POVM without spending purity on energy

The cuts in (4.1)-(4.3) satisfy total energy `<=4 sqrt(beta_n)`,
sum `S_n<=3I`, total cut distance `<=2v_n`, and
`||S_n-I||_2^2<=12v_n`. The overlap estimate uses positivity of
`tr(f_i f_k)`, not commutativity of the different cuts.

Adding the physical summand to their direct sum gives an auxiliary
dimension between `d_n` and `4d_n`. Hence the trace `Tr/d_n` and its
normalized trace define the same ultraproduct null ideal. Polar
completion of each compressed unitary has intertwining cost bounded
by the corresponding original projection commutator; summing gives
(4.5) with no factor `m_n`.

Inside the auxiliary commutant, the polar partial isometry `V` of the
cut column has small missing initial and final supports, as in (4.6).
Choose a MASA containing the **entire** internal label algebra
`L=[L_n]_omega`. Projection comparison replaces the complement of
the range by an equivalent projection in this MASA. Near-identity
conjugacy of the complements then gives `Z` in the commutant with
range commuting with `L` and `||Z-W||_2<=20 sqrt(v)`.

The two external statements used here have the necessary finite-algebra
scope: [Houdayer-Vaes, Lemma 2.1](https://arxiv.org/pdf/1203.1254)
places a finite-trace projection into a MASA by equivalence when the
restricted trace is semifinite; the restriction is finite here.
[Ioana, Lemma 2.2(1)](https://ems.press/content/serial-article-files/47873)
provides unitary conjugacy of equivalent finite projections with
2-norm displacement at most three times the distance of the projections.
Both statements were checked in primary-source PDFs on September 20,
2026. The proof uses them in the specified commutant corner, not merely
in the ambient matrix ultraproduct.

The subtle quantifier is in (4.8). If pinching an arbitrary representative
of the new range did not approximate it, choose a witnessing set of
scalar phases separately at each coordinate. That bounded phase sequence
is an element of `L`; it would fail to commute with the range. Thus
commutation with all of `L` gives simultaneous control over every
coordinate label, including growing label sets.

After pinching and spectral cutting, excess rank over `d_n` is `o(d_n)`.
Removing that rank inside label blocks permits a rectangular polar
extension from the physical space onto the entire retained range.
This is an explicit lift; it assumes no internality of the commutant.
Equation (4.10) sums commutators over orthogonal label blocks exactly.
Intertwining then controls the pulled-back partition's total energy.
The missing initial support may have positive trace; its class is
invariant, so its commutator still tends to zero.

The distance budget in (4.11) is
`(40+sqrt(12)+sqrt(2))^2 v < 5000v`. The contradiction argument fixes
`h,epsilon` before choosing arbitrary dimensions and outcome counts.
It therefore proves the stated two-parameter uniform modulus.

### 3.3 Block Cholesky covariance: Lemma 5.2

The rectangular inverse map
`Q_mu(Z)=(I+mu Z*Z)^(-1)` is `sqrt(mu)`-Lipschitz in Hilbert-Schmidt
norm: differentiate and use
`||Z Q_mu(Z)||_op <= 1/(2 sqrt(mu))`. This yields (5.1) from the
inclusion-column defect (5.5) at every prefix, without bounding `||S_i||`.

The main check is the map `J(Z)=C(Z)^(-1) Z`, where
`I+mu ZZ*=C C*` has positive diagonal blocks and is block lower
triangular. Along a differentiable path,

```text
Xi=C^(-1) dot(C),
Upsilon=C^(-1) mu(dot(Z)Z*+Z dot(Z)*) C^(-*),
Xi+Xi*=Upsilon.
```

On a diagonal block with positive eigenvalues `g_r`,
`Xi_(rs)=g_s/(g_r+g_s) Upsilon_(rs)`. Strictly lower blocks equal the
corresponding blocks of `Upsilon`; strictly upper blocks vanish.
Therefore `||Xi||_2<=||Upsilon||_2`, independently of block number.
Also `||C^(-1)||<=1` and
`mu J J*=I-C^(-1)C^(-*)<=I`. These give
`||Upsilon||_2<=2 sqrt(mu)||dot(Z)||_2` and
`||dot(J)||_2<=3||dot(Z)||_2`. There is no unbounded triangular
projection estimate hidden here: the norm used is Hilbert-Schmidt.

Uniqueness of the positive-diagonal factor gives covariance under
block-diagonal unitary changes on the left and arbitrary unitary
changes on the right. The explicit row factors (5.6) give

```text
B_i = mu D_(i-1) F_i* (I+mu F_i D_(i-1) F_i*)^(-1)
                     F_i D_(i-1) = W_i* W_i.
```

Hence `W*W=I-D_m<=I`; this contraction bound is what permits summing
the commutator product expansions in (5.2).

For (5.3), `W_i F_i*=g_mu(H_i)`, where
`g_mu(x)=sqrt(mu)x/sqrt(1+mu x)` and `0<=H_i<=I`.
Its derivative is bounded below by
`ell_mu=sqrt(mu)/(1+mu)^(3/2)>0`. Entrywise divided-difference
comparison therefore controls commutators with `H_i` and with
`C_ii=(I+mu H_i)^(1/2)`. Recovering `D_(i-1)F_i*` from `W_i* C_ii`
proves (5.3). An admissible paper constant is

```text
M_mu = mu^2(9mu+1)/(2 ell_mu^2),
C_mu = 36(1+mu)+4 M_mu/mu+2.
```

To obtain (5.4), approximate a fixed function uniformly by finite
linear combinations of resolvents and constants. The approximation
error, summed after right multiplication by `f_i`, is bounded by
`4 rho^2 sum_i tr(f_i)`. Bounded total trace, not a bound on the number
of projections or on their sum's operator norm, is the required input.

### 3.4 Range leakage: Lemma 5.3

With `A=D_(i-1)+sI` and `B=B_i`, the noncommutative inverse identity is

```text
(A-B)^(-1)-A^(-1)-A^(-1) B A^(-1)
   = A^(-1) B (A-B)^(-1) B A^(-1) >= 0.
```

The order of factors is essential and is correct. Telescoping gives
`sum_i (D_(i-1)+sI)^(-1) B_i (D_(i-1)+sI)^(-1) <= s^(-1) I`.
Triangle inequality in the direct sum of amplitudes gives the analogous
bound for a finite resolvent combination. Uniform approximation of `g`
then costs `rho^2 sum_i tr(B_i)<=rho^2`, proving (5.9).

This is stronger than a small leakage bound for each individual range:
it controls their **sum** although the ranges can overlap. The order
of limits is indispensable: `g,rho` are fixed before the ultralimit,
and only then does `rho` tend to zero.

### 3.5 Defect pruning and doubling: Lemma 5.4

Discard a whole block if `xi_i>theta tr(P_i)/8`. In a remaining block,
remove any projection of at most half the current rank whose compressed
energy is below `(theta/8)tr(p)`. Entries crossing the accumulated removed
set into its remainder are charged to disjoint earlier cuts, giving
(5.13). At a hypothetical first crossing of one quarter of the original
trace, the accumulated trace is less than five eighths. Applying the
original all-test inequality to the smaller of the removed set and its
complement contradicts (5.13). Thus the removed set stays eligible for
the original inequality and has trace at most `8xi_i/(7theta)`;
its boundary is at most `xi_i/7`.

On a retained block, the compressed matrices are contractions. The
layer-cake argument uses small-support spectral projections and row and
column square sums bounded by one; this gives `Q(y)>=kappa^2 tr(y^2)`
with `kappa=theta/8`. Median splitting handles self-adjoint trace-zero
matrices. The symmetrized commutator form preserves adjoints, so real and
imaginary parts extend the bound to arbitrary trace-zero matrices.

For a compression `a=v|a|`, the two unitaries
`v(|a| +/- i sqrt(I-|a|^2))` have average exactly `a`. Convexity for
both `a` and `a*` transfers the contraction gap to the doubled list.
Their squared edit cost is twice the pinching leakage per sign.
Summing block boundaries gives the stated `16h xi/7` cost. The constants
`theta^2/64` and `4(2h)=8h` are consistent.

### 3.6 Selection, coverage, and return of every test: Theorem 5.1

For a fixed `0<t<=1/256`, the relevant choices are

```text
L=36/a^2, beta=t/(4L), gamma=sqrt(t), lambda=t^(-1),
k_t=lambda/(1+lambda) * (1-2sqrt(t))^2,
sigma=gamma/(lambda(1-gamma)), A_*=(1+t)/k_t.
```

The selection test includes the actual repair-corner leakage:
`E_n(p)+3tr(p(I-e_n))<beta tr(p)`. Principal-angle cutting into `e_n`
costs at most twice this leakage in squared distance. Theorem 3.2 then
gives the original-space repair (5.18),

```text
||f-p||_2^2 < t tr(p),
(1-t)rank p < rank f < (1+t)rank p,
E_n(f)<=eta_n tr(f).
```

Choose each seed `p_i` with minimum positive rank **inside its chosen
high-density window** `b_i`. A minimum exists because ranks range over
finitely many integers; compactness of the strict sublevel set is not
needed. Its resolvent decrement has trace at least `k_t tr(p_i)`.
Since decrements telescope to at most `I`, recursion terminates in at
most `d_n/k_t` steps and supplies (5.21): bounded total seed trace and
vanishing total repaired energy. The final window has vanishing trace
by failure of the same test; the static prefix bound is uniform over
the adaptively selected windows.

Coverage is not inferred from bounded seed trace alone. The second
resolvent scale `mu=1`, the determinant identity, and (5.23) give
`tr log(I+S_m)>=A_n log(2)-b_t`. Jensen gives the upper bound
`log(1+A_n)`. Comparing their derivatives above `A_n=1` yields
`A_n<=1+v_t`. The scalar function `x-1-log(x)` bounds the mass of
`S_m<1/2`. Together with the large scale `lambda`, this proves the
remainder bound (5.26) and purity bound (5.28). All constants are fixed
functions of `t`; the full POVM has variance at most `2q_t` in the limit.

Theorem 4.3 rounds its effects in the original dimension with vanishing
total energy, using a diagonal sequence of **fixed** tolerances. The
identity (5.31) charges total label mismatch by `(V_n+H_n)/2`.
The contractions `Y_i=g(D_(i-1))B_i Q_i` have mutually orthogonal
right supports but generally overlapping left supports. Their left
supports lie in the **original** windows `b_i` because of the support
chosen for `g`. Lemma 5.2 controls the summed commutator of the varying
functions `g(D_(i-1))` after multiplication by their own seed projections;
an individual-prefix estimate alone would not suffice for (5.33).

One common spectral threshold in `[1/3,1/2]` gives orthogonal physical
supports `P_i<=Q_i` and vanishing summed energy. On those supports the
polar parts `V_i` satisfy `V_i*V_i=P_i`, `Pi_i=V_iV_i*<=b_i`, and
`sum_i E_n(V_i)->0`. Most importantly,

```text
Pi_i <= 3 g(D_(i-1)) B_i g(D_(i-1)),
sum_i tr(Pi_i(I-e_n)) ->_omega 0.                     (5.38)
```

The second statement follows from Lemma 5.3 with this **fixed** `g`.
The sets `b_i` themselves are not claimed to have summable leakage.

After pinching the generators to the physical `P_i`, let `w_j` be their
polar-completed unitaries. Every small projection `q<=P_i` transports
to `y=V_i q V_i*<=b_i`. Its rank is unchanged and strictly smaller than
`rank(p_i)` because
`rank(P_i)<=rank(f_i)<(1+t)rank(p_i)<2rank(p_i)`.
The actual minimum-rank rule, with its leakage penalty, therefore applies
to `y`, giving (5.41). This addresses the tested-corner obstruction
recorded in the September 8 Cairn artifact.

The positive defect matrices from the two intertwining errors and the
leakage have total trace tending to zero, by orthogonality of the
**initial** projections and (5.38). The exact commutator identity in
Step 6 then gives simultaneously for all eligible `q`

```text
E_w(q) >= (beta/2)tr(q)-xi_i,
xi_i=2tr(Z_i)+(3/2)tr(H_i), sum_i xi_i ->_omega 0.
```

Lemma 5.4 applies with the already fixed `theta=beta/2`. Its total
discarded trace `16xi_n/beta` tends to zero. Thus no nonvanishing
`boundary/gap` term survives this application.

Finally `sigma=O(t^(3/2))`, `b_t,v_t,s_t,q_t=O(t)`, and
`F(t)=2((5002+4/gamma)q_t+s_t)=O(sqrt(t))`. Choose **one fixed t**
so that `F(t)<=epsilon`; then `c=beta^2/256>0` is fixed while all
coordinate limits are taken. Sending `t=t_n->0` inside these estimates
would require a new argument and is not asserted.

## 4. Reusable Cairn material and Liu's additional construction

The canonical files and their cited September 8 artifacts were searched
and read before proposing new interfaces. Relevant existing claims are:

| Existing claim | What can actually be reused | What it does not supply |
| --- | --- | --- |
| `low-energy-povms-yield-flexible-projection-cuts` | Outcome-count-free coarea, `sum f_i<=3I`, polar completion, direct-sum intertwining and rank comparison | Same-dimension orthogonalization with energy independent of fixed purity deficit |
| `outcome-count-free-subpovm-completion` | Dimension- and outcome-independent distance rounding for supplied effects | Vanishing equivariant energy when purity has a fixed positive limit |
| `quantum-expansion-transports-across-leaking-corners` | Return a test to a tested corner and pay explicit, aggregate leakage | Selection of the windows, summability for the actual varying ranges in (5.38), or closure of a `boundary/gap` budget |
| `reflected-corners-control-defective-quantum-variance` | Defective projection expansion gives bounded-observable variance with exterior boundary accounted for | Finite pruning to defect-free scalar gaps on every surviving block |
| `soft-projection-cones-have-low-energy-residuals` | Unbounded positive projection sums can be handled; residual energy and dual gain are controlled | Expansion-compatible selection, the two resolvent scales, or the block Cholesky localized covariance estimate |
| `hs-block-gap-iff-liftable-masa-of-actor-commutant` | The bounded, summed downstream interface once a liftable masa is available | Construction of that masa or the off-diagonal matching needed for full internality |

The September 8 `quantum-corner-expansion-transport` artifact already
returns projections to their tested corners and charges leakage. Its
Section 4 explicitly identifies the nonvanishing `boundary/gap` ratio.
It would be inaccurate to describe corner return or soft overlapping
selection, by themselves, as newly supplied by Liu relative to this
corpus. The additional assembly audited here is the coupled
leakage-penalized minimum-rank rule, uniform relative repair, resolvent
increment covariance, label-preserving physical rounding, and summable
leakage of the actual transported ranges.

No complete version of this assembly was found in the inspected
canonical nodes or the three supplied September 8 artifacts. This is a
bounded repository comparison, not a priority or provenance judgment.

## 5. Shared claim interfaces and routes

The names below were synchronized with the integration editor's canonical
nodes after their creation. This artifact did not create those nodes.
Every claim id is at most 58 characters. Statements should retain exactly
the quantifiers in Section 1.

| Claim id | Length | Statement / sufficient route inputs |
| --- | ---: | --- |
| `quotient-gap-gives-uniform-relative-projection-repair` | 53 | OPEN audit leaf: Theorem 3.2, with its exact all-rank quantifiers above. Its proposed proof uses uniform witness transfer, word-neighborhood packing, and coarea, with no internality prerequisite. |
| `low-energy-povms-round-equivariantly-in-place` | 45 | OPEN audit leaf: Theorem 4.3. Existing flexible-cut material supplies the initial cut construction; the remaining proof must include finite-algebra projection comparison and full-label pinching. |
| `resolvent-assembly-controls-covariance-and-leakage` | 50 | OPEN audit leaf combining all of Lemma 5.2 and Lemma 5.3. The two exact statements above are a conjunction: summed/localized covariance for projection-sum resolvents, and fixed-continuous-function leakage for arbitrary decreasing positive-contraction chains. |
| `defective-block-expansion-prunes-to-doubled-gaps` | 48 | OPEN audit leaf: Lemma 5.4 with all-test hypotheses, ambient defects, and doubled-list output. Its proposed proof is finite pruning, Cheeger, and two-unitary realization. |
| `quotient-gap-gives-large-scalar-expanding-blocks` | 48 | Conditional assembly target: Theorem 5.1. Its route requires the four preceding leaves and supplies the minimum-rank/resolvent/coverage/transport argument of Section 3.6. |
| `quotient-gap-expectations-have-coordinate-lifts` | 47 | Separate interface for Liu's Proposition 3.1, needed for Section 6 expectation exhaustion. The integration editor supplied `quotient-gap-expectation-lift-proof` as an independent verification and restatement of Liu's argument, not a novel proof. Preserve the fixed-model quantifier order stated above. It is not an extra prerequisite of the Theorem 5.1 assembly when the relative-repair leaf already contains its full statement. |

For the current integration, keep the four long analytic leaves OPEN
and attach this audit as evidence. No no-premise literature imports of
those leaves are proposed. The expectation-lift route records an
independent verification of Liu's Proposition 3.1, following Liu's
witness-transfer identity, diagonal construction and algebra criterion.
It is not a claim of a new theorem or proof. The steps were checked
against the exact interface here. Normalize the
supplied gap to a number in `(0,1)` before setting `r=1-a`.

A route with `requires: []` asserts a complete proof; “the paper says
so” plus this bounded audit must not silently acquire that meaning.
The conditional Theorem 5.1 route makes a separate, reviewable claim:
the four precisely stated interfaces suffice by the assembly checked
in Section 3.6. The expectation-lift claim remains separately visible
for the Section 6 consumer.

Do **not** route Theorem 5.1 directly to
`hs-one-level-expander-block-decomposition`: the old claim asks for a
gap for compressed original generators with one positive constant as
discarded trace goes to zero. Theorem 5.1 permits two perturbed copies
and a gap depending on a fixed discarded-trace tolerance. Tiny-trace
blocks prevent passing a normalized scalar gap through an arbitrary
ambient 2-norm perturbation.

Similarly, block-scalar expansion alone does not identify off-diagonal
intertwiners, build coherent multiplicity matrix units, or exhaust the
whole relative commutant. A route from the proposed expanding-block
claim to Kazhdan commutant internality needs the separate Section 6 matching and
expectation-exhaustion results. The existing
`rank-one-lift-perturbation-gap-no-go` remains relevant to overstrong
translations into the old one-level claim.

## 6. Checked versus unresolved

Checked here: the algebraic identities and inequalities listed in
Section 3, the fixed-before-limit parameter order, the mechanisms for
uniformity in ranks and outcome counts, the exact comparison with the
specified earlier Cairn results, and the applicability of the two
primary-source projection-comparison statements.

Not independently reconstructed here: the general finite von Neumann
algebra machinery behind those comparison theorems, foundational
tracial-ultraproduct facts, or every result in Sections 6-8. No numerical
experiments, Lean proof, automated theorem verification, or clean
whole-repository Cairn build is claimed. This artifact introduces no
canonical nodes and changes no computed research statuses.

No real gap in the audited chain was identified. The open audit boundary
is the rest of the claimed theorem, rather than an asserted missing
step in Sections 3-5. The conclusions available for immediate careful
reuse are the finite and ultraproduct analytic interfaces stated above,
with their hypotheses and tolerance dependence intact.

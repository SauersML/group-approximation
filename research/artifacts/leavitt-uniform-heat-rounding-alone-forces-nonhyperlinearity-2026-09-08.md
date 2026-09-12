# Uniform heat rounding alone would force nonhyperlinearity of H

2026-09-08. Written arguments, independently audited. No computation,
build, job, or new Lean verification. The rounding premise below is
unproved, so this does not determine hyperlinearity of H.

The separate hypothesis concerning the center of a chosen embedding
can be removed from the conditional program. The two inputs are
[the full heat-commutant identification](leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md)
and [the native central-height theorem and generation identity](leavitt-central-height-and-coordinate-swap-gap-2026-09-08.md).
The latter now proves that a uniformly rounded native L-heat produces
a nonzero trace-zero element of the center of the full H-commutant.

## 1. The sufficient rounding premise

Fix an isomorphism theta:H->L, where L is the native rank-three
corner subgroup. Choose a finite symmetric generating word list S of
H such that theta(S) is a generating list of L containing the native
root ell=x_23(1). Fix a Kazhdan SOS certificate and its transported
certificate for these lists. All inverse spellings are paired.

Consider the following sequential rounding property for S:

```text
(R) For every full canonical matrix microstate sequence V_n of H,
    and every t_n -> infinity with epsilon_n t_n -> 0,
    there are unital finite-dimensional algebras B_n subset M_(d_n)
    such that ||exp(-t_n A_n)-E_(B_n)||_(infinity->2) -> 0.
```

Here A_n=I-|S|^(-1) sum_s Ad(V_(n,s)), and epsilon_n bounds the
finitely many word-identification defects in the fixed SOS certificate.
The error norm is uniform on the whole operator unit ball. One may
increase epsilon_n to bound further fixed relation rows when choosing
the heat times. Property (R) is not asserted here.

The time quantifier has an equivalent weaker formulation: for every
full canonical microstate sequence, it suffices that **some** admissible
time sequence admits rounding. The
[admissible-time comparison](leavitt-poissonization-and-admissible-time-rounding-equivalence-2026-09-08.md)
shows that all admissible heat times for the same model have vanishing
uniform difference, so the same rounded algebras then work for every
admissible time. One prescribed admissible logarithmic time also gives
an equivalent premise. This does not remove the universal quantifier
over microstate sequences.

**Conditional theorem.** If (R) holds, H is not hyperlinear.

In particular, a dimension-independent rounding theorem for all
self-adjoint bistochastic UCP maps that are nearly idempotent in
infinity->2 norm would imply nonhyperlinearity of this same H. The
previous heat estimates would supply its near-idempotence hypothesis.
No independent factorial-commutant embedding premise is needed.

## 2. One rounded global heat permits scalar-commutant selection

We first prove a general selection statement for a countable ICC
property-(T) group G. Suppose a canonical microstate sequence V_n
admits rounded **global G-heat** maps

```text
T_n(t_n)=exp(-t_n A_n),
eta_n=||T_n(t_n)-E_(B_n)||_(infinity->2) -> 0,
t_n -> infinity,       epsilon_n t_n -> 0.          (1)
```

Then there is another canonical microstate sequence of G whose
embedding into its tracial matrix ultraproduct has scalar full
G-relative commutant. We prove the selection, rather than assume an
embedding theorem.

### Exact commutation with the rounded algebra

The SOS heat-energy estimate supplies numbers beta_(n,s)->0 with

```text
sup_(||x||_op<=1) ||[V_(n,s),T_n(t_n)x]||_2 <= beta_(n,s).
```

For a unitary b in B_n, transfer through (1) to get
`||[V_(n,s),b]||_2<=beta_(n,s)+2eta_n`. Haar averaging over
the unitary group of B_n gives

```text
dist_2(V_(n,s),B_n') <= (beta_(n,s)+2eta_n)/sqrt(2).
```

If E is a trace-preserving expectation, V a unitary and X=E(V),
a unitary polar completion W of X within the range algebra satisfies

```text
||V-W||_2^2 = 2-2 tau(|X|)
            <= 2-2||X||_2^2 = 2||V-X||_2^2.
```

Apply this with E=E_(B_n') and pair the inverse choices. There are
unitaries W_(n,s) in B_n' with

```text
gamma_n := max_s ||V_(n,s)-W_(n,s)||_2 -> 0.          (2)
```

These corrected tuples are still full canonical microstates by
fixed-word telescoping. Their group relations remain approximate;
no repair to exact group representations is claimed.

### Slower heat times preserve the rounded algebra

For 0<tau<=t_n and a contraction x, the integrated energy estimate gives

```text
||(T_n(tau)-T_n(t_n))x||_2^2
 <= (2/kappa) exp(-2 kappa tau)
    +(2 C epsilon_n/kappa)(t_n-tau).                (3)
```

Indeed the left side is bounded by the decrease of squared L2 norm
between the two times; integrate the SOS energy estimate over that
interval. Thus any tau_n<=t_n with tau_n->infinity still gives
`||T_n(tau_n)-E_(B_n)||_(infinity->2)->0`.

Let T'_n be the heat for W_(n,s). The Duhamel formula and the L2 and
operator-norm contractions of both heat semigroups give

```text
||T'_n(tau)-T_n(tau)||_(infinity->2) <= 2 tau gamma_n. (4)
```

Fix an enumeration of all true relation words over S, with the
fixed SOS rows first. Choose integers J_n->infinity and times
tau_n->infinity, tau_n<=t_n, slowly enough that tau_n gamma_n->0
and tau_n squared times the sum of squared defects of the first
J_n relation words for W_n tends to zero. This is possible since
every fixed word defect tends to zero. A diagonal choice first makes
the unscaled finite sum tend to zero, then chooses tau_n->infinity
below t_n and below the corresponding inverse-error bounds.

Equations (1)--(4) yield

```text
xi_n=||T'_n(tau_n)-E_(B_n)||_(infinity->2) -> 0.       (5)
```

### The component estimates average with physical trace

Write the represented finite algebra and the corrected tuple as

```text
B_n = direct_sum_i (M_(a_(n,i)) tensor I_(b_(n,i))),
W_(n,s) = direct_sum_i (I_(a_(n,i)) tensor W_(n,i,s)),
lambda_(n,i)=a_(n,i)b_(n,i)/d_n.
```

Let T_(n,i) be the adjoint heat of the tuple W_(n,i,s), using
normalized trace on M_(b_(n,i)), and put

```text
xi_(n,i)=||T_(n,i)(tau_n)-E_scalar||_(infinity->2).
```

Block-diagonal contractions with independently chosen inputs
I_(a_(n,i)) tensor x_i show that

```text
sum_i lambda_(n,i) xi_(n,i)^2 <= xi_n^2.             (6)
```

The corrected tuple commutes with B_n exactly, so both maps preserve
these diagonal blocks. Each block heat acts as identity tensor
T_(n,i), and its expectation as identity tensor E_scalar. Every
fixed relation's squared normalized defect likewise averages with
the weights lambda_(n,i).

The canonical trace also concentrates in this mean-square sense:
for every nonidentity g in G,

```text
sum_i lambda_(n,i) |tr_(b_(n,i))(W_(n,i,g))|^2 -> 0. (7)
```

To prove (7), choose M distinct conjugates h_j g h_j^(-1), using
the ICC assumption, and form the literal matrix average

```text
Z_n=(1/M) sum_(j=1)^M W_(n,h_j) W_(n,g) W_(n,h_j)^*.
```

In every component the trace of this average equals the trace of
W_(n,i,g) exactly. Cauchy--Schwarz in each component bounds the
left side of (7) by ||Z_n||_2^2. Global canonicality gives
`||Z_n||_2^2 -> 1/M`, since distinct conjugates are orthogonal in
canonical trace. Let M grow after taking the limit in n. This proves
(7) without assuming componentwise canonical traces in advance.

### Selecting the component and identifying its full commutant

Keep the relation prefix of length J_n chosen with the heat times.
Fix an enumeration of the nonidentity elements of G and representing
words. Independently choose a prefix of length K_n->infinity slowly
enough, using (7), that its sum of weighted squared trace errors tends
to zero. Then the weighted mean of the following nonnegative
component cost tends to zero:

```text
xi_(n,i)^2
+ tau_n^2 sum_(listed relations r) ||W_(n,i,r)-I||_2^2
+ sum_(listed nonidentity g) |tr(W_(n,i,g))|^2.       (8)
```

This follows from (6), (7), the diagonal time choice, and the
weighted averaging of relation defects. Pick a component i_n whose
cost is no greater than the weighted mean. Its tuples are full
canonical G-microstates. Their heat maps at tau_n converge uniformly
to scalar expectation, and their fixed SOS-row defects satisfy

```text
epsilon_selected,n tau_n -> 0.                     (9)
```

The time penalty in (8) is essential: uniform scalar heat convergence
at arbitrarily long times alone would not control slowly commuting
bounded matrix sequences. With (9), the full heat-commutant
identification applies and gives

```text
pi_selected(G)' intersect product_omega M_(b_(n,i_n)) = C1. (10)
```

This proves the selection statement. In particular, scalarity refers
to the entire external commutant in this matrix ultraproduct, not
merely to the finite-coordinate commutants or the represented group
factor.

## 3. Applying the rounding premise twice to the same H

Suppose H were hyperlinear and (R) held. Start with canonical H
microstates and choose an admissible global heat time. The first use
of (R) supplies (1). H is ICC, since it is infinite simple, so the
selection theorem gives canonical microstates phi_n of H with scalar
full global commutant in their matrix ultraproduct M.

Now precompose these selected microstates with theta:H->L. The
result is another full canonical microstate sequence of H. Its heat
on S is exactly the native L-heat of phi_n on theta(S). Choose heat
times slow enough to control both the transported SOS rows and the
fixed native compressor rows. The second use of (R) supplies uniform
rounding for those native L-heat maps, in the same selected matrix
sequence.

The native central-height theorem then supplies a self-adjoint
element z with

```text
z in Z(phi(H)' intersect M),
tau(z)=0,           ||z||_2>=1/8.                   (11)
```

Here membership in the whole-group commutant uses the proved native
identity H=<L,uKu^(-1)>: the height is central in the L-commutant,
so it commutes with K, and it commutes with u by the overlap-flow
estimate. Equation (11) contradicts scalarity in (10).

This proves the conditional theorem. Its two uses of rounding have
different roles, and the second is not silently inferred from the
first rounded sequence. Universal property (R) supplies it after
selection and restriction to the isomorphic native subgroup.

## 4. The remaining question

The unproved input is now (R), or a suitable theorem that supplies
these two instances of it. No separate control of trace distortion,
central block count, purely atomic center, or factorial embedding
selection is required in this conditional route.

Equivalently, if H is hyperlinear, property (R) must fail for some
canonical H-microstate sequence and admissible Kazhdan heat times.
That is a conditional obstruction to heat rounding, not an existing
counterexample: canonical microstates of H have not been constructed.
Neither branch of the original hyperlinearity question is proved.

## 5. Relation to the published Kazhdan commutant problem

[Alekseev--Thom, Open Problem 6.2(a)](https://arxiv.org/html/2608.05362v1#S6)
asks whether a Kazhdan-group relative commutant in a tracial matrix
ultraproduct can be written as an ultraproduct of finite-dimensional
coordinate subalgebras, allowing replacement of d_n by m_n with
`m_n/d_n->omega 1`. Part (b) additionally asks for generator lifts
whose exact centralizers realize those algebras. We use only (a).

For a fixed canonical H model and free ultrafilter omega, part (a)
for its embedding is equivalent to the existence of uniform heat
rounding along omega. Here and below the dimension identification is
the one induced by compression or adjoining a corner of vanishing
normalized trace, as in the stated problem.

To see this first in unchanged dimensions, let

```text
D=pi(H)' intersect product_omega M_(d_n),
P_n=exp(-t_n A_n),
t_n->infinity,             epsilon_n t_n->0.
```

The heat calculation identifies the coordinate map induced by P_n
with E_D. If `D=product_omega B_n`, the maps E_(B_n) also induce E_D:
their induced map is normal, trace preserving, fixes D, and has range
D. Uniqueness of the trace-preserving expectation identifies the two
maps. Equality for all bounded input sequences then gives

```text
lim_omega ||P_n-E_(B_n)||_(infinity->2)=0.             (12)
```

Indeed, a failure of (12) supplies a contraction witness x_n at each
index in an omega-large set, contradicting equality of the two induced
maps. Conversely (12) makes their induced expectations equal and
therefore identifies their ranges. This step uses uniformity on the
whole operator unit ball; equality on selected fixed words would not
suffice.

Negligible dimension changes do not weaken the conclusion here. If
`m_n>=d_n`, identify M_(d_n) with a rank-d_n corner p_n of M_(m_n).
The compressed coordinate maps

```text
F_n(x)=p_n E_(B_n)(x) p_n,       x in p_n M_(m_n) p_n,
```

induce the transported expectation E_D. The same witness argument
gives `||P_n-F_n||_(infinity->2)->omega 0`. The
[exact-expectation corner theorem, section 10](leavitt-kazhdan-heat-rounding-boundary-and-factorial-center-countermodel-2026-09-08.md)
rounds F_n to an expectation onto an algebra in the original corner,
at error at most `25((m_n-d_n)/m_n)^(1/4)`. Thus (12) follows in
the original dimensions. If `m_n<d_n`, embed B_n in a rank-m_n corner
of M_(d_n) and adjoin the scalar algebra on its complement. The
resulting exact expectations induce E_D because the complement has
vanishing trace, and the witness argument again gives (12). Treat
the two index sets separately. If the coordinate algebras initially
have units different from the ambient units, their missing corners
have trace tending to zero, since their ultraproduct contains 1;
adjoining scalars on those corners first makes them unital.

Finally, a positive answer to 6.2(a) for every canonical embedding of
this same H implies the ordinary sequential property (R). Otherwise
some canonical model has an admissible heat sequence and a subsequence
on which the distance to every algebra expectation is at least a
fixed positive constant. Reindex that subsequence and take a free
ultrafilter. The preceding implication contradicts this lower bound.

Combining with sections 2--3 proves the conditional consequence

```text
6.2(a) holds for every canonical embedding of H
    => H is not hyperlinear.

H is hyperlinear
    => some canonical embedding of H is a negative instance of 6.2(a),
       even allowing dimension ratios tending to one.               (13)
```

This does not assert a negative instance without first establishing
hyperlinearity of H. It locates the sufficient rounding premise in a
published open problem. The two-use selection argument is essential:
merely representing one arbitrary native commutant by finite algebras
does not alone give the scalar global commutant needed for the final
contradiction.

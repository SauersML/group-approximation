# Maximal-abelian channel rounding and its native heat obstruction

2026-09-08. Written finite-dimensional proofs. No local execution,
build, numerical search, or new Lean verification. The general
conditional-expectation rounding problem and the nonhyperlinear-group
goal remain open.

Write `tr=Tr/d`, `||.||_2` for normalized Hilbert--Schmidt norm, and
`||T||_(infinity->2)=sup_(||x||<=1)||T(x)||_2`. A Schur channel in a
chosen orthonormal basis multiplies the entry `x_ij` by a correlation
coefficient `s_ij`. It fixes the full diagonal algebra pointwise.

## 1. An averaged maximal-abelian energy gives a Schur approximation

Let `P:M_d->M_d` be self-adjoint on `L^2`, unital, trace-preserving
and completely positive. Let `D` be a maximal abelian subalgebra and
define

```text
a_D(P)=integral_(u in U(D)) [1-Re tr(u*P(u))] du.       (1)
```

The integrand is nonnegative because `P` contracts `L^2` and `u`
is a unitary. Haar measure is normalized. In particular, a uniform
bound `||P(u)-u||_2<=a` implies `a_D(P)<=a`, but (1) is the
weaker assumption used below.

Choose a Kraus representation

```text
P(x)=sum_k v_k* x v_k,
sum_k v_k* v_k=sum_k v_k v_k*=I.
```

Put `d_k=E_D(v_k)` and `h=sum_k d_k* d_k`. In diagonal coordinates,

```text
h_i=sum_k |(v_k)_ii|^2 <= sum_(k,j) |(v_k)_ji|^2=1.
```

Thus `0<=h<=I`. Haar averaging conjugation by `U(D)` is `E_D`, so

```text
sum_k ||v_k-d_k||_2^2
 =integral_(u in U(D)) [1-Re tr(u*P(u))] du
 =tr(I-h)=a_D(P).                                    (2)
```

One can also obtain (2) by integrating the identity
`sum_k ||u v_k-v_k u||_2^2=2-2Re tr(u*P(u))`.

Define the repaired channel

```text
S(x)=sum_k d_k* x d_k+(I-h)^(1/2) x (I-h)^(1/2).      (3)
```

All Kraus operators in (3) are diagonal. Their squared moduli sum
to `I`, so `S` is unital, trace-preserving, completely positive,
and fixes `D`. Its coefficient at `E_ij` contributed by the first
sum is `sum_k conjugate((v_k)_ii)(v_k)_jj`. This is also the
coefficient of `E_ij` in `P(E_ij)`, and is real because `P` is
self-adjoint on `L^2`. The added coefficient is real as well.
Consequently `S` is a self-adjoint Schur channel.

For a dimension-independent comparison, use Stinespring columns

```text
V=(v_1,...,v_r,0),
W=(d_1,...,d_r,(I-h)^(1/2)).
```

Both columns are isometries. Normalize the rectangular Hilbert--Schmidt
norm by the dimension `d` of their common domain. Equation (2) gives
`||V-W||_2^2=2a_D(P)`. Expanding the difference of the two compressions
of `I tensor x` gives

```text
||P-S||_(infinity->2) <= 2 sqrt(2a_D(P)) =: gamma.      (4)
```

Only the isometry operator norms enter this estimate; there is no
factor depending on the number of Kraus operators or on `d`.

## 2. Combining this repair with exact Schur rounding

Let `epsilon=||P^2-P||_(infinity->2)`. Both maps contract operator
norm and `L^2`, so

```text
||S^2-S||_(infinity->2) <= epsilon+3gamma.              (5)
```

Indeed, expand `S^2-P^2=S(S-P)+(S-P)P` and estimate the three
differences using the appropriate contractions. Applying the
[matching-and-Gram Schur theorem](schur-near-idempotent-partition-rounding-2026-09-08.md)
gives a partition of the diagonal coordinates and its block algebra
`B`, containing `D`, with

```text
||P-E_B||_(infinity->2)
 <= gamma+min(1,4 sqrt(epsilon+3gamma)).                (6)
```

This is a positive rounding theorem under the additional averaged
maximal-abelian hypothesis. It does not manufacture that hypothesis.

## 3. A fixed noncommuting pair gives a uniform separation

This part applies to a map `P` that contracts operator norm and `L^2`.
For unitaries `V,W`, put

```text
beta_V=sup_(||x||<=1)||[V,P(x)]||_2,
beta_W=sup_(||x||<=1)||[W,P(x)]||_2,
c=||VW-WV||_2.
```

Here `[V,x]=Vx-xV` is an additive commutator. Let `S` be any map
fixing a maximal abelian `D` pointwise and write
`eta=||P-S||_(infinity->2)`. For every `u in U(D)`,

```text
||[V,u]||_2 <= beta_V+2eta.
```

Haar averaging gives the exact identity

```text
integral ||[V,u]||_2^2 du=2||V-E_D(V)||_2^2.
```

Let `X=E_D(V)` and `Y=E_D(W)`. They are commuting contractions;
no polar repair is necessary. The decomposition

```text
VW-WV=[V-X,W]+[X,W-Y]
```

therefore proves

```text
c <= sqrt(2)(beta_V+beta_W)+4 sqrt(2) eta.             (7)
```

This is uniform over every choice of the maximal abelian algebra.
It applies in particular to all Schur channels in all bases, and
to all conditional expectations whose ranges contain an ambient
maximal abelian subalgebra.

For an averaged version suppose in addition `P` is self-adjoint and
`0<=P<=I` on `L^2`. Then `(I-P)^2<=I-P` yields

```text
integral ||P(u)-u||_2^2 du <= a_D(P).
```

Using Minkowski's inequality in the Haar integral instead of the
uniform estimate above proves

```text
c <= sqrt(2)(beta_V+beta_W)+4 sqrt(2) sqrt(a_D(P)).     (8)
```

Without Hilbert-space positivity, `L^2` contractivity still gives
the same argument with `sqrt(2a_D(P))` in place of `sqrt(a_D(P))`.

## 4. Admissible native Kazhdan heat satisfies the needed bounds

For completeness, the heat estimate required here can be proved
directly, without assuming any rounding theorem. Fix a finite symmetric
Kazhdan generating word list `S_L` for the native `L=EL_3(R)`,
`R=L_(F_2)(1,2)`, and pair inverse spellings exactly. Property `(T)`
and its rank transport are among the inputs proved in the
[fixed-core separation argument](leavitt-finite-core-averaging-separation-2026-09-08.md).
Choose a fixed group-algebra SOS certificate

```text
Delta^2-kappa Delta=sum_j xi_j*xi_j,       kappa>0,
Delta=1-|S_L|^(-1)sum_(s in S_L) s.
```

In a full canonical microstate sequence let `epsilon_n` bound the
finitely many equality rows in this expanded certificate, and let

```text
A_n=I-|S_L|^(-1)sum_s Ad(V_(n,s)),
P_n=exp(-t_n A_n),
t_n -> infinity,       epsilon_n t_n -> 0.            (9)
```

The maps are bistochastic UCP and `0<=P_n<=I` on `L^2`.
Evaluating the fixed SOS identity gives a residual satisfying

```text
||(A_n^2-kappa A_n-sum_j X_(n,j)*X_(n,j))x||_2
 <= C epsilon_n ||x||_op.                            (10)
```

This follows by expressing the residual as a fixed linear combination
of differences of adjoint word maps and using
`||Ad(V)x-Ad(W)x||_2<=2||V-W||_2||x||_op`.
For `g(s)=<A_n exp(-sA_n)x,exp(-sA_n)x>`, differentiation and
operator-ball preservation give

```text
g'(s)<=-2kappa g(s)+2C epsilon_n ||x||_op^2,
g(s)<=2 exp(-2kappa s)||x||_2^2
       +(C epsilon_n/kappa)||x||_op^2.               (11)
```

The Dirichlet identity expresses `g(t_n)` as the mean squared
generator commutator of `P_n(x)`. Thus each fixed generator has
`beta_(n,s)->0` uniformly on the operator unit ball. Telescoping
extends this to each fixed word. If a separately spelled matrix for
the same word is used, its equality defect contributes another
vanishing term. No growing word or uniform finite-coordinate spectral
gap is used here.

Choose the two fixed native roots `v=x_12(1)` and `w=x_23(1)`.
Their group commutator is the nonidentity root `x_13(1)`. Full
canonicality consequently gives

```text
||V_n W_n-W_n V_n||_2 -> sqrt(2).                    (12)
```

Combining (7)--(12), including the uniformity over `D`, proves

```text
liminf_n inf_(all-basis Schur S) ||P_n-S||_(infinity->2) >= 1/4,
liminf_n inf_D a_D(P_n) >= 1/16.                     (13)
```

The second conclusion uses positivity of the heat as a Hilbert-space
operator. Both apply conditionally to any full canonical microstates;
no such sequence is constructed.

## 5. The remaining general rounding problem

Equations (6) and (13) serve different purposes. Equation (6) supplies
an explicit positive theorem for channels with a nearly fixed ambient
maximal abelian algebra. Equation (13) proves that native heat stays
a fixed distance from that class in every basis. Near idempotence
alone has not supplied the hypothesis of (6).

A general finite-dimensional subalgebra of `M_d` is represented as
`direct_sum_i (M_(a_i) tensor I_(b_i))`. It contains an ambient
maximal abelian subalgebra exactly when every multiplicity `b_i=1`.
Thus (13) excludes these multiplicity-one rounding targets. It does
not exclude general represented algebras, whose multiplicities are
precisely what this Schur argument does not address. In particular,
the result is not a proof or a refutation of general uniform
conditional-expectation rounding and gives no matrix-relator gap.

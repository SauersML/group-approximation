---
rg: 2
id: small-angle-cohomology-and-hard-curvature-proof
kind: route
title: Kill the tangent module of delta-scaled operator-small matrix sequences
target: two-kazhdan-correction-has-quadratic-rank-curvature
requires:
  - two-kazhdan-stationary-curvature-has-no-small-angle-part
---

Fix a free ultrafilter and the input scale `delta_j`. Let `H_all` be the
Hilbert ultraproduct of normalized matrix L2 spaces. Define `K_delta` as
the closure of the classes represented by uniformly L2-bounded sequences
`X_j` with

```text
lim_omega delta_j ||X_j||_op = 0.                       (SAC1)
```

This is larger than the closure of operator-bounded sequences used in
the earlier regular-component argument. It includes normalized errors
supported on very small subspaces when their actual angles tend to zero.

Every vector of `K_delta` has representatives satisfying `(SAC1)`.
Indeed, choose core approximants converging in Hilbert norm, choose
omega-large sets on which their approximation errors and delta-scaled
operator norms have the required bounds, and choose the approximation
index tending to infinity sufficiently slowly along those sets.
The resulting diagonal sequence represents the given vector, remains
L2-bounded, and has delta-scaled operator norm tending to zero.
Skew-Hermitian vectors admit skew-Hermitian representatives by taking
the skew part. Arbitrary left or right multiplication by unitary
sequences preserves this closed subspace and its orthogonal complement.

Choose fixed word representatives `q_g`, with `q_e` empty, and put
`u_j(g)=U_j(q_g)`. Each fixed-pair defect

```text
D_j(g,h)=u_j(g)u_j(h)u_j(gh)^*
```

has HS distance `O(delta_j)` from identity, by the fixed van Kampen area.
For core vectors `X`,

```text
||(D_j-I)X_j||_2+||X_j(D_j-I)||_2
 <= 2||D_j-I||_2 ||X_j||_op -> 0.
```

Hence `Ad(u(g))` defines a genuine unitary G-action on `K_delta`,
although it need not do so on `H_all`. Density extends the group law
from the core. The projection `P_delta` onto `K_delta` commutes with
each adjoint operator, since both the subspace and its complement are
invariant under these unitary operators.

Here is the quadratic-error estimate that replaces uniform integrability.
If `A_j,B_j` are operator-bounded with L2 norms `O(delta_j)`, then
`[A_jB_j/delta_j]` is L2-bounded and orthogonal to `K_delta`. For a core
test vector `Y`,

```text
|tr(Y_j^* A_j B_j)|/delta_j
 <= ||Y_j||_op ||A_j||_2 ||B_j||_2/delta_j
 = O(delta_j ||Y_j||_op) -> 0.                         (SAC2)
```

Density proves orthogonality to the closed subspace. Apply `(SAC2)` to
unitarity and the exact associativity identity

```text
(D-I)+(D-I)^*=-(D-I)^*(D-I),
D(g,h)D(gh,k)=Ad(u(g))(D(h,k))D(g,hk).
```

Thus `c_delta(g,h)=P_delta[(D_j(g,h)-I)/delta_j]` is a skew-Hermitian
2-cocycle for the genuine action on `K_delta`. Ordinary H2 vanishing
gives a cochain with this coboundary; applying the equivariant real
projection `X -> (X-X^*)/2` gives a skew-Hermitian cochain `b` with
`db=c_delta`. One may pass to
the closed invariant span of the countably many cocycle values; no
nonseparability assumption is needed. Since `c_delta(e,g)=0`, its
coboundary equation forces `b(e)=0`.

Choose representatives `b_j(g)` satisfying `(SAC1)` and define

```text
v_j(g)=exp(-delta_j b_j(g))u_j(g),       v_j(e)=I.
```

Functional calculus for a skew-Hermitian matrix gives

```text
||exp(-delta_j b_j)-I+delta_j b_j||_2
 <= (delta_j^2/2)||b_j||_op ||b_j||_2 = o(delta_j).
```

Products of two exponent differences have L2 norm `o(delta_j)` because
one factor is `O(delta_j)` in L2 and the other is `o(1)` in operator
norm. A mixed product with an old defect has the same bound: the old
defect is `O(delta_j)` in L2 and the exponent difference is `o(1)` in
operator norm. Therefore

```text
[(v_j(g)v_j(h)v_j(gh)^*-I)/delta_j]
 = [(D_j(g,h)-I)/delta_j]-db(g,h) in K_delta^perp.       (SAC3)
```

Set `V_j(s)=v_j(bar(s))`. The fixed null word
`q_(bar(s))s^(-1)` bounds the difference between `u_j(bar(s))` and
the original generator by `O(delta_j)`. This also handles redundant
generator symbols. The exponent bound proves `(QRC1)`. Finite word
telescoping and invariance of `K_delta^perp` under left/right unitaries
show that every rescaled defining error `[E_(j,r)/delta_j]` lies in
that orthogonal complement. Inverse letters follow from the pair
equation for `(g,g^(-1))` and `v_j(e)=I`.

We now identify what this orthogonality says about angles. Let
`X_j=E_j/delta_j`, with `||X_j||_2<=C`. If low-angle energy does not
vanish as the cutoff tends to zero, choose `t_j->omega 0` slowly so
that

```text
Y_j=X_j 1_(|E_j|<=t_j)
```

retains a fixed positive amount of L2 energy. Then
`delta_j||Y_j||_op<=t_j`, so `[Y_j]` belongs to `K_delta`, whereas
`tr(Y_j^*X_j)=||Y_j||_2^2` contradicts orthogonality.
Conversely, at each fixed `t>0`, the high-angle part satisfies

```text
tr(1_(|E_j|>t)) <= C^2 delta_j^2/t^2,
||X_j 1_(|E_j|>t)||_1 <= C^2 delta_j/t.
```

Its pairing with each core test vector tends to zero by `(SAC1)`.
The low-angle pairing is bounded by its L2 norm times that of the
test vector. Taking first the ultralimit and then `t downarrow 0`
proves the converse. This proves the ultrafilter version of `(QRC2)`.
Choose countably many cutoffs tending to zero and a diagonal subsequence
realizing their estimates. Monotonicity in the cutoff gives `(QRC2)`
with the ordinary limsup written in the claim.

For fixed epsilon choose a fixed cutoff `t` making every low-angle
L2 error less than `epsilon delta_j/2` eventually, and put

```text
P_(j,epsilon)=join_(r in R) 1_(|E_(j,r)|>t).
```

Its normalized rank is at most `|R|C^2 delta_j^2/t^2`. Its complement
is below every low spectral projection. Since each unitary-minus-identity
error is normal, both left and right complementary HS errors are at most
`epsilon delta_j/2`. This proves `(QRC3)`. The operator bound off this
support is only `t`; it is not asserted to be `epsilon delta_j`.

Finally `(QRC4)` implies that each normalized input relator error lies
in `K_delta`: truncate its actual angle at cutoffs tending to zero
sufficiently slowly. Van Kampen telescoping puts every `c(g,h)` in
`K_delta` as well. Thus the residual in `(SAC3)` vanishes in all of
L2, giving HS defect `o(delta_j)`. Uniform integrability implies this
small-angle condition because its normalized cutoff `M` corresponds to
actual angle `M delta_j`. Operator-norm-small input errors imply it
directly. In the latter case all fixed-word section discrepancies tend
to zero in operator norm, as do the exponent differences, proving the
last assertion about generator correction. None of these arguments
makes the spectral supports reducing or supplies an infinite repair
schedule for a fixed matrix dimension.

The uniform finite-scale version `(QRC5)` follows by a diagonal
contradiction, without a uniform cochain estimate. If it failed for a
fixed epsilon, choose for each integer `j` a tuple of positive defect
`delta_j<1/j` for which no output obeys its bounds with `A=C=j`.
Apply the sequential theorem to this input with reduction factor
`epsilon/2`. Along its output subsequence the generator and residual HS
constants, and the fixed-factor rank constant, are finite. For large
subsequence indices all are below `j`, and the complementary error is
at most `epsilon delta_j`. This contradicts the choice of the inputs.
The resulting constants are nonconstructive and may grow as epsilon
decreases. This argument supplies no invariant support.

The appended stationary and gradient-flow consequence is the required
stationary-curvature theorem, applied to the same all-unitary H2
hypothesis and the literal elementary generator sections. It tests
the cohomological descent direction against the actual energy gradient,
so almost-stationarity removes the need to change the tuple first.
Its first-exit estimate supplies the stated hybrid correction radius,
without assuming that the spectral supports are invariant.

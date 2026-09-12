# Transporting projection expansion between physical corners

Date: 2026-09-08. Written matrix proof; no computation or build.

All traces are normalized by the original dimension. Let `K` be
self-adjoint, bistochastic and UCP on `M_d`, and write

\[
 \mathcal E(x)=\tau(x^*(1-K)x).
\]

This is a nonnegative quadratic form and its square root is a
seminorm. Since `K` is an `L^2` contraction,
`E(x)<=2||x||_2^2`. No nonnegative-spectrum assumption on `K`
is needed.

## 1. Moving a projection into a tested corner

Let `p,q` be arbitrary projections and let `q'` be the range
projection of `pq`. Put `ell_q=tau(q(1-p))`. Then

\[
 q'\leq p,\quad \operatorname{rank}q'\leq\operatorname{rank}q,
 \quad \tau(q')\geq\tau(q)-\ell_q,
 \quad \|q-q'\|_2^2\leq2\ell_q.
 \tag{1}
\]

To verify all four statements, diagonalize `qpq` on the range of
`q`. For each positive eigenvalue `cos^2(theta)`, the corresponding
unit vector and its normalized image under `p` form a principal-angle
pair. Zero eigenvalues are precisely the vectors in the range of
`q` perpendicular to `p`. If their number is `k`, then

\[
 \tau(q)-\tau(q')=k/d\leq\ell_q,
 \qquad \tau(qq')=\tau(qp),
 \qquad \|q-q'\|_2^2=2\ell_q-k/d.
 \tag{2}
\]

These formulas include `q'=0`. In particular no intersection
`q wedge p` is used; that intersection could lose the whole rank
even at a small nonzero angle.

Suppose that for some `theta>=0`, `c>0` and `kappa>=0`,

\[
 \mathcal E(e)\geq c\tau(e)-\kappa
 \quad\text{for every projection }e\leq p
                   \text{ with }\tau(e)\leq\theta.
 \tag{3}
\]

Every projection `q` with `tau(q)<=theta`, wherever it lies,
satisfies

\[
 \boxed{\mathcal E(q)\geq
       \frac c2\tau(q)-\frac\kappa2
                      -\left(\frac c2+4\right)\ell_q.}
 \tag{4}
\]

Indeed, `q'` is eligible for (3), and (1) gives
`E(q')>=c tau(q)-c ell_q-kappa`. On the other hand,

\[
 \sqrt{\mathcal E(q')}\leq
       \sqrt{\mathcal E(q)}+\sqrt2\|q-q'\|_2
       \leq\sqrt{\mathcal E(q)}+2\sqrt{\ell_q},
\]

so `E(q')<=2E(q)+8ell_q`. Combining these two inequalities
proves (4). The expansion cutoff is not enlarged: this uses the
actual rank decrease in (1).

## 2. Variance in the new corner

Let `r` be a nonzero projection with `tau(r)/2<=theta`, and put
`ell_r=tau(r(1-p))`. For `q<=r`, positivity gives
`ell_q<=ell_r`. Thus (4) supplies expansion inside `r` with

\[
 c'=c/2,\qquad
 \kappa'=\kappa/2+(c/2+4)\ell_r.
\]

Apply the established
[[reflected-corners-control-defective-quantum-variance]] theorem,
which includes the exterior boundary of `r`. For a self-adjoint
`x=rxr`, `M=||x||_op`, the result is

\[
 \boxed{\begin{aligned}
 \left\|x-\frac{\tau(x)}{\tau(r)}r\right\|_2^2
 &\leq\frac8{c^2}\mathcal E(x)+\frac{8M^2}{c}\kappa\\
 &\quad+\left(8+\frac{64}{c}\right)M^2\ell_r
           +\frac{16M^2}{c}\mathcal E(r).
 \end{aligned}}                                                   \tag{5}
\]

All terms retain ambient normalization, including `kappa` and
the trace leakage. If a normalized corner trace is desired, divide
every term by `tau(r)`.

The leakage term cannot be omitted even for exact expectations.
On `M_2` take `K` to be diagonal expectation, let `p` be the
rank-one projection onto `(1,1)/sqrt(2)`, and set `r=1`.
The only projections under `p` are zero and `p`, and

\[
 \mathcal E(p)=1/4=\tfrac12\tau(p).
\]

Thus (3) holds with `c=1/2`, `kappa=0`, `theta=1/2`.
Nevertheless the diagonal Pauli matrix `x=diag(1,-1)` has
variance one in `r`, while `E(x)=E(r)=0`. Here
`ell_r=1/2`. A variance conclusion retaining only energy and
the original expansion defect would be false.

## 3. Summation over a common tested corner

Suppose projections `r_i` satisfy `sum_i r_i<=C1` and their
half ranks satisfy the same cutoff in (3). Then

\[
 \sum_i\ell_{r_i}
 =\tau\left((1-p)\sum_i r_i\right)
 \leq C\tau(1-p).
 \tag{6}
\]

If (3) has defect zero, summing (5) for self-adjoint contractions
`x_i=r_i x_i r_i` gives

\[
 \begin{aligned}
 \sum_i\left\|x_i-\frac{\tau(x_i)}{\tau(r_i)}r_i\right\|_2^2
 &\leq\frac8{c^2}\sum_i\mathcal E(x_i)
      +\left(8+\frac{64}{c}\right)C\tau(1-p)\\
 &\quad+\frac{16}{c}\sum_i\mathcal E(r_i).
 \end{aligned}                                                     \tag{7}
\]

Zero `r_i` are omitted. With nonzero individual defects, add
`(8/c)sum_i kappa_i` instead of multiplying an untracked defect
by an unspecified outcome count.

For the spectral cuts of
[[low-energy-povms-yield-flexible-projection-cuts]], one has `C=3`.
Equation (6) therefore handles the possibility that those cuts leave
one original large retained corner. Small projections in the cuts
need not actually lie in that corner: (1)--(4) move the test back
and pay the aggregate trace leakage once.

## 4. What changes for successive remaining corners

Let `p_0,...,p_m` be an orthogonal partition of one, and define

\[
 \beta=\sum_{i=0}^m\mathcal E(p_i),\qquad
 R_i=1-\sum_{j<i}p_j\quad(1\leq i\leq m).
\]

The projection `p_0` may be an initially discarded corner. Suppose
the later cuts satisfy `r_i<=3K(p_i)`, as happens for spectral
thresholds in `(1/3,2/3)`. Then

\[
 \boxed{\sum_{i=1}^m\tau(r_i(1-R_i))\leq\frac32\beta.}
 \tag{8}
\]

For a proof put `w_(ji)=tau(p_j K(p_i))`. Positivity and
self-adjointness give `w_(ji)>=0` and `w_(ji)=w_(ij)`; the
marginals are `sum_j w_(ji)=tau(p_i)`. Hence

\[
 \sum_{i=1}^m\tau((1-R_i)K(p_i))
 =\sum_{j<i}w_{ji}
 =\frac12\sum_i\left(\tau(p_i)-\tau(p_iK(p_i))\right)
 =\beta/2.
 \tag{9}
\]

Every unordered pair is counted once, including pairs involving
`p_0`. Multiplying the operator inequality for each cut by the
positive projection `1-R_i` under the trace proves (8).

This estimate is useful but does not by itself close the recursive
selection argument. If a seed rule only supplies
`E(p_i)<=h tau(p_i)`, it yields `beta<=h`. The leakage term in
(5) then contains `beta/c`. If the expansion threshold `c` is of
order `h`, this ratio need not tend to zero. Obtaining `beta=o(c)`,
a stronger leakage estimate, or another selection principle remains
necessary for that use of the estimate.

The remaining-corner leakage also need not vanish with the
idempotence defect for arbitrary seeds. Again let `K` be diagonal
expectation on `M_2`, but take `p_0` to be the rank-one projection
onto `(cos(theta),sin(theta))`, `p_1=1-p_0`, with
`0<theta<arcsin(1/sqrt(3))`. Every threshold in `(1/3,2/3)`
of `K(p_1)` is `r_1=diag(0,1)`. Direct calculation gives

\[
 \tau(r_1(1-R_1))=\tfrac12\sin^2\theta>0,
 \qquad\beta=2\sin^2\theta\cos^2\theta,
 \qquad K^2-K=0.
 \tag{10}
\]

These are cuts of the repaired positive effects themselves. The
example excludes an idempotence-only upper bound tending to zero
for all supplied seed choices; it does not exclude a better choice.

## 5. A bounded weighted projection frame has bounded energy

There is a related estimate useful for nonorthogonal seed selection.
Let `w_i>=0`, let `q_i` be projections, and suppose

\[
 S=\sum_i w_iq_i\leq C1.
\]

Then

\[
 \boxed{\mathcal E(S)\leq4C\sum_i w_i\mathcal E(q_i).}
 \tag{11}
\]

Choose a Kraus family `K(x)=sum_a v_a^*xv_a`. Bistochasticity
gives the energy identity

\[
 2\mathcal E(x)=\sum_a\|[v_a,x]\|_2^2
 \quad(x=x^*).
\]

Since `q_i^2=q_i`, for each fixed Kraus operator `v` one has

\[
 [v,S]=\sum_i w_i[v,q_i]q_i+\sum_i w_iq_i[v,q_i].
\]

Factor the first sum as an operator row times an operator column.
The row consists of `sqrt(w_i)[v,q_i]`, and the column of
`sqrt(w_i)q_i`. Its column operator norm is at most `sqrt(C)`
because its squared norm is `||S||`. Rectangular
Hilbert--Schmidt Cauchy--Schwarz therefore bounds the squared norm
of this sum by `C sum_i w_i||[v,q_i]||_2^2`. The second sum has
the same bound, using the projection row and commutator column.
The squared triangle inequality gives

\[
 \|[v,S]\|_2^2\leq4C\sum_i w_i\|[v,q_i]\|_2^2.
\]

Sum over Kraus operators and divide by two to obtain (11).
No factor depends on the number of projections.

In particular, if `S<=1` and `E(q_i)<=h tau(q_i)`, then
`E(S)<=4h tau(S)<=4h`, and `E(1-S)=E(S)`. The residual positive
effect is low-energy. This does not ensure that a low-energy
projection extracted from it lies under its support gap or can be
added while retaining `S<=1`. The estimate is a packing tool,
not a proof that the packing fills the identity or that its members
are expanding.

The results above isolate two different costs: leaving one original
retained corner has the aggregate allowance (6), while leaving
successive remaining corners is controlled by the seed boundary
(8). Neither statement supplies the missing quantum seed selection
or a headline group-approximation result.

# Flexible Hilbert--Schmidt distance: words, dimension, and upward repair

## Status and purpose

This is a complete written proof of the metric estimates below. It repairs
the cross-dimension justification in
`triangle-reduces-dv-to-unbounded-congruence-capture`. It does not prove
congruence capture, flexible stability of `SL_2(Z[1/2])`, or the existence
of a non-hyperlinear group. No literature priority or Lean verification is
asserted.

The source convention is the zero-padding distance used in
[Dogon--Vigdorovich, arXiv:2506.20843v2](https://arxiv.org/html/2506.20843v2),
Definition 1.2 and the discussion preceding Question 1.4. The comparison
representation in that question may have a different dimension. Corollary
1.5 is their implication from a positive answer to a non-hyperlinear finite
central extension. The proofs here are elementary metric and matrix
arguments; they do not supply that positive answer.

For positive integers `d,D`, put `M=max(d,D)` and let `j_M` extend a matrix
by a zero block to size `M`. For `U in U(d)` and `V in U(D)`, write

\[
 d_0(U,V)^2=\frac{\|j_M(U)-j_M(V)\|_F^2}{M}.             \tag{1}
\]

Zero padding in this definition must be distinguished from padding a
representation by the trivial representation, which uses identity blocks.
Within one dimension (1) is the usual normalized Hilbert--Schmidt distance.
Tuple distance is the maximum of (1) over a fixed nonempty generating set.

## 1. Triangle inequality, with all dimension orderings covered

We prove a slightly more general fact. In any real or complex Hilbert space,
on its nonzero vectors the function

\[
 h(x,z)=\frac{\|x-z\|}{\max(\|x\|,\|z\|)}              \tag{2}
\]

is a metric. Symmetry and separation are immediate. For the triangle
inequality, interchange `x,z` if necessary so that
`a=||x|| <= b=||z||`, and put `c=||y||`.

If `c<=b`, the ordinary triangle inequality gives

\[
 h(x,z)\le\frac{\|x-y\|+\|y-z\|}{b}
          \le h(x,y)+h(y,z).
\]

If `c>=b`, use the inversion map `J(v)=v/||v||^2`. Direct expansion of
the squared Hilbert norm gives

\[
 \|J(v)-J(w)\|=\frac{\|v-w\|}{\|v\|\|w\|}.
\]

The triangle inequality for `J(x),J(y),J(z)`, multiplied by `abc`, yields

\[
 c\|x-z\|\le b\|x-y\|+a\|y-z\|.
\]

Divide by `bc` and use `a<=b`. Since both distances through `y` have
denominator `c`, this proves (2)'s triangle inequality in the remaining
case. No ordering of matrix dimensions has been omitted.

Embed all finite matrices in the Hilbert space of Hilbert--Schmidt
operators on `ell^2(N)` by zero extension. A `d`-dimensional unitary has
Frobenius norm `sqrt(d)`. Thus (1) is the restriction of (2), proving that
`d_0` is a metric. The maximum metric on tuples also satisfies the triangle
inequality.

## 2. Word evaluation and local defects

Let `U,V` be unitary tuples, of possibly different dimensions, and let
`delta=max_s d_0(U_s,V_s)`. For every nonempty word `w` of length `ell`,

\[
 d_0(w(U),w(V))\le \ell\delta.                         \tag{3}
\]

To see this, zero-pad both tuples to `M`. An inverse letter is evaluated
by the adjoint of its padded generator, not by inverting the padded
matrix. Padding commutes with adjoints and with nonempty products; every
padded factor has operator norm at most one. Telescope the product
difference, and use `||AXB||_F<=||A||_op ||X||_F ||B||_op` in each term.
Division by `sqrt(M)` proves (3).

There is an important empty-word exception. Its two values are `I_d` and
`I_D`, whose distance is `sqrt(|D-d|/M)`, not necessarily zero. The bound
valid for all words is therefore

\[
 d_0(w(U),w(V))\le\max(1,|w|)\delta,                   \tag{4}
\]

using the dimension lower bound proved in Section 3 for the empty word.
Equivalently one can handle the identity word separately.

Suppose a local defect is defined by finitely many pairs of words:

\[
 e(U)=\max_i d_0(a_i(U),b_i(U)).
\]

Each pair is evaluated in the dimension of its own tuple. From the metric
triangle inequality and (4),

\[
 |e(U)-e(V)|\le L\delta,
 \quad L=\max_i\bigl(\max(1,|a_i|)+\max(1,|b_i|)\bigr).
                                                               \tag{5}
\]

For the nonempty Iwahori words, each of length at most `L_B`, (5) gives
the required `2 L_B delta` bound in either direction, in any two dimensions.

### Why one common-normalization triangle is not sufficient

Consider the pairs

\[
 A=\operatorname{diag}(-1,1),\quad B=I_2,\qquad
 a=(-1),\quad b=(1).
\]

Their internal squared defects are

\[
 d_0(A,B)^2=2,\qquad d_0(a,b)^2=4,
\]

while `d_0(A,a)^2=d_0(B,b)^2=1/2`. Padding `a,b` to dimension two reduces
their squared internal defect to `2`. A triangle proved solely with that
common normalization bounds the *padded* defect; it is not yet a bound on
the original scalar defect `2`. In particular the earlier reduction's
sentence about padding the input pair did not justify the case where the
comparison pair is smaller. Equation (5) repairs the argument using the
actual metric, and preserves the stated constant.

## 3. The dimension charge and an exact compression identity

Assume `d<=D`, let `P` be the projection onto the first `d` coordinates,
and set `Q=I_D-P`. Write `A=PVP|_(P C^D)`. Unitarity gives

\[
 \|U\oplus0-V\|_F^2
   =(D-d)+\|U-A\|_F^2+\|QVP\|_F^2.                   \tag{6}
\]

Indeed the left side is `d+D-2 Re Tr(U^* A)`. On the right,
`||A||_F^2+||QVP||_F^2=d`, because `VP` is an isometry on `P C^D`.
Expansion gives the same expression. This proves (6), including when
`P` is not invariant under `V`.

By symmetry and nonnegativity, in all dimensions

\[
 \frac{|D-d|}{\max(d,D)}\le d_0(U,V)^2.                \tag{7}
\]

Consequently distance at most `epsilon<1` forces

\[
 \frac{\max(d,D)}{\min(d,D)}\le\frac1{1-\epsilon^2}.
                                                               \tag{8}
\]

For `D>=d`, (6) also controls both compression error and leakage:

\[
 \frac{\|U-A\|_F^2+\|QVP\|_F^2}{D}
       =d_0(U,V)^2-\frac{D-d}{D}.                     \tag{9}
\]

In particular any flexible repair whose distance tends to zero already
has relative added dimension tending to zero. This is a consequence of the
chosen metric, not an extra hypothesis that can be traded for a repair.

## 4. Upward-only repair costs at most a factor two

Let `C` be a nonempty class of finite-dimensional representations of a
fixed group (or compatible pairs of representations) with the following
closure property: if `rho in C`, then `rho direct_sum 1_k in C` for every
nonnegative integer `k`. Fix an input tuple `pi` of dimension `d`, and put

\[
 A(\pi)=\inf_{\rho\in C}d_0(\pi,\rho),\qquad
 A_\uparrow(\pi)=\inf_{\substack{\rho\in C\\\dim\rho\ge d}}
                           d_0(\pi,\rho).
\]

Then

\[
 A(\pi)\le A_\uparrow(\pi)\le2A(\pi).                \tag{10}
\]

The first inequality is inclusion of the sets of comparisons. To prove the
second, take any comparison `rho` of dimension `D`. If `D>=d`, keep it.
If `D<d`, set `rho'=rho direct_sum 1_(d-D)`, which belongs to `C` and has
dimension `d`. On every generator the ordinary same-size triangle gives

\[
 \|\pi(s)-\rho'(s)\|_{2,d}
 \le \|\pi(s)-(\rho(s)\oplus0)\|_{2,d}
       +\sqrt{(d-D)/d}
 \le2d_0(\pi,\rho),                                  \tag{11}
\]

where the last step uses (7). Take the maximum over generators and then
the infimum over `rho`; no minimizing comparison is assumed to exist.

Both compatible Iwahori pairs and exact congruence vertex pairs are closed
under these trivial summands. Thus their unrestricted distance-to-class
functions and the versions allowing only dimensions at least the input
dimension vanish along exactly the same sequences. Combining (8) and
(10) gives the usual `D_n>=d_n`, `D_n/d_n ->1` form whenever such repair
exists. These equivalences do not construct a close comparison.

### The factor two is sharp, even for a class of exact representations

Take the group `C_2`, its one-element generating set, and let `C` consist
of its trivial representations in all positive dimensions. For integers
`d>4k>=4`, let the input generator be

\[
 U=\operatorname{diag}(I_{d-k},-I_k).
\]

For the comparison `I_D`, direct evaluation of (1) gives

\[
 d_0(U,I_D)^2=
 \begin{cases}
 (d-D)/d,&1\le D\le d-k,\\
 (3D-3d+4k)/d,&d-k\le D\le d,\\
 1-(d-4k)/D,&D\ge d.
 \end{cases}                                         \tag{12}
\]

The first branch decreases, the second increases, and the third increases
because `d>4k`. Their exact minima therefore give

\[
 A(U)=\sqrt{k/d},\qquad A_\uparrow(U)=2\sqrt{k/d}.
\]

This establishes sharpness of (10) for an admissible class, not just for a
particular choice of comparison. It makes no claim that the Iwahori class
itself attains this factor.

## 5. Consequence for the live Iwahori proof obligation

Let `A_cong` denote distance to the union of exact congruence vertex pairs,
and assume their established same-size repair estimate with constant `K`.
Given a comparison `rho`, (5) gives

\[
 \operatorname{def}(\rho)
 \le\operatorname{def}(\pi)+2L_B d_0(\pi,\rho)
\]

whether `rho` is smaller or larger. The metric triangle then rigorously
gives the existing reduction

\[
 A_{\rm cong}(\pi)\le D(\pi)
 \le K\operatorname{def}(\pi)+(1+2KL_B)A_{\rm cong}(\pi).
\]

The lower bound uses the separately stated congruence description of exact
compatible pairs. Neither that description nor the congruence repair
theorem is re-proved here; they remain dependencies of the reduction.

The missing statement remains
`def(pi_n)->0 implies A_cong(pi_n)->0`. Fixed-dimensional compactness,
the dimension charge (7), and the conversion (10) do not supply it. The
attempt to obtain it from dimension control alone stops at (7): that
inequality assumes a close exact comparison, whose existence is precisely
what must still be proved.

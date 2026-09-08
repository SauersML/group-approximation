# Coefficient two holds for every two-dimensional Higman tuple

2026-09-07. The theorem below covers all of U(2)^4, using an exact finite
polynomial certificate, and all common direct sums of blocks of size at
most two. It does **not** cover arbitrary larger blocks. Indeed the
[rational U(3) witness](higman-qutrit-coefficient-bound.md) refutes even
coefficient sixteen. No nonhyperlinear existence or Lean verification
claim is made.

## Theorem

Let \(U=(U_0,U_1,U_2,U_3)\in U(2)^4\), and use the Higman convention

\[
r_i(U)=U_iU_{i+1}U_i^{-1}U_{i+1}^{-2},\quad
e_v(U)=\|v(U)-I\|_{2,2}^2=2-2\operatorname{Re}\operatorname{tr}_2(v(U)).
\]

Then, for every j,

\[
e_{g_j}(U)\le 2\sum_{i=0}^3 e_{r_i}(U).              \tag{2D}
\]

Cyclic symmetry reduces the proof to j=0. The U(3) counterexample and
(2D) together prove that **three is the smallest matrix dimension in
which coefficient two fails**. Scalars obey the stronger coefficient
one bound, since their commutators vanish.

## 1. Scalar phases reduce U(2) to SU(2)

Write \(U_i=z_iV_i\), with \(|z_i|=1\) and \(V_i\in SU(2)\), choosing a
square root of each determinant. Traces of SU(2) matrices are real.
Set \(c_i=\operatorname{Re}z_i\),
\(x_i=\operatorname{tr}_2(V_i)\), and
\(t_i=\operatorname{tr}_2(r_i(V))\). The scalar exponent of the successor
generator in r_i is -1; that of the conjugator is zero. Thus

\[
e_{g_0}(U)=2-2c_0x_0,\qquad
e_{r_i}(U)=2-2c_{i+1}t_i.
\]

The difference \(2\sum_i e_{r_i}-e_{g_0}\) is affine in the four real
variables \(c_i\in[-1,1]\). It is therefore a convex combination of its
values at \(c_i\in\{-1,1\}\): use independent sign probabilities
\(\Pr(\sigma_i=s)=(1+sc_i)/2\). Each vertex is realized by the tuple
\((\sigma_iV_i)\in SU(2)^4\). It suffices to prove the inequality on SU(2).
This argument retains scalar phases; it never replaces ordinary HS
distance by a projective distance.

## 2. A scalar polynomial bounds every quaternion tuple

Represent \(V_i\) by a unit quaternion \((x_i,v_i)\), with
\(v_i\in\mathbb R^3\) and \(\|v_i\|^2=1-x_i^2\). Quaternion
multiplication, or the formula for conjugation as a rotation, gives

\[
\operatorname{tr}_2(r_i(V))
=x_{i+1}-4x_{i+1}\|v_i\mathbin{\times}v_{i+1}\|^2.   \tag{Q}
\]

For completeness, the dot product of the conjugated vector v_j with
v_j is \((2x_i^2-1)\|v_j\|^2+2(v_i\cdot v_j)^2\). Multiplying by
\(V_j^{-2}\) gives (Q), using
\(\|v_i\times v_j\|^2=(1-x_i^2)(1-x_j^2)-(v_i\cdot v_j)^2\).
Consequently, for j=i+1,

\[
e_{r_i}(V)\ge h_j(x):=
2-2x_j+8\min(x_j,0)(1-x_{j-1}^2)(1-x_j^2).           \tag{L}
\]

This uses both bounds on the squared cross product: zero and
\((1-x_i^2)(1-x_j^2)\). No assumption on joint attainability of the
individual lower bounds is needed.

If \(x_0\ge0\), the incoming relator satisfies
\(e_{r_3}\ge2-2x_0=e_{g_0}\), and (2D) follows immediately.
It remains to consider \(x_0\in[-1,0]\). Divide each other coordinate
into [-1,0] and [0,1], giving eight closed sign boxes which cover the
entire remaining domain, including every boundary.

On each box the following expression is an ordinary polynomial of
degree at most three in each variable:

\[
P(x)=2\sum_jh_j(x)-(2-2x_0)
=14+2x_0-4\sum_jx_j
 +16\sum_{j\,\mathrm{negative}}x_j(1-x_{j-1}^2)(1-x_j^2). \tag{P}
\]

The exact certificate below proves \(P\ge1/36>0\) on these boxes.
Together with (L) and the nonnegative-x_0 case this proves (2D).

## 3. Complete rational certificate, not sampled points

Let \(B_{k,3}(t)=\binom3k t^k(1-t)^{3-k}\). These four polynomials are
nonnegative on [0,1] and sum to one. Their fourfold products therefore
form a nonnegative partition of unity on [0,1]^4. A polynomial written
in this tensor Bernstein basis is bounded below by its smallest
coefficient throughout the box.

To verify the conversion, the identity

\[
t^m=\sum_{k=m}^3\frac{\binom{k}{m}}{\binom3m}B_{k,3}(t),
\qquad 0\le m\le3,
\]

follows by substituting
\(\binom3k\binom{k}{m}=\binom3m\binom{3-m}{k-m}\) and applying the
binomial theorem. Substitute \(x=l+(h-l)t\) and expand each monomial.
This is exactly the conversion in `initial_coefficients`.

The certificate `higman-u2-bernstein-certificate.json` records eight
binary subdivision trees. At an internal node `[axis, left, right]`,
both children are the closed halves of the parent box along that axis.
A null node is a terminal box. Therefore structural induction proves
that each tree covers its entire initial sign box; no omitted cell or
unchecked remainder is possible.

Midpoint de Casteljau subdivision replaces adjacent Bernstein
coefficients by their average, repeatedly. The successive first entries
give the left-child coefficients, and the successive last entries in
reverse order give the right-child coefficients. This identity follows
by substituting t/2 and (1+t)/2 in the Bernstein expansion and using
Pascal's identity; the other coordinates stay unchanged. All arithmetic
is rational.

The verifier reconstructs (P), computes its 256 Bernstein coefficients
per initial box, and follows both children of every recorded split. It
accepts a terminal box only if **all** its coefficients are nonnegative.
It neither reads nor trusts precomputed coefficients or energy values.
The complete replay has:

| Certificate property | Exact value |
| --- | --- |
| Initial sign boxes | 8 |
| Internal subdivision nodes | 48 |
| Terminal boxes | 56 |
| Maximum subdivision depth | 6 |
| Terminal coefficients checked | 14,336 |
| Minimum terminal coefficient | 1/36 |

Thus (P) is nonnegative everywhere in the domain. This is a finite
proof certificate for a continuous parameter space, not a finite sample
of matrices. The separate tests check polynomial conversion and both
half-box identities at rational arguments, cross-check (Q) against exact
matrix word products, check the scalar-phase convex combination, and
reject incomplete or malformed partitions. Those tests support the
implementation; coverage and positivity are supplied by the full replay.

```sh
python3 experiments/higman_u2_certificate.py verify
python3 -m unittest discover -s experiments -p test_higman_u2_certificate.py -v
```

The generator is optional: `generate --output PATH` reconstructs the
same partition. Its depth limit produces an error if exhausted. The
verifier does not assume the generator terminates for other polynomials.

## 4. Consequences for larger tuples with common small blocks

If a tuple V in U(d)^4 is simultaneously block diagonal with blocks of
dimension one or two, each word preserves the same decomposition.
Normalized squared HS energies are the dimension-weighted averages of
their block energies. Applying (2D) in each block proves the same bound
in any total dimension. This concerns **common direct sums**, not tensor
products of two-dimensional spaces or independent decompositions for
different generators.

Suppose U and such a V satisfy
\(\max_i\|U_i-V_i\|_{2,d}\le\varepsilon\). Each relator has word length
five. Telescoping products of unitaries gives
\(\|r_i(U)-r_i(V)\|_2\le5\varepsilon\). The triangle inequality in
\(\mathbb R^4\) then gives, writing \(E(U)=\sum_i e_{r_i}(U)\),

\[
\sqrt{E(V)}\le\sqrt{E(U)}+10\varepsilon.
\]

Using (2D) on V proves the explicit bound

\[
\|U_j-I\|_2\le\sqrt{2E(U)}+(1+10\sqrt2)\varepsilon. \tag{R}
\]

In particular a canonical Higman microstate sequence, for which
\(E(U_n)\to0\) and \(e_{g_j}(U_n)\to2\), must have lower limiting
distance at least \(\sqrt2/(1+10\sqrt2)\) from this common-small-block
class. This is a necessary condition on such a hypothetical sequence,
not a proof that the sequence cannot exist.

There is also an exact dimension ledger. If a fraction \(\theta\) of
a common invariant block decomposition has blocks of dimension at least
three, then

\[
e_{g_j}(U)\le2E(U)+4\theta,                         \tag{D}
\]

because every marked unitary energy is at most four on the remaining
blocks. Hence any canonical sequence must have
\(\liminf\theta\ge1/2\). Neither (R) nor (D) bounds the high-dimensional
blocks themselves. The explicit U(3) counterexample already shows that
the coefficient cannot be carried over unchanged.

## Boundary and prior context

This answers the dimension-two coefficient question left by the earlier
bounded rational search. It does not determine the optimal coefficient
even in dimension two: the earlier exact lower bound is about 1.818,
whereas the present certified upper bound is two. Quaternion coordinates
and Bernstein positivity are classical methods; this contribution is
their exact specialization and full replay for the four Higman relators.
No claim of global novelty is made.

The all-dimensions word certificate and the four-seam gluing conclusion
remain unproved. Current primary-source status checks are recorded in
the linked U(3) artifact. No finite-dimensional calculation here replaces
those missing hypotheses or proves nonhyperlinear existence.

# The certified outer atlas quotient has a large phase-moving tangent space

Date: 2026-08-11

## Result

The exact outer \(A_8\) quotient from
`notes/FALSE_ATLAS_CERTIFIED_A8_QUOTIENT.md` kills all 24 currently certified
zero classes while retaining phase class `11` as a nonidentity involution.
It is not an isolated or infinitesimally rigid solution of the 24 matrix
equations.

In an exact outer-stable \(30\)-dimensional permutation model, let
\(J_0\) be the linearization of the 24 zero relations with respect to the
relative chart unitary.  Then

\[
 \operatorname{rank}_{\mathbb Q}J_0=764,
 \qquad
 \dim_{\mathbb C}\ker J_0=900-764=136.              \tag{OT1}
\]

If \(D_r\) is the derivative of phase class `11`, then

\[
 \operatorname{rank}_{\mathbb Q}
 \begin{bmatrix}J_0\\D_r\end{bmatrix}=824,
 \qquad
 \operatorname{rank}(D_r|_{\ker J_0})=60.           \tag{OT2}
\]

The obvious chart-commutant gauge space has dimension only \(8\), and its
directions do not move the phase.  Thus at least \(128\) tangent dimensions
are nongauge, and their phase variations span a \(60\)-dimensional space.

This gives a rigorous positive deformation signal: the certified-zero
package does not even infinitesimally pin the phase to its finite
\(A_8\)-conjugacy class.  It does not prove that a nonlinear deformation can
make the phase central or scalar; second-order obstructions may remain.

## The outer-stable model

Identify \(A_8\) with \(GL_4(\mathbb F _2)\).  Let \(\sigma\) be its
permutation representation on the 15 nonzero vectors of
\(\mathbb F _2^4\), and let

\[
 \theta(g)=(g^{-1})^{\mathsf T},
 \qquad
 \rho(g)=\sigma(g)\oplus\sigma(\theta(g))            \tag{OT3}
\]

on \(V=\mathbb C^{30}\).  The block swap implements \(\theta\) in this
outer-stable representation.  For the exact alignment matrix

```text
00000100010000000001000000000001
```

the relative unitary \(U_0\) implements the phase-preserving outer quotient

\[
 g_1\longmapsto g,
 \qquad
 g_2\longmapsto h\theta(g)h^{-1}.                   \tag{OT4}
\]

Direct permutation evaluation verifies that all 24 zero representatives
are identity and that phase class `11` is an involution different from the
identity.

## Linearization formula

Fix the first chart and write the second as

\[
 \rho_{2,U}(g)=U\rho(g)U^{-1}.
\]

For \(U(t)=e^{tX}U_0\), evaluate a word as

\[
 w(U_0)=A_1A_2\cdots A_k,
 \qquad P_j=A_1\cdots A_j,
 \qquad P_0=1.
\]

Only second-chart syllables vary.  Right-trivializing the derivative gives
the exact telescoping formula

\[
 D_w(X)=
 \sum_{\substack{1\leq j\leq k\\A_j\text{ from chart }2}}
 \left(\operatorname{Ad}(P_{j-1})-
       \operatorname{Ad}(P_j)\right)X.              \tag{OT5}
\]

Every \(P_j\) is a permutation matrix.  Therefore `(OT5)` has integer
coefficients on the matrix-unit basis of \(\operatorname{End}(V)\).  The
script forms the exact Gram matrices \(J_0^*J_0\) and
\(J_0^*J_0+D_r^*D_r\).  GAP row reduction over \(\mathbb Q\) gives the two
ranks in `(OT1)--(OT2)`.  Independent reductions modulo \(1000003\) and
\(1000033\) give the same ranks.

The calculation is stated over \(\operatorname{End}_{\mathbb C}(V)\), but
it is also the unitary tangent calculation.  The maps in `(OT5)` preserve
adjoints, their kernels are star-closed, and the complexification of the
skew-Hermitian kernel is the full complex kernel.  Hence the unitary tangent
kernel has real dimension \(136\), and the real phase-variation rank is
\(60\).

## Gauge comparison

The representation `(OT3)` is the disjoint union of the point and
hyperplane actions of \(GL_4(2)\).  Its commutant dimension is the number of
orbits on ordered pairs:

* two point--point orbits (equal and distinct);
* two hyperplane--hyperplane orbits;
* incidence and nonincidence in each of the two cross directions.

Thus

\[
 \dim\rho(A_8)'=8.                                   \tag{OT6}
\]

The aligned second chart has the same image subgroup, so left and right
chart gauge variations give this same 8-dimensional space.  Since the phase
at the base point belongs to \(\rho(A_8)\), every commutant direction has
zero phase derivative.  Equations `(OT1)--(OT2)` therefore describe genuine
relative-chart motion, not a change of basis.

## Consequence and boundary

This closes a possible negative interpretation of the exact finite
quotient: the outer solution is not a rigid isolated component forced by
the 24 zero relations.  A phase-centralizing search should work in the
\(136\)-dimensional tangent kernel and prioritize its \(60\)-dimensional
phase-moving quotient, rather than optimize over all \(U(30)\) or over a
fixed 64-dimensional irrep without using the exact-zero geometry.

The result is not a proof that class `11` survives in \(R/[P,R]\), and it
does not produce a hyperlinear nonsofic group.  A nonlinear integration
theorem, an exact central quotient, or new higher-radius relations are still
needed.

## Reproduction

The portable modular check is

```text
PYTHONPATH=experiments \
python3 experiments/atlas_certified_outer_tangent.py
```

For exact characteristic-zero ranks, emit and run the GAP calculation:

```text
PYTHONPATH=experiments \
python3 experiments/atlas_certified_outer_tangent.py --gap \
  > /tmp/atlas_outer_tangent_rank.g
/Users/user/.pixi/bin/gap -q /tmp/atlas_outer_tangent_rank.g
```

The output is

```text
zero_rank_Q 764
combined_rank_Q 824
```

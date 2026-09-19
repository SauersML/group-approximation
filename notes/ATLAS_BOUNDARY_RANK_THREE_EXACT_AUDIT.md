# Exact audit of the rank-three boundary-rigidity proposal

Date: 2026-08-12

## 1. Outcome

Let

\[
 P=A_8^{(1)}*A_8^{(2)}
\]

be the two-chart source for the binary Leavitt atlas, and let
\(\mathcal B\) be the 234 collision-tree words at the first nonclassical
boundary (half-radius five).  There is a unique inner classical alignment
\(k_0\in A_8\) for which every \(q\in\mathcal B\) evaluates to the identity.
Put

\[
 H=\{\operatorname{diag}(a,1):a\in GL_3(\mathbf F_2)\}
   \cong GL_3(2).
\]

The proposed implication

\[
 \text{all boundary relations are exact}
 \quad\Longrightarrow\quad
 \text{the relative chart unitary intertwines }H                 \tag{1}
\]

is **false**, even for finite exact models with exactly regular chart
characters.  More precisely, there is a finite group \(E\), two injective
homomorphisms

\[
 \alpha_1,\alpha_2:A_8\longrightarrow E,
\]

such that

1. every \(q\in\mathcal B\) evaluates to the identity under
   \((\alpha_1,\alpha_2)\), which is stronger than the required centrality;
2. the two charts do not agree on any of four standard transvections
   generating \(H\), after the \(k_0\)-alignment; and
3. in the left regular representation of \(E\), both chart restrictions are
   copies of the regular representation of \(A_8\).

An independent dual certificate over \(\mathbf F_2\) verifies the obstruction
without trusting the row-space discovery calculation.

This result refutes the global boundary estimate proposed in (A).  It does
not refute a boundary-plus-interior matrix rigidity theorem.  Indeed one
explicit interior centrality relation already kills the entire affine family
constructed below at the order-zero quotient level.

## 2. The signed-prefix derivatives

Identify \(A_8\) with \(GL_4(2)\).  At the aligned fold

\[
 g^{(1)}\mapsto g,
 \qquad
 g^{(2)}\mapsto k_0gk_0^{-1},                         \tag{2}
\]

every word \(q\in\mathcal B\) has value one.  Its right-trivialized
characteristic-two derivative is an element

\[
 d_q=\sum_{j:\,\text{the }j\text{-th syllable is in chart }2}
       (p_{j-1}+p_j)
       \in\mathbf F_2[A_8],                            \tag{3}
\]

where \(p_j\) is the aligned prefix through syllable \(j\).  Let

\[
 I=\sum_{q\in\mathcal B}\mathbf F_2[A_8]d_q           \tag{4}
\]

be the generated left ideal, and put

\[
 M=\mathbf F_2[A_8]/I,
 \qquad m=1+I.                                        \tag{5}
\]

The exact left-ideal closure calculation gives

\[
 \dim_{\mathbf F_2} I=20005,
 \qquad
 \dim_{\mathbf F_2}M=155.                             \tag{6}
\]

The dimension in (6) is useful for identifying the model, but it is not
needed for the logical counterexample.  Finiteness follows already from
\(M\) being a quotient of the finite-dimensional group algebra.

For the four adjacent transvections

\[
 h=I+E_{01},\ I+E_{10},\ I+E_{12},\ I+E_{21},         \tag{7}
\]

the calculation gives

\[
 (1+h)m\ne0.                                          \tag{8}
\]

There is a direct certificate for (8).  A Boolean functional

\[
 \ell:\mathbf F_2[A_8]\longrightarrow\mathbf F_2
\]

with support 9408 satisfies

\[
 \ell(xd_q)=0
 \quad(x\in A_8,\ q\in\mathcal B),
 \qquad
 \ell(1+h)=1                                          \tag{9}
\]

for each of the four choices in (7).  Thus \(1+h\notin I\) independently
of any rank computation.

## 3. The finite countermodel

Form the semidirect product

\[
 E=M\rtimes A_8,
 \qquad
 (a,g)(b,h)=(a+gb,gh).                                \tag{10}
\]

Let

\[
 \alpha_1(g)=(0,g),
 \qquad
 u=(m,k_0),
 \qquad
 \alpha_2(g)=u(0,g)u^{-1}.                            \tag{11}
\]

Both chart maps are injective because their projections to \(A_8\) are an
automorphism.  Expanding (11) in characteristic two gives

\[
 \alpha_2(g)
 =\bigl((1+k_0gk_0^{-1})m,\ k_0gk_0^{-1}\bigr).       \tag{12}
\]

For a boundary word \(q\), its \(A_8\)-coordinate is one by (2), and its
\(M\)-coordinate is exactly \(d_qm\).  Equations (4)--(5) therefore give

\[
 q(\alpha_1,\alpha_2)=1_E
 \qquad(q\in\mathcal B).                              \tag{13}
\]

On the other hand, separating the inner alignment from the affine part
leaves the element \(v=(m,1)\).  For \(h\) in (7), its commutator with the
first chart has translation coordinate \((1+h)m\), up to multiplication by
an invertible group element.  Equation (8) gives

\[
 [v,\alpha_1(h)]\ne1.                                 \tag{14}
\]

Thus (13) and (14) contradict (1).

The computed dimension (6) gives

\[
 |E|=2^{155}\,|A_8|=2^{155}\cdot20160.                \tag{15}
\]

Finally, for either chart subgroup \(A_i=\alpha_i(A_8)\),

\[
 \operatorname{Res}^{E}_{A_i}\lambda_E
 \cong [E:A_i]\lambda_{A_8}
 =2^{155}\lambda_{A_8}.                               \tag{16}
\]

Hence this is an exact counterexample in precisely the regular-margin
representation sector used by the atlas criterion.

## 4. Why the first interior relation kills this family

Collision-tree word 19243 has length eight.  Under (2) its value is an
involution \(c\ne1\), and the chart-one generator `p1_12` satisfies

\[
 [p1\_12,c]\ne1.                                      \tag{17}
\]

The normalized Hilbert--Schmidt defect of this commutator in the regular
representation of \(A_8\) is \(\sqrt2\).

More importantly, (17) survives every affine deformation of the fixed
order-zero fold (2).  In any extension \(V\rtimes A_8\), the projection of
the centrality commutator of word 19243 is exactly \([p1\_12,c]\).  No
choice of translation cocycle can make that commutator trivial.  Therefore
the one interior relation kills the whole affine family (10)--(12), not
merely the particular 155-dimensional quotient.

This is not a classification of arbitrary solutions: a different
order-zero finite quotient or a genuinely tracial/CE solution need not
project to the fold (2).

## 5. Exhaustion of the natural \(A_9\) and \(A_{10}\) overgroups

There is a second exact check which is independent of the affine module
construction.  Embed \(A_8\) as a point stabilizer in \(A_9\), fix the
first labeled chart, and conjugate the second chart by every element of
\(S_9\).  Odd conjugators are included, so the scan also covers the outer
labeling of the second \(A_8\).  These are all \(9!=362880\) labeled
two-chart positions in the natural point-stabilizer geometry.

The group generated by the two point stabilizers is either \(A_8\) or
\(A_9\), hence is centerless.  In this geometry a required centrality word
is therefore central exactly when it is the identity.  Exact exhaustive
evaluation gives

\[
 \#\{k\in S_9:q(k)=1\text{ for all }q\in\mathcal B\}=1.              \tag{18}
\]

The unique survivor fixes the ninth point and is the already known
classical alignment.  Adding only the centrality word at collision index
19243 leaves no survivor:

\[
 \#\{k\in S_9:q(k)=1\text{ for all }q\in
        \mathcal B\cup\{q_{19243}\}\}=0.                            \tag{19}
\]

Thus the boundary-plus-one-interior packet has no exact model in the full
natural \(A_9\) point-stabilizer family.  This closes one finite geometry;
it is not a classification of arbitrary finite-dimensional or
Connes-embeddable tracial solutions.

The next natural geometry gives the same result.  Let the two copies of
\(A_8\) act on eight-point supports in \(A_{10}\).  Quotienting conjugators
by the order-two centralizer of the base chart leaves
\(10!/2=1814400\) distinct labeled second charts.  Exhaustive evaluation
again finds exactly one boundary survivor, the classical alignment on the
same eight-point support, and no survivor after adding word 19243.

The first-boundary-failure histograms in degrees nine and ten agree after
accounting for the extra conjugators which fail the zeroth word.  In
particular, every \(A_{10}\) chart with a different eight-point support is
already rejected by the first boundary word.  This suggests a symbolic
support-coincidence lemma for natural alternating overgroups; that lemma is
not asserted here beyond the two exhaustively checked degrees.

## 6. A necessary correction to the SOS strategy

The full atlas presentation always has an exact tracial model: its group
von Neumann algebra with the regular trace.  Consequently no ordinary
noncommutative sum-of-squares identity, valid in every finite tracial von
Neumann algebra, can prove the desired contradiction.  Such an identity
would also hold in the regular group von Neumann algebra, where all defining
relations vanish exactly while every nontrivial group word has positive
\(L^2\)-distance from one.

The sought inequality must therefore distinguish **Connes-embeddable**
tracial algebras from arbitrary finite tracial algebras.  Equivalently, it
must be a matrix/\(R^\omega\)-valid separation of the kind appearing in
nonlocal-game correlation gaps, not a universal algebraic positivity
certificate.  This is why a global polynomial SOS search, without a
matrix-specific ingredient, cannot finish nonhyperlinearity.

## 7. The five-word packet is rigid in the smallest simple ambient group

There is nevertheless a useful exact positive result for the compressed
indices

\[
 0,\ 11,\ 30,\ 44,\ 55.
 \tag{20}
\]

Transport the second copy through \(k_0\), so that all five words lie in
\(H_1*H_2\).  Fix the first standard embedding \(H<GL_4(2)\), and for
each \(c\in GL_4(2)\) map the second copy by

\[
 h\longmapsto chc^{-1}.
 \tag{21}
\]

Exhaustive exact evaluation over all \(20160\) choices of \(c\) gives

\[
 \#\{c:\text{all five words in (20) vanish under (21)}\}=1.
 \tag{22}
\]

For the unique solution the two copies of \(H\) coincide, and the generated
image has order \(168\).  In particular there is no finite \(A_8\)-image of
the five-relator quotient which separates the two copies.

This does not prove that the abstract quotient is \(H\).  Its rational
linearization is already known to have full rank while its two-primary
linearization retains residue, so an infinite or more complicated perfect
quotient is not excluded.  A bounded Todd--Coxeter calculation and a
low-index search through degree twelve did not terminate; neither timeout is
used as evidence.  The durable statement is only the exhaustive finite
certificate `(22)`.

The replayable scan is

```text
python3 experiments/atlas_boundary_h_finite_quotient_scan.py
```

with archived output in
`experiments/atlas-boundary-h-finite-quotient-scan.json`.

The live finite-window target is now:

> Find a finite boundary-plus-interior packet for which every
> Connes-embeddable regular-margin solution is impossible, while the regular
> von Neumann algebra of the presented group remains the unavoidable
> non-CE exact solution.

There is now a computation-free reason the earlier finite-central-extension
route cannot mediate this separation.  The natural kernel

\[
 \ker(A_8*A_8\to A_8*_H A_8)
\]

is relatively perfect, while the genuine Leavitt quotient is an explicit
exact branch in which the two aligned copies of \(H\) remain distinct.
Therefore the genuine boundary group has noncentral kernel over the amalgam.
The proof, together with the resulting finite-coefficient Leavitt extraction
target, is recorded in
`ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md`.

## 7. Replayable artifacts

Discovery and independent verification:

```text
experiments/atlas_boundary_f2_bridge_ideal.py
experiments/atlas_boundary_f2_bridge_witness_verify.py
experiments/atlas-boundary-f2-bridge-ideal.json
```

The independent verifier reconstructs all 234 derivatives and checks (9)
against every left translate.  Its output is

```text
certificate_verified=true
group_order=20160
functional_support_size=9408
boundary_words_annihilated_with_all_left_translates=234
bridge_pairings=[1,1,1,1]
```

The fixed interior obstruction is generated by

```text
experiments/atlas_interior_single_bridge.py
experiments/atlas-interior-single-bridge.json
```

The exhaustive natural-overgroup scan is generated by

```text
experiments/atlas_a9_two_chart_scan.py
experiments/atlas-a9-two-chart-scan-v2.json
experiments/atlas-a10-two-chart-scan.json
```

The recorded outputs check respectively \(362880\) and \(1814400\) distinct
labeled charts, report one boundary survivor and zero boundary-plus-interior
survivors in each degree, and record `timed_out=false`.

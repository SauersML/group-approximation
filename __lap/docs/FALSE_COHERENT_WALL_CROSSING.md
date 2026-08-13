# Coherent wall crossing for the shortest Leavitt-atlas parity window

Date: 2026-08-11

## 1. Scope

Let

\[
 P=A_{8,1}*A_{8,2}\longrightarrow
 L_{\mathbb F _2}(1,2)^\times
\]

be the explicit two-chart atlas map.  The complete half-radius-five
collision tree contains 234 words on which the tensor flip has a nontrivial
factor projection.  This note isolates the shortest one-sided part of that
boundary and gives an exact coherent repair of all but one inverse-pair.

The result is not a model of the complete radius-ten window.  Its value is
that it replaces 34 apparently separate parity relations by one exact
residual pair, while retaining honest (A_8) charts throughout.  The
specific Pauli phase which originally motivated the calculation is now
known to die in the full universal central cover; see Section 5.

All enumerations below are reproduced by
`experiments/atlas_clifford_window_search.py`.  The decisive matrix
identities are independently certified over the rational Gaussian group
algebra by `experiments/atlas_clifford_window_certificate.py`.

## 2. Every shortest one-sided failure is a parity triple

Among the 234 tensor-flip failures there are exactly 34 reduced words of
length six with inversion number three and precisely one trivial factor
projection.  In each such word, the three letters from the factor with
nontrivial projection are the same involution (b).  Write the other three
letters, in occurrence order, as (a_0,a_1,a_2).  Then

\[
 a_0a_1a_2=1.                                      \tag{1}
\]

Up to whether the alternating word begins with (a_0) or (b), its three
vertices are

\[
 (b,a_0),\qquad (b,a_0a_1),\qquad (b,1).           \tag{2}
\]

They record the three conjugates of (b) whose product is the kernel word.
Thus every shortest failure is a three-uniform parity edge.

After duplicate edges are removed, the exact incidence data are:

| repeated factor | raw words | distinct edges | vertices | component sizes | incidence rank over \(\mathbb F_2\) | nullity |
|---:|---:|---:|---:|:---|---:|---:|
| 1 | 22 | 14 | 24 | \(5,5,7,7\) | 14 | 10 |
| 2 | 12 | 10 | 20 | \(4,4,6,6\) | 10 | 10 |

In particular, the 24 distinct edge equations are linearly independent.
The simultaneous parity object is nevertheless disconnected: it consists
of eight small components and has 20 free binary label directions.  This is
the precise finite relation module on which a future Weyl or Clifford
gluing must act.

## 3. Fourteen simultaneous classical baselines

For (k\in A_8=GL_4(2)), identify the second chart with the first by

\[
 h_2\longmapsto khk^{-1}.                           \tag{3}
\]

An exhaustive exact (4\times4) calculation gives:

**Proposition 1.** Exactly fourteen elements (k\in GL_4(2)) make all 34
shortest parity words equal to (1) under (3).

The fourteen elements have orders

\[
 2^4,\qquad 3^2,\qquad 4^4,\qquad 7^4,              \tag{4}
\]

where the exponents denote multiplicities.  They have no nontrivial common
left or right set stabilizer and generate all of (A_8).  Hence the solution
set is not a coset of a small subgroup.  It is a genuinely global collection
of compatible chamber alignments.

This proposition supplies a simultaneous phase-(+1) baseline.  It does
not retain a central witness: every shortest kernel word is literally
trivial in every one of these fourteen models.

## 4. A coherent square root crosses seven of the eight components

Let (W) be the 64-dimensional (A_8)-irrep obtained from the (S_8)
Specht module of shape ((5,2,1)), and write

\[
 \rho:A_8\longrightarrow U(W).
\]

Its character on the even cycle types of (S_8) is

\[
\begin{array}{c|rrrrrrrrrrrr}
\mu&1^8&2^2 1^4&2^4&3 1^5&3 2^2 1&3^2 1^2&4 2 1^2&4^2&5 1^3&5 3&6 2&7 1\\
\hline
\chi_W(\mu)&64&0&0&4&0&-2&0&0&-1&-1&0&1.
\end{array}                                         \tag{5}
\]

Take

\[
 k=\begin{pmatrix}
0&0&1&0\\0&1&0&0\\0&0&0&1\\1&0&0&0
\end{pmatrix},\qquad
 d=\begin{pmatrix}
1&0&0&0\\0&1&0&0\\0&0&1&0\\1&0&0&1
\end{pmatrix}.                                      \tag{6}
\]

The element (k) is one of the fourteen baselines and (d^2=1).  Therefore

\[
 U=\rho(k){I-i\rho(d)\over\sqrt2}                  \tag{7}
\]

is unitary.  Use the two honest chart representations

\[
 \rho_1(h)=\rho(h),\qquad
 \rho_2(h)=U\rho(h)U^*.                             \tag{8}
\]

**Theorem 2 (exact coherent wall crossing).** In the model (8), 32 of the
34 shortest parity words act exactly as (I_W).  The only exceptions are
one word and its inverse.  For either exceptional word (q_\partial),

\[
 \operatorname{tr}_{64}(\rho(q_\partial))={1\over4},\qquad
 \left\|\rho(q_\partial)-{1\over4}I\right\|_2^2
 ={15\over16}.                                      \tag{9}
\]

Consequently

\[
 \|\rho(q_\partial)-I\|_2^2={3\over2}.             \tag{10}
\]

Because the first (A_8)-chart is irreducible on (W), its commutant is
scalar.  Equation (9) is therefore an exact obstruction to centrality, not
merely a failure of a chosen scalar phase.

**Proof.**  Put (D=\rho(d)).  Since (D^2=I), (7) is unitary.  For every
(h\in A_8), conjugation expands without square roots:

\[
 {I-iD\over\sqrt2}\rho(h){I+iD\over\sqrt2}
 ={1\over2}\bigl(\rho(h)+D\rho(h)D
                 +i\rho(h)D-iD\rho(h)\bigr).       \tag{11}
\]

Thus every six-letter word has coefficients in \(\mathbb Q(i)[A_8]\).
For its exact group-algebra value (a), put

\[
 c={1\over64}\sum_g a_g\chi_W(g).                  \tag{12}
\]

Then

\[
 \|\rho(a)-cI\|_2^2
 ={1\over64}\sum_{g,h}\overline{(a-c)_g}(a-c)_h
                   \chi_W(g^{-1}h).                \tag{13}
\]

Substituting the 34 exact word expansions into (13), using (5), gives zero
for 32 words.  In all 32 cases (12) equals (1).  For the remaining inverse
pair, (12) is (1/4) and (13) is (15/16).  Every term in this calculation
is a rational Gaussian number.  The certificate script performs precisely
(11)--(13) with `Fraction` arithmetic and returns the two indices `4,5`.
End proof.

The square root (7) is not an arbitrary numerical perturbation.  It is the
quarter-turn between two exact classical walls: if (k) and (kd) are
the corresponding endpoints, then (U) is their coherent superposition in
the (d)-eigenspaces.

## 5. Global regrading: this is a finite-window diagnostic, not a witness

At the level of the truncated 34-word system, the local Pauli block in
`FALSE_LOCAL_CLIFFORD_ATLAS.md` and Theorem 2 are complementary:

* the Pauli block retains a nontrivial phase on one parity edge but, by
  itself, does not centralize the other shortest edges;
* the coherent wall crossing centralizes 32 shortest words exactly but gives
  them phase (+1), and leaves one inverse-pair macroscopically noncentral.

Multiplying (7) by the opposite square root of the same (d) repairs the
last pair only by returning to a classical alignment.  Indeed the two
quarter-turns cancel, while repeating the same quarter-turn gives, up to a
scalar, the other classical endpoint (kd).  Thus a second scalar square
root in the same wall direction cannot retain a central phase.

However, `FALSE_CLIFFORD_TORSION_GATE.md` proves a stronger global fact.  A
common six-leaf superperfect chart first kills the three commutator signs and
reduces the local phase to an involution.  An eight-leaf refinement has a
perfect four-leaf overlap with that chart, forcing the remaining lift of
(b) to agree.  Consequently the local parity word satisfies

\[
 q=1\quad\text{in }P/[P,R].                          \tag{14}
\]

Therefore no multiplicity fusion is allowed to retain its Pauli phase in a
full atlas model.  Theorem 2 remains useful as an exact description of the
shortest boundary geometry and as a regression test: truncated centrality
can create convincing nontrivial Clifford sectors even when the proposed
central class is globally zero.  A live FALSE witness must be chosen among
cross-chart words which survive the superperfect/perfect-overlap scanner.

The complete boundary classification, including the 178 explicit deaths
and the all-depth positive-cardinality obstruction for the 56 remaining
words, is recorded separately in `FALSE_ATLAS_PERFECT_OVERLAP_SCAN.md`.

## 6. A unique classical alignment repairs the entire boundary

The 56 intrinsically cross-chart words are not mutually inconsistent.
There is a single inner alignment of the two (A_8) charts which kills not
only those words but the entire 234-word tensor-flip boundary.

Let

\[
 k=\begin{pmatrix}
 0&0&1&0\\
 0&1&0&0\\
 1&0&0&0\\
 0&0&0&1
 \end{pmatrix}\in GL_4(\mathbb F_2).                 \tag{15}
\]

Thus (k) interchanges the first and third basis vectors.  Identify the
two chart factors by

\[
 h_1\longmapsto h,\qquad h_2\longmapsto khk^{-1}.     \tag{16}
\]

**Theorem 3 (unique boundary alignment).** Every one of the 234 boundary
words evaluates to the identity under (16).  Moreover, (15) is the unique
element of (GL_4(\mathbb F_2)) with this property.

The statement is an exhaustive exact calculation over \(\mathbb F_2\):
`experiments/atlas_boundary_inner_alignment.py` enumerates all 20,160
alignments.  On the complete radius-five collision tree, containing 27,256
kernel words, (16) kills 20,862 and fails on 6,394.  It is therefore a
perfect repair of the tensor-flip boundary, not a representation of the
whole radius-five quotient window.

The alignment gives a finite identity quotient of the survivor package in
which both local (GL_3(2)) factors remain faithful: (k) itself lies in
that (GL_3(2)), and the two factor maps differ by its inner automorphism.
This proves global consistency of all eight survivor classes and shows that
their phase analysis is a deformation problem around one rigid classical
point.  It does not show that their classes vanish in (R/[P,R]); the map
in (16) is a quotient of the local relation package, not a lift of the full
Leavitt atlas.

There is an immediate analytic no-go for the most literal use of the two
complementary models.  Let a block sum put normalized dimension weight
(t) on the tensor flip and (1-t) on the alignment (16).  Choose any
boundary word.  The alignment kills it, whereas the tensor flip gives it a
nontrivial projection in at least one centerless (A_8) factor; one of the
twelve generator commutators therefore has squared normalized-HS defect
(2t).  Conversely, among the 6,394 interior words not killed by (16),
choose one and then a chart generator not commuting with its nonidentity
regular image.  The tensor flip kills this word, while that commutator has
squared defect (2(1-t)) on the alignment block.  Consequently every such
block sum satisfies

\[
 \max_{c\in\mathcal C_5}\|\pi(c)-1\|_2
 \geq\sqrt{2\max\{t,1-t\}}\geq1.                    \tag{17}
\]

Thus ordinary orthogonal mixing cannot combine the complementary exact
solutions.  Any useful fusion must couple their subspaces nonorthogonally
or leave this two-model span.

## 7. The canonical spectral bridge is transverse but still rigid

There is a canonical genuinely coupled interpolation between the two
endpoints.  On the regular representation put

\[
 W=L_k^*J.
\]

Since \(k^2=1\), one has \(W^2=C_k\) and \(W^4=1\).  Functional calculus
therefore makes

\[
 U_t=L_kW^t,\qquad 0\leq t\leq1,                     \tag{18}
\]

an explicit four-term polynomial in \(W\), with \(U_0=L_k\) and \(U_1=J\).
Unlike `(17)`, this is not an orthogonal mixture: each intermediate chart is
obtained by conjugating with one unitary on the same regular space.

The rank-three corner has an exact and unexpectedly clean structure.  Of
the 27,256 radius-five collision-tree words, precisely 3,012 have every
letter in

\[
 H=\operatorname{diag}(GL_3(2),1).
\]

They consist of 210 boundary words and 2,802 words with trivial factor
projections.  Exhaustive exact evaluation in \(GL_4(2)\) shows that the
alignment `(16)` kills all 3,012.  Thus none of the 6,394 failures of `(16)`
is an inconsistency internal to the rank-three corner: every failure uses a
letter transverse to \(H\).

The spectral interpolation `(18)` nevertheless fails the first joint gate.
The complete 168-dimensional regular calculation on \(H\) gives the following
maximum boundary defects at
\(t=0,1/8,1/4,3/8,1/2,5/8,3/4,7/8,1\):

\[
 0, .97739, 1.41862, 1.41595, 1.39743,
 1.42384, 1.40655, 1.40995, \sqrt2.              \tag{19}
\]

On the full 20,160-dimensional regular representation, a deterministic
two-probe calculation using a shortest boundary word and the shortest
transverse interior word gives, at
\(t=0,1/4,1/2,3/4,1\), respectively,

\[
\begin{array}{c|ccccc}
t&0&1/4&1/2&3/4&1\\ \hline
\text{boundary}&0&1.25569&1.41391&1.38618&1.41544\\
\text{transverse}&1.41691&1.40385&1.36479&1.30868&0.
\end{array}                                         \tag{20}
\]

The endpoint values in `(20)` are exactly \(0\) and \(\sqrt2\); the small
deviation shown is the two-probe trace estimator.  The intermediate entries
are a numerical diagnostic, not a certified continuum lower bound.
Nevertheless, `(19)--(20)` rule out the most canonical spectral square-root
candidate: it moves the boundary obstruction into the regular space rather
than transferring it into a central phase.

`experiments/atlas_spectral_bridge_search.py` reproduces the exact corner
enumeration and the full-regular diagnostic.  A live nonorthogonal fusion
must use multiplicity degrees of freedom not generated by functional
calculus of \(L_k^*J\).

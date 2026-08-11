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

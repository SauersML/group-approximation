# A local Clifford sector in the binary Leavitt atlas

Date: 2026-08-11

## 1. The first failing tensor-flip word is a parity word

Let

\[
 P=K_1*K_2,\qquad K=GL_4(\mathbb F _2)\cong A_8,
\]

and use the two binary-prefix charts from
FALSE_RECURSIVE_ATLAS_EXHAUSTION.md. Inside the upper-left \(2\times2\)
block of \(K\), put

\[
 s=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
 t=\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
 r=(st)^{-1}=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
 b=\begin{pmatrix}1&1\\0&1\end{pmatrix},             \tag{1}
\]

with an identity block on the last two coordinates. Thus \(s,t,b\) are
involutions, \(st\) has order three, and \(str=1\). Consider

\[
 q=s_1b_2t_1b_2r_1b_2\in K_1*K_2.                    \tag{2}
\]

**Lemma 1.** The word \(q\) belongs to the exact Leavitt kernel
\(R=\ker(P\to L_{\mathbb F _2}(1,2)^\times)\).

**Proof.** This is one of the length-six representatives first exposed by
the complete half-radius-five collision tree. There is also a short direct
prefix certificate. The two chart leaf sets are

\[
 (01,1,000,001),\qquad (00,1,010,011).                \tag{3}
\]

Multiplication of the six corresponding leaf matrices reduces (2) to the
following nine monomials:

\[
\begin{aligned}
 &000(000)^*+001(001)^*+010(010)^*+011(011)^*\\
 &\quad+10(10)^*+11(11)^*\\
 &\quad+01(1)^*+010(10)^*+011(11)^* .                \tag{4}
\end{aligned}
\]

The last line is zero in characteristic two, because

\[
 01(1)^*=010(10)^*+011(11)^* .                       \tag{5}
\]

Refining the two length-two diagonal terms in the first two lines gives all
eight depth-three diagonal matrix units. Their sum is \(1\). Hence (4)
is exactly \(1\), proving \(q\in R\). End proof.

Define three conjugates of the second-chart involution

\[
 p_0=b_2,\qquad p_1=s_1b_2s_1^{-1},\qquad
 p_2=(s_1t_1)b_2(s_1t_1)^{-1}.                       \tag{6}
\]

Since \(str=1\), equation (2) becomes

\[
 q=p_1p_2p_0.                                        \tag{7}
\]

In the Leavitt quotient, Lemma 1 and \(p_j^2=1\) imply that the \(p_j\)
commute: from \(p_1p_2p_0=1\), one has \(p_0=p_2p_1\), and \(p_0^2=1\)
gives \(p_1p_2=p_2p_1\); the remaining commutations follow. Thus the image
of (6) is a Klein four group.

In the universal central atlas cover

\[
 U=P/[P,R],                                           \tag{8}
\]

both \(q\) and the three pairwise commutators of the \(p_j\) are central.
This permits a different lift: the three involutions may anticommute, with
their product a central fourth root of unity.

## 2. The two-dimensional Pauli lift

Let \(X,Y,Z\) be the Pauli matrices and put

\[
 S={X+Y\over\sqrt2},\qquad T=-{X+Z\over\sqrt2}.       \tag{9}
\]

They are self-adjoint involutions and

\[
 (ST)^3=1.                                            \tag{10}
\]

Hence \(s\mapsto S,t\mapsto T\) is the standard two-dimensional
representation \(\sigma\) of the first \(S_3=\langle s,t\rangle\). Give
the selected transposition \(b\) in the second \(S_3\) the value \(X\). It
can be completed to the standard representation of that \(S_3\), since
every trace-zero self-adjoint involution is unitarily conjugate to the image
of a transposition in \(\sigma\).

Conjugation in (9) gives

\[
 p_0\mapsto X,\qquad p_1\mapsto Y,\qquad p_2\mapsto-Z.\tag{11}
\]

Consequently

\[
 q\mapsto-iI_2,\qquad [p_i,p_j]\mapsto-I_2
 \quad(i\ne j).                                      \tag{12}
\]

This is an honest representation of the free product \(S_3*S_3\). The
projective behavior occurs only after passing to the Klein-four quotient:
its three commuting involutions have become a Clifford triple.

## 3. Extension to two honest \(A_8\) charts

The Pauli block is not confined to a representation of the small subgroup.
It extends to a pair of honest \(A_8\) representations.

Let \(W\) be the irreducible \(64\)-dimensional representation of \(A_8\)
obtained by restricting the \(S_8\) Specht module of shape \((5,2,1)\).
For the embedded \(S_3\leq GL_4(2)\) above, its involutions are transvections
and its elements of order three have two-dimensional fixed space. Under
\(GL_4(2)\cong A_8\), these are respectively the cycle classes
\(2^4\) and \(3^2 1^2\): their class sizes are \(105\) and \(1120\).
Murnaghan--Nakayama gives

\[
 \chi_W(1)=64,\qquad \chi_W(2^4)=0,\qquad
 \chi_W(3^2 1^2)=-2.                                 \tag{13}
\]

Taking inner products with the three characters of \(S_3\) yields

\[
 \operatorname{Res}^{A_8}_{S_3}W
   \cong10\,\mathbf1\oplus10\,\mathrm{sgn}
                 \oplus22\,\sigma.                  \tag{14}
\]

Put

\[
 \alpha=12\,\mathbf1\oplus10\,\sigma .               \tag{15}
\]

Since

\[
 \sigma\otimes\sigma
   \cong\mathbf1\oplus\mathrm{sgn}\oplus\sigma,
\]

equations (14)--(15) give

\[
 \sigma\otimes\alpha
   \cong10\,\mathbf1\oplus10\,\mathrm{sgn}
                 \oplus22\,\sigma.                  \tag{16}
\]

We may therefore realize the restriction of a first copy of \(W\) as
\(\sigma\otimes\alpha\) on
\(\mathbb C^2\otimes\mathbb C^{32}\). For a second copy of \(W\), (13)
says that the chosen transposition has trace zero. Its \(+1\) and \(-1\)
eigenspaces both have dimension \(32\), so after a unitary change of basis
we may arrange

\[
 \rho_2(b)=X\otimes I_{32}.                           \tag{17}
\]

Use (9) on the \(\sigma\) tensor factor of the first chart. Equations
(11)--(12) are unchanged on tensoring by \(\alpha\). We have proved:

**Theorem 2 (exact local Clifford atlas block).** There are honest
representations

\[
 \rho_1,\rho_2:A_8\longrightarrow U(64),             \tag{18}
\]

both equivalent to \(W\), whose free-product representation satisfies

\[
 \rho(q)=-iI_{64},\qquad
 \rho([p_i,p_j])=-I_{64}\quad(i\ne j).               \tag{19}
\]

In particular, every centrality constraint

\[
 [x,q],\qquad [x,[p_i,p_j]]\qquad(x\in K_1\cup K_2) \tag{20}
\]

is satisfied exactly. The block retains the central phase on all of its
dimension; it is neither monomial nor a small-rank perturbation of the
tensor flip.

## 4. The irreducible Clifford sector is forced

The \(64\)-dimensional choice is not accidental.

**Proposition 3.** Suppose a representation of the two local \(S_3\)
subgroups has \(q=\pm i\), has the three \(p_j\) pairwise anticommuting, and
both subgroup actions extend irreducibly to \(A_8\) on that central spectral
sector. Then both \(A_8\) representations are equivalent to \(W\).

**Proof.** Anticommutation with \(p_0=b_2\) gives

\[
 \operatorname{Tr}(p_0)
 =\operatorname{Tr}(p_1p_0p_1^{-1})
 =-\operatorname{Tr}(p_0)=0.                         \tag{21}
\]

Thus the character of the second \(A_8\) representation vanishes on the
transvection class \(2^4\). The irreducible \(A_8\) character table, obtained
equally by restricting the paired \(S_8\) Specht characters and splitting
the two self-conjugate shapes, has exactly one row which vanishes on this
class: the \(64\)-dimensional row \((5,2,1)\). Hence the second chart is
\(W\). The first irreducible chart acts on the same \(64\)-dimensional
space, and \(W\) is the unique irreducible \(A_8\) representation of that
dimension. End proof.

Therefore every irreducible full-chart realization of this Clifford sign
passes through the same \(64\)-dimensional sector. Reducible constructions
may combine sectors with cancelling transvection characters, but there is no
second irreducible seed to search for.

## 5. An exact regular-character block with surviving phase

All other irreducible \(A_8\) sectors admit a phase-\(1\) realization of the
same local relation. This follows from a small branching calculation.

Write the irreducible \(S_4\) representations as

\[
 1,\quad\varepsilon,\quad v,\quad v\varepsilon,\quad u
\]

of dimensions \(1,1,3,3,2\), respectively. Restriction to a point
stabilizer \(S_3<S_4\) and evaluation at a double transposition give

\[
\begin{array}{c|ccccc}
 &1&\varepsilon&v&v\varepsilon&u\\ \hline
\operatorname{Res}_{S_3}
 &1&\mathrm{sgn}&1+\sigma&\mathrm{sgn}+\sigma&\sigma\\
\chi(2^2)&1&1&-1&-1&2 .
\end{array}                                           \tag{22}
\]

If an \(A_8\) representation restricts to

\[
 m_1\,1\oplus m_\varepsilon\,\mathrm{sgn}
             \oplus m_\sigma\,\sigma                 \tag{23}
\]

and has transvection character \(c\), an \(S_4\) representation with
multiplicities \((x_1,x_\varepsilon,x_v,x_{v\varepsilon},x_u)\) has the
required restriction and double-transposition trace exactly when

\[
\begin{aligned}
 m_1&=x_1+x_v,\\
 m_\varepsilon&=x_\varepsilon+x_{v\varepsilon},\\
 m_\sigma&=x_v+x_{v\varepsilon}+x_u,\\
 c&=x_1+x_\varepsilon-x_v-x_{v\varepsilon}+2x_u .
\end{aligned}                                        \tag{24}
\]

For the irreducible \(A_8\) rows, one nonnegative solution of (24) is:

\[
\begin{array}{c|r|r|r|r|c}
\dim&m_1&m_\varepsilon&m_\sigma&c&
(x_1,x_\varepsilon,x_v,x_{v\varepsilon},x_u)\\ \hline
1  &1&0&0 & 1 &(1,0,0,0,0)\\
7  &1&2&2 &-1 &(1,0,0,2,0)\\
14 &6&0&4 & 6 &(4,0,2,0,2)\\
20 &5&1&7 & 4 &(2,0,3,1,3)\\
21 &2&5&7 &-3 &(1,0,1,5,1)\\
28 &3&7&9 &-4 &(2,0,1,7,1)\\
35 &8&5&11& 3 &(5,0,3,5,3)\\
45 &6&9&15&-3 &(3,0,3,9,3)\\
56 &13&5&19&8 &(6,0,7,5,7)\\
64 &10&10&22&0&(4,0,6,10,6)\\
70 &11&13&23&-2&(6,0,5,13,5).
\end{array}                                          \tag{25}
\]

The three \(21\)-dimensional irreducibles have the same row here, and the
two \(45\)-dimensional irreducibles have the same row. Thus (25) covers all
irreducible representations of \(A_8\).

For a row \(W'\), realize the first local \(S_3\) by the corresponding
\(S_4\) representation in (25). Let its normal Klein four subgroup have
nonidentity elements \(P_0,P_1,P_2\), permuted by that \(S_3\). Equation
(22) and (24) say that \(P_0\) and the image of \(b\) in
\(\operatorname{Res}_{S_3}^{A_8}W'\) are involutions of the same dimension
and trace, hence are unitarily conjugate. Choose the second chart basis so
that they agree. Then

\[
 p_j=P_j,\qquad p_1p_2p_0=1,\qquad [p_i,p_j]=1.       \tag{26}
\]

Both local \(S_3\) actions extend to honest copies of \(W'\) by construction.
This proves:

**Proposition 4 (phase-\(1\) completion).** Every irreducible \(A_8\)
representation admits a pair of honest chart realizations on which \(q\)
and the three pairwise commutators in (6) act as \(1\).

Now decompose the regular representation as

\[
 \lambda_{A_8}\cong
 \bigoplus_{W'\in\widehat {A_8}}(\dim W')\,W'.        \tag{27}
\]

On all \(64\) copies of the \(64\)-dimensional summand \(W\), use Theorem 2.
On every other summand use Proposition 4. The direct sum has both chart
restrictions exactly equal to \(\lambda_{A_8}\), while \(q\) and all three
commutators are scalar on every common summand and therefore central in the
whole free-product image.

**Theorem 5 (canonical regular local certificate).** There is a relative
unitary \(V\in U(20160)\) between two regular \(A_8\) charts such that

\[
 [\rho(x),\rho(q)]=[\rho(x),\rho([p_i,p_j])]=1
 \quad(x\in P,\ i\ne j),                              \tag{28}
\]

and

\[
\begin{aligned}
 \|\rho(q)-1\|_2^2
   &=2\,{64^2\over20160}={128\over315},\\
 \|\rho([p_i,p_j])-1\|_2^2
   &=4\,{64^2\over20160}={256\over315}.               \tag{29}
\end{aligned}
\]

Thus the first parity relation has an exact canonical regular-chart model
which both kills its centrality defects and retains a positive normalized
Hilbert--Schmidt central witness. The witness occupies the complete
\(64\)-irrep isotypic component, of relative dimension \(64^2/20160\), not
a vanishing corner.

## 6. What this proves and what remains

Theorem 2 is a genuine finite-dimensional solution of the first local
Clifford cluster, but it is not a representation of the full group (8).
If all of \([P,R]\) vanished, it would give a nontrivial finite-dimensional
representation of \(U\), whereas the latter has only the trivial such
representation. Therefore some later kernel relation must obstruct the
extension.

The useful conclusion is now a no-go boundary. The radius-ten failure of the
commuting tensor flip does **not** impose a local positive lower bound:
Theorem 5 closes the parity word and its induced Klein-four commutators
exactly inside the canonical regular-character problem, with a positive
central witness on that truncated window.  However,
`FALSE_CLIFFORD_TORSION_GATE.md` proves that a six-leaf common chart kills
the commutator phases and a perfect four-leaf overlap through an eight-leaf
bridge kills the residual sign.  Thus \(q=1\) in the full universal central
cover.  No continuation of this local block can retain its phase while
satisfying all later relations.

## 7. Exact implementation and complete-boundary audit

`experiments/atlas_clifford_block.py` instantiates Theorem 2 using GAP's
explicit `GL_4(F_2) -> A8` isomorphism and Sage's orthogonal Young
representation of shape `(5,2,1)`.  The six-element `S3` average constructs
the tensor-factor intertwiner, and an exact-sign eigenspace match constructs
the second chart.  Numerically, the defining identities verify with
Frobenius residual below `5.4e-14`.

Scoring all 234 words at the first tensor-flip boundary gives a sharply
localized result.  This one Clifford alignment centralizes 19 words.  All
19 belong to one projection-pair class `(1,b)` containing 25 words; the six
other alternating representatives with the same pair are not centralized.
On the full boundary the RMS centrality defect is `1.3587338001` and the
maximum is `2`.  Thus projection pairs are insufficient data once the
tensor flip is deformed, exactly as anticipated in
`FALSE_RECURSIVE_ATLAS_EXHAUSTION.md`.

There is a large exact family of Clifford-preserving refinements.  Right
multiplication of the relative chart unitary by the commutant of the second
involution gives `U(32) x U(32)` and leaves the Pauli lamp image, `q=-i`,
and its three commutators unchanged.  The projected optimizer in
`atlas_clifford_refine.py` targets all 300 centrality constraints attached
to the 25-word pair class.  Over 20 worst-tail iterations it improves the
RMS defect only from `0.7189726` to `0.7162448`; the maximum remains pinned
at `2`, while the Clifford identities stay below `6e-14`.

This is numerical evidence of a rigid subconstraint inside that Pauli
manifold, while `FALSE_CLIFFORD_TORSION_GATE.md` now supplies the exact
reason the whole branch fails: the class of `q` is zero in `R/[P,R]`.
Do not run more seeds, convert the pinned constraint into a larger optimizer,
or couple additional 64-dimensional isotypic copies in an attempt to retain
this witness.  Keep the construction only as a regression test for false
positives produced by truncated centrality windows.

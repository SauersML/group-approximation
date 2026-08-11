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

## 4. What this proves and what remains

Theorem 2 is a genuine finite-dimensional solution of the first local
Clifford cluster, but it is not a representation of the full group (8).
If all of \([P,R]\) vanished, it would give a nontrivial finite-dimensional
representation of \(U\), whereas the latter has only the trivial such
representation. Therefore some later kernel relation must obstruct the
extension.

The useful change is that this obstruction is now sharply posed. The
radius-ten failure of the commuting tensor flip does **not** impose a local
positive lower bound: a macroscopic \(64\)-dimensional \(A_8\) sector closes
the parity word and its induced Klein-four commutators exactly, with the
desired central phase. The next task is to add further Clifford sectors so
that an increasing collision window is central while the accumulated
character approaches the regular \(A_8\) character. A proof that the
normalized cost of the later relations is \(o(1)\) would feed directly into
the recursive atlas criterion and produce a hyperlinear nonsofic group.


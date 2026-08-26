# Finite central-HNN hidden legs return only the edge join

## Status

This is a Cairn-only computation of the minimal two-stable-letter architecture
suggested by
`notes/FALSE_SPLIT_LEFT_RIGHT_GRAPH_TRANSDUCER_LEAKS_VALUE_AXES.md`.

The split transducer failed because its two transition legs returned to the
base separately.  The smallest Britton repair is to hide each transition
inside a conjugated copy of the base:

\[
  P^{t_1}=t_1^{-1}Pt_1,
  \qquad
  P^{t_2}=t_2^{-1}Pt_2,
\]

where each stable letter centralizes a finitely generated edge subgroup.  The
cutter

\[
  L=\langle P^{t_1},P^{t_2}\rangle
\]

is finitely generated whenever (P) is.  Its transition elements are outside
the original base unless an HNN pinch is available, so it passes the elementary
axis-leakage test.

The exact Britton computation is nevertheless negative:

\[
  \boxed{L\cap P=\langle M_1,M_2\rangle,}
\]

where (M_i) is the subgroup centralized by (t_i).  Therefore finitely
generated edges give a finitely generated base intersection.  In particular
this architecture cannot cut out the infinite-rank conjugator graph.

The proof is two applications of the proved repository theorem `Pinch.pinch`
from `GroupApproximation/Higman/Pinch.lean`.  Finite presentability and
torsion-freeness of the tower are exactly the existing results
`HNNFinitePresentation.isFinitelyPresented_hnnExtension` and
`HNNBritton.isPowerTorsionFree_hnn`.  No Lean, build, MSI, or external input
was used.

## 1. The two-stage tower

Let (P) be a group and let (M_1,M_2\leq P).  Form the central HNN extension

\[
  E_1=\langle P,t_1\mid[t_1,m]=1\ (m\in M_1)\rangle.
  \tag{1.1}
\]

Write (i_1:P\hookrightarrow E_1) for the canonical embedding.  Regard

\[
  M_2'=i_1(M_2)\leq E_1
\]

as the second edge group, and form

\[
  E_2=\langle E_1,t_2\mid[t_2,m]=1\ (m\in M_2')\rangle.
  \tag{1.2}
\]

Write (i_2:E_1\hookrightarrow E_2), and put

\[
  i=i_2i_1:P\hookrightarrow E_2.
\]

Inside (E_2), define the two hidden copies

\[
\begin{aligned}
  C_1&=i_2(t_1^{-1}i_1(P)t_1),\\
  C_2&=t_2^{-1}i(P)t_2,
\end{aligned}
\tag{1.3}
\]

and their join

\[
  L=\langle C_1,C_2\rangle.
  \tag{1.4}
\]

All displayed embeddings are injective by the HNN normal form, exposed in the
repository as `HNNExtension.of_injective`.

## 2. Exact base intersection

Put

\[
  Z=\langle M_1,M_2\rangle\leq P.
  \tag{2.1}
\]

### Theorem 2.1 — two hidden legs return exactly the edge join

In the tower (1.1)--(1.4),

\[
  \boxed{L\cap i(P)=i(Z).}
  \tag{2.2}
\]

Equivalently, in repository `comap` notation,

\[
  L\mathbin{.comap}i=M_1\vee M_2.
  \tag{2.3}
\]

### Proof: the easy inclusion

If (m\in M_1), the first HNN relation gives

\[
  t_1^{-1}i_1(m)t_1=i_1(m).
\]

After applying (i_2), the element (i(m)) belongs to (C_1\leq L).
Similarly, if (m\in M_2), the second HNN relation gives

\[
  t_2^{-1}i(m)t_2=i(m),
\]

so (i(m)\in C_2\leq L).  Hence

\[
  i(Z)\leq L\cap i(P).
  \tag{2.4}
\]

### Proof: first Britton descent

Inside (E_1), let

\[
  S_1=\langle i_1(Z),t_1^{-1}i_1(P)t_1\rangle.
  \tag{2.5}
\]

Apply `Pinch.pinch` to the central HNN extension (1.1) with

\[
  M=M_1,
  \qquad Z=\langle M_1,M_2\rangle,
  \qquad Q=P.
\]

Its two crossing hypotheses are immediate:

\[
  Q\cap M_1=M_1\leq Z,
  \qquad
  Z\cap M_1\leq P=Q.
  \tag{2.6}
\]

The conclusion of `Pinch.pinch`, together with the obvious reverse inclusion,
is

\[
  \boxed{S_1\cap i_1(P)=i_1(Z).}
  \tag{2.7}
\]

This is the first complete normal-form calculation: every word in the first
hidden copy that returns to the base collapses through (M_1), and adjoining
the already allowed subgroup (Z) creates nothing else in the base.

### Proof: second Britton descent

Inside (E_2), put

\[
  S_2=\langle i_2(S_1),t_2^{-1}i(P)t_2\rangle.
  \tag{2.8}
\]

Apply `Pinch.pinch` to the second extension (1.2) with

\[
  M=M_2'=i_1(M_2),
  \qquad Z=S_1,
  \qquad Q=i_1(P).
\]

Again the two crossing hypotheses are exact and elementary.  First,

\[
  Q\cap M_2'=M_2'\leq i_1(Z)\leq S_1,
  \tag{2.9}
\]

because (M_2\leq Z).  Second,

\[
  S_1\cap M_2'\leq i_1(P)=Q
  \tag{2.10}
\]

because \(M_2'\) itself is a subgroup of \(i_1(P)\).  Thus the second pinch
gives

\[
  \boxed{S_2\cap i_2(E_1)=i_2(S_1).}
  \tag{2.11}

The cutter (L) is contained in (S_2): its first generator subgroup (C_1)
lies in (i_2(S_1)), and its second generator subgroup is the other generator
of (2.8).  Now take (x\in L\cap i(P)).  Since (i(P)\leq i_2(E_1)), equation
(2.11) puts (x) in (i_2(S_1)).  Injectivity of (i_2) and (2.7) then put
(x) in (i(Z)).  Therefore

\[
  L\cap i(P)\leq i(Z).
  \tag{2.12}
\]

Combining (2.4) and (2.12) proves (2.2). \(\square\)

## 3. Finiteness consequence

### Corollary 3.1 — finite edges force a finite-rank return

Assume (P), (M_1), and (M_2) are finitely generated.  Then (L) is
finitely generated and (L\cap i(P)) is finitely generated.

### Proof

Each (C_i) is an isomorphic image of (P), hence finitely generated, and the
join of two finitely generated subgroups is finitely generated by
`Higman.fg_sup`.  Theorem 2.1 identifies the base intersection with
(M_1\vee M_2), which is finitely generated by another application of
`Higman.fg_sup`. \(\square\)

If (P) is finitely presented and the (M_i) are finitely generated, both HNN
extensions are finitely presented by
`HNNFinitePresentation.isFinitelyPresented_hnnExtension`.  If (P) is
torsion-free, both are torsion-free by
`HNNBritton.isPowerTorsionFree_hnn`.  Thus Corollary 3.1 is an obstruction
inside the fully compiler-valid regime; no missing permanence theorem is being
used.

## 4. Application to the conjugator graph

Take

\[
  P=D=F_3\times F_3
\]

and let

\[
  \Gamma=
  \left\langle(h^{-1}ah,h):h\in K\right\rangle
\]

be `Higman.Star.graphSub`.  The repository theorem
`Star.graphHom_injective` identifies (Gamma) with the free group on the
infinite basis indexed by (K=F(b,c)).  Hence (Gamma) is not finitely
generated.

Suppose the two edge groups (M_1,M_2\leq D) are finitely generated and the
cutter is the minimal hidden-leg cutter (1.4).  Theorem 2.1 and Corollary 3.1
give

\[
  L\cap D=M_1\vee M_2,
\]

a finitely generated subgroup.  Therefore

\[
  \boxed{L\cap D\neq\Gamma.}
  \tag{4.1}
\]

This is not the previous split-axis obstruction.  Here neither conjugated copy
of a generic base transition returns to (D) separately.  Britton reduction
is doing the synchronization.  The exact computation says that every return
is nevertheless generated by the two finite edge pinch sets, so two hidden
whole-base legs still have only finite-rank return capacity.

## 5. Finite-tower form

The same proof rules out any finite number of central hidden whole-base legs.

### Corollary 5.1 — a finite central tower returns the finite edge join

Let (M_1,\ldots,M_r\leq P).  Starting at (E_0=P), form (E_j) from
(E_{j-1}) by adjoining (t_j) centralizing the canonical image of (M_j).
In (E_r), let (C_j) be the final image of

\[
  t_j^{-1}Pt_j
\]

and put (L_r=\langle C_1,\ldots,C_r\rangle).  Then

\[
  \boxed{L_r\cap P=\langle M_1,\ldots,M_r\rangle.}
  \tag{5.1}
\]

### Proof

Let (Z=\langle M_1,\ldots,M_r\rangle\leq P).  At level zero start with
(S_0=Z).  At level (j), let

\[
  S_j=\langle S_{j-1},t_j^{-1}Pt_j\rangle
\]

inside (E_j), transporting all earlier groups through the canonical
embeddings.  Apply `Pinch.pinch` with (Q=P), edge (M_j), and
(Z=S_{j-1}).  The first crossing condition holds because

\[
  M_j\leq Z\leq S_{j-1},
\]

and the second because the edge lies in the canonical image of (P).
Therefore

\[
  S_j\cap E_{j-1}=S_{j-1}.
  \tag{5.2}
\]

Repeated descent through (5.2) gives

\[
  S_r\cap P=Z.
\]

The actual cutter (L_r) lies in (S_r), while every (M_j) lies in
(C_j\leq L_r) because (t_j) centralizes (M_j).  Hence

\[
  Z\leq L_r\cap P\leq S_r\cap P=Z,

\]

which proves (5.1). \(\square\)

For finite (r), if every (M_j) is finitely generated then the right side of
(5.1) is finitely generated.  Consequently no finite central-HNN tower of
hidden conjugated whole-base copies can cut out `Star.graphSub`.

## 6. Exact remaining design constraint

The split transition design exposed both legs in the base and leaked the value
axes.  The present design hides every leg behind a stable letter, but its only
possible base returns are central pinches, whose total contribution is the
finite join (5.1).

A successful finite-rank bridge must therefore go beyond central hidden copies.
At least one stable letter must identify two **different** finitely generated
associated subgroups, and its matched return must change state rather than
merely centralize an edge element.  Moreover, the iterated state changes must
create infinitely many graph basis elements without placing the whole graph in
an associated subgroup.  The existing `HNNDescent` and `Pinch` theorems can
verify such a construction after its finite edge maps are supplied; the
central case computed here cannot supply them.

No claim is made that `Star.graphSub` is non-benign, and noncentral finite-edge
HNN transducers remain open.

# Asymmetric HNN hidden whole-base legs still return only one edge side

## Status

This is a Cairn-only normal-form computation for the genuinely noncentral case
left open by
`notes/FALSE_FINITE_CENTRAL_HNN_HIDDEN_LEGS_RETURN_ONLY_EDGE_JOIN.md`.
No Lean, build, MSI, or literature input was used.

Let

\[
  H=\operatorname{HNN}(G;A\overset{\phi}{\longrightarrow}B)
   =\langle G,t\mid tat^{-1}=\phi(a)\ (a\in A)\rangle .
\]

The isomorphism \(\phi:A\to B\) may be arbitrary; in particular it need not
be the identity and neither edge subgroup need be central.  The exact
one-letter calculation is

\[
 \boxed{\langle Z,t^{-1}Gt\rangle\cap G=Z\quad\text{whenever }A\leq Z.}
 \tag{0.1}
\]

Thus the hidden whole-base copy \(t^{-1}Gt\) returns the **unmoved** edge side
\(A\), not an orbit closure under \(\phi\).  The opposite orientation satisfies

\[
 \boxed{\langle Z,tGt^{-1}\rangle\cap G=Z\quad\text{whenever }B\leq Z.}
 \tag{0.2}
\]

Iterating (0.1) through the minimal two-letter asymmetric tower gives

\[
 \boxed{\langle t_1^{-1}Pt_1,t_2^{-1}Pt_2\rangle\cap P=A_1\vee A_2.}
 \tag{0.3}
\]

Here the second associated pair is a pair of subgroups of the original base
copy \(P\), transported into the first HNN extension.  Consequently finite-rank
edge groups again have only finite-rank return capacity.  In particular this
two-letter architecture cannot cut out `Higman.Star.graphSub`.

The new ingredient is the asymmetric block-pinch lemma below.  Its proof uses
exactly the stable-letter convention and Britton theorem already proved in
`GroupApproximation/GroupTheory/HNNBrittonPinch.lean`:

* `HNNBritton.t_conj_of_mem`:
  \(tgt^{-1}=\phi(g)\) for \(g\in A\);
* `HNNBritton.t_inv_conj_of_mem`:
  \(t^{-1}gt=\phi^{-1}(g)\) for \(g\in B\);
* `HNNBritton.wordProd_notMem_range`: a nonempty pinch-free spelling does not
  lie in the base copy.

The block-form collection uses the same elementary closure argument as
`Higman.Pinch.exists_blockForm` in
`GroupApproximation/Higman/Pinch.lean`; unlike `Higman.Pinch.pinch`, the lemma
below does not assume a central HNN extension.

## 1. The asymmetric block-pinch lemma

Let \(Z,Q\leq G\), and put

\[
  S=\langle Z,t^{-1}Qt\rangle\leq H.
  \tag{1.1}
\]

The notation suppresses the canonical injective copy of \(G\) in \(H\).
That embedding is injective by `HNNExtension.of_injective`.

### Lemma 1.1 — exact asymmetric descent

Assume

\[
\begin{aligned}
  \phi^{-1}(Q\cap B)&\leq Z, &&\tag{1.2}\\
  \phi(Z\cap A)&\leq Q. &&\tag{1.3}
\end{aligned}
\]

Then

\[
  \boxed{S\cap G=Z.}
  \tag{1.4}
\]

Here (1.2) means: if \(q\in Q\cap B\), then
\(\phi^{-1}(q)\in Z\); (1.3) has the analogous literal meaning.  Thus there is
no ambiguity about images of intersections of subgroups with different ambient
types.

### Proof

The inclusion \(Z\leq S\cap G\) is immediate.  For the reverse inclusion,
every element of \(S\) has a block spelling

\[
 w=z_0
   (t^{-1}q_1tz_1)
   (t^{-1}q_2tz_2)\cdots
   (t^{-1}q_ktz_k),
 \tag{1.5}
\]

with \(z_i\in Z\) and \(q_i\in Q\).  This follows by induction on a product
of generators from \(Z\cup t^{-1}Qt\) and their inverses: \(Z\) and \(Q\) are
subgroups, so inverse generators have the same form; a \(Z\)-term is absorbed
into the adjacent \(z\)-entry (or into \(z_0\)), while a conjugated
\(Q\)-term starts a new block.
This is precisely the collection performed by
`Higman.Pinch.exists_list_of_mem_closure` and
`Higman.Pinch.exists_blockForm` in the central specialization; centrality is
not used in obtaining (1.5).

Induct on the number \(k\) of blocks, subject to the hypothesis \(w\in G\).
There are three exhaustive cases.

**First pinch.**  Suppose \(q_i\in B\) for some \(i\).  Repository theorem
`HNNBritton.t_inv_conj_of_mem` gives

\[
  t^{-1}q_it=\phi^{-1}(q_i).
  \tag{1.6}
\]

Since also \(q_i\in Q\), hypothesis (1.2) puts the right side in \(Z\).
Collapse this block and absorb the result into its adjacent \(Z\)-entries.
The new spelling has \(k-1\) blocks, all its \(q\)-entries still lie in \(Q\),
all its \(z\)-entries still lie in \(Z\), and represents the same \(w\).
The induction hypothesis gives \(w\in Z\).

**Crossing pinch.**  Suppose no \(q_i\) lies in \(B\), but some nonfinal
\(z_i\), \(i<k\), lies in \(A\).  The two adjacent blocks merge as

\[
\begin{aligned}
 &(t^{-1}q_it z_i)(t^{-1}q_{i+1}t z_{i+1})\\
 &\qquad=t^{-1}\bigl(q_i\,\phi(z_i)\,q_{i+1}\bigr)t z_{i+1}.
\end{aligned}
\tag{1.7}
\]

This uses `HNNBritton.t_conj_of_mem`.  By (1.3),
\(\phi(z_i)\in Q\), hence the new conjugated entry
\(q_i\phi(z_i)q_{i+1}\) is again in \(Q\).  We again have a valid block
spelling with \(k-1\) blocks, so induction gives \(w\in Z\).

**No pinch.**  Otherwise every \(q_i\notin B\), and every nonfinal
\(z_i\notin A\).  If \(k>0\), the stable-letter syllables of (1.5) are

\[
 (-1,q_1),(+1,z_1),(-1,q_2),(+1,z_2),\ldots,(-1,q_k),(+1,z_k).
 \tag{1.8}
\]

At each \((-1,+1)\) seam the base entry is outside \(B\); at each
\((+1,-1)\) seam it is outside \(A\).  There is no seam after the last
syllable.  Hence (1.8) satisfies `HNNBritton.NoPinch`.  Since it is nonempty,
`HNNBritton.wordProd_notMem_range` says that \(w\notin G\), contrary to the
hypothesis.  Therefore \(k=0\), so (1.5) is just \(w=z_0\in Z\).

Every shortening strictly lowers \(k\), so the induction terminates.  This
proves (1.4). \(\square\)

### Corollary 1.2 — a hidden whole base returns one edge side

Take \(Q=G\).  Condition (1.3) is automatic, and condition (1.2) is exactly
\(A\leq Z\), because \(\phi^{-1}(B)=A\).  Lemma 1.1 therefore proves (0.1).
Moreover

\[
  t^{-1}Gt\cap G=A:
  \tag{1.9}
\]

the inclusion from right to left is
\(a=t^{-1}\phi(a)t\), while the reverse inclusion is the
`HNNBritton.t_inv_conj_mem_range_iff` criterion.

Swapping \((A,B,\phi,t)\) with
\((B,A,\phi^{-1},t^{-1})\) gives (0.2) and

\[
  tGt^{-1}\cap G=B.
  \tag{1.10}
\]

The important point is that (0.1) is stronger than (1.9): arbitrary products
alternating between \(Z\) and the hidden copy still return no new base element.

## 2. The minimal two-letter asymmetric tower

Let \(P\) be a group.  Choose subgroups \(A_i,B_i\leq P\) and isomorphisms

\[
  \phi_i:A_i\overset{\sim}{\longrightarrow}B_i
  \qquad(i=1,2).
\]

Form

\[
 E_1=\operatorname{HNN}(P;A_1\overset{\phi_1}{\longrightarrow}B_1).
 \tag{2.1}
\]

Write \(i_1:P\hookrightarrow E_1\) and let \(t_1\) be its stable letter.
Transport \(A_2,B_2,\phi_2\) along \(i_1\), and form

\[
 E_2=\operatorname{HNN}
   (E_1;i_1(A_2)\overset{i_1\phi_2i_1^{-1}}{\longrightarrow}i_1(B_2)).
 \tag{2.2}
\]

Write \(i_2:E_1\hookrightarrow E_2\), let \(t_2\) be the second stable
letter, and identify all earlier groups with their canonical images.  Define

\[
\begin{aligned}
 C_1&=t_1^{-1}Pt_1\leq E_2,\\
 C_2&=t_2^{-1}Pt_2\leq E_2,\\
 L&=C_1\vee C_2,\\
 R&=A_1\vee A_2\leq P.
\end{aligned}
\tag{2.3}
\]

### Theorem 2.1 — exact two-letter return intersection

In the tower (2.1)--(2.3),

\[
  \boxed{L\cap P=R=A_1\vee A_2.}
  \tag{2.4}
\]

### Proof

Inside \(E_1\), put

\[
  S_1=\langle R,t_1^{-1}Pt_1\rangle.
  \tag{2.5}
\]

Since \(A_1\leq R\), Corollary 1.2 gives

\[
  S_1\cap P=R.
  \tag{2.6}
\]

Inside \(E_2\), put

\[
  S_2=\langle S_1,t_2^{-1}Pt_2\rangle.
  \tag{2.7}
\]

Apply Lemma 1.1 at the second HNN stage with base \(G=E_1\),
\(Z=S_1\), and \(Q=P\).  Its first hypothesis holds because

\[
  \phi_2^{-1}(P\cap B_2)=A_2\leq R\leq S_1.
  \tag{2.8}
\]

Its second hypothesis holds because

\[
  \phi_2(S_1\cap A_2)\leq\phi_2(A_2)=B_2\leq P=Q.
  \tag{2.9}
\]

Therefore

\[
  S_2\cap E_1=S_1.
  \tag{2.10}
\]

Now \(L\leq S_2\).  If \(x\in L\cap P\), then (2.10) puts \(x\) in
\(S_1\), and (2.6) puts \(x\) in \(R\).  Hence
\(L\cap P\leq R\).

Conversely, if \(a\in A_1\), then

\[
  a=t_1^{-1}\phi_1(a)t_1\in C_1,
\]

and if \(a\in A_2\), then

\[
  a=t_2^{-1}\phi_2(a)t_2\in C_2.
\]

Thus \(R=A_1\vee A_2\leq L\cap P\), proving (2.4). \(\square\)

This proof explicitly accounts for mixed words in both stable letters.  The
second-stage block descent first forces every return into \(S_1\); the
first-stage descent then forces it into \(R\).  A pinch carrying a label through
\(\phi_2\) stays inside the conjugated whole base \(P\), so it merges two
second-stage blocks rather than creating a new return state.  This is why
noncentrality does not increase capacity in this architecture.

## 3. Orientations and finite towers

For each stage choose one of the hidden copies

\[
  t_i^{-1}Pt_i\quad\text{or}\quad t_iPt_i^{-1}.
\]

Call its return side \(R_i=A_i\) in the first orientation and \(R_i=B_i\) in
the second.  Repeating Lemma 1.1, or its swapped form (0.2), proves the exact
finite-tower formula

\[
  \boxed{
    \left\langle P^{t_1^{\varepsilon_1}},\ldots,
                    P^{t_r^{\varepsilon_r}}\right\rangle\cap P
      =R_1\vee\cdots\vee R_r,
  }
  \tag{3.1}
\]

provided every later associated pair is transported from subgroups of the
original base \(P\).  The induction is the proof of Theorem 2.1 verbatim: at
stage \(i\), the returned side \(R_i\) is already in the seed
\(R_1\vee\cdots\vee R_r\), and the opposite side lies in the conjugated
whole-base subgroup \(Q=P\), so the two asymmetric crossing hypotheses hold.

If the edge sides are finitely generated and the tower is finite, the right
side of (3.1) is finitely generated.  This conclusion does not require the
edge maps to be central, to extend to endomorphisms of \(P\), or to preserve
any common subgroup.

This is an obstruction in the compiler-valid finiteness regime, not just an
abstract normal-form curiosity.  If \(P\) is finitely presented and the edge
sides are finitely generated, every stage of the finite tower is finitely
presented by
`HNNFinitePresentation.isFinitelyPresented_hnnExtension`.  Each hidden copy
of \(P\) is finitely generated, and its finite join is finitely generated by
`Higman.fg_sup`.  If \(P\) is torsion-free, the tower remains torsion-free by
`HNNBritton.isPowerTorsionFree_hnn`.

## 4. Capacity obstruction for the conjugator graph

Take \(P=F_3\times F_3\) and

\[
  \Gamma=
  \left\langle(h^{-1}ah,h):h\in K\right\rangle
  =\texttt{Higman.Star.graphSub}.
  \tag{4.1}
\]

Repository theorem `Star.graphHom_injective` says that the homomorphism from
the free group on the alphabet \(K\), sending the letter \(h\) to
\((h^{-1}ah,h)\), is injective.  By the definition of `Star.graphSub` as its
range, \(\Gamma\) is therefore the free group on that displayed basis.  The
alphabet \(K=\langle b,c\rangle\) is infinite, and a finite set of free-group
words uses only finitely many letters; a basis letter outside that finite
support is not in the subgroup they generate.  Hence \(\Gamma\) is not
finitely generated.  This is the same finite-support argument recorded in
`GroupApproximation/Higman/TransportStar.lean` and
`notes/TRUE_FP_HNN_FORCES_FG_EDGE_AND_INFINITE_EDGE_COMPILERS_FAIL.md`.

If both edge isomorphisms in Theorem 2.1 have finitely generated sides, then

\[
  L\cap P=A_1\vee A_2
\]

is finitely generated, and therefore cannot equal \(\Gamma\).  The same holds
for every finite tower covered by (3.1).

The obstruction is exact and deliberately narrow:

\[
 \boxed{
 \begin{gathered}
   \text{finite asymmetric HNN tower}\ +
   \text{hidden conjugates of the whole original base}\\
   \Longrightarrow
   \text{base return is the finite join of one edge side per letter.}
 \end{gathered}}
 \tag{4.2}
\]

It does **not** rule out the repository's `RowDeletionBenign.stableWitness`
pattern.  That construction adjoins the stable letter itself to finitely many
base seeds, and `HNNDescent.closure_inf_range` can then return an infinite
subgroup stable under the partial edge map.  Nor does (4.2) cover a hidden
conjugate \(t^{-1}Qt\) of a proper subgroup \(Q<P\) when the crossing
conditions (1.2)--(1.3) fail.  Lemma 1.1 identifies the precise remaining
place where a finite-rank transducer could acquire additional capacity: its
proper hidden state subgroup must fail one of those two containments, so that
successive noncentral pinches genuinely change the allowed state set.  Whole
base hidden legs cannot do so.

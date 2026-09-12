# Finite presentability forces a finitely generated HNN edge

## Status

This is a Cairn-only converse to
`HNNFinitePresentation.isFinitelyPresented_hnnExtension` and an audit of its
consequence for the remaining Higman un-conjugation leaf.

If a finitely presented group is used as the base of a one-letter HNN
extension, then the extension is finitely presented **only if** its associated
subgroup is finitely generated.  Thus the countably generated edge in
`Higman/HNNEmbedding.lean` is not merely outside the hypotheses of the
repository's finite-presentation theorem: when its base is finitely presented,
the resulting HNN extension is not finitely presented.  The same conclusion
holds for a literal HNN extension of \(F_3\times F_3\) along the whole
conjugator graph.

The proof uses only repository-internal results:

* the quotient model, relators, and finite-generation direction in
  `GroupApproximation/Algebra/HNNFinitePresentation.lean`;
* `Tietze.ker_isFinitelyNormallyGenerated` from
  `GroupApproximation/Algebra/FinitePresentationKernel.lean`;
* `Tietze.exists_finite_subset_subset_normalClosure` from
  `GroupApproximation/Algebra/FinitePresentationTietze.lean`;
* the exact pinch criterion `HNNBritton.t_conj_mem_range_iff` from
  `GroupApproximation/GroupTheory/HNNBrittonPinch.lean`;
* the free associated subgroups `HNNEmb.aEquiv`, `HNNEmb.bEquiv` from
  `GroupApproximation/Higman/HNNEmbedding.lean`;
* `Star.graphHom_injective` and the graph reduction in
  `GroupApproximation/Higman/TransportStar.lean`.

No Lean, build, MSI, or external input was used.

## 1. The converse theorem

Let \(G\) be a group, let \(A,B\leq G\), and let

\[
  \phi:A\mathbin{\cong}B
\]

be a group isomorphism.  Write

\[
  H=\operatorname{HNN}(G,A,B,\phi)
\]

with stable letter \(t\), in the repository convention

\[
  tat^{-1}=\phi(a)\qquad(a\in A).
  \tag{1.1}
\]

### Theorem 1.1 — an FP HNN extension over an FP base has an FG edge

If \(G\) and \(H\) are finitely presented, then \(A\) is finitely generated.

### Proof

Put

\[
  C=G*\langle t\rangle
\]

and, for \(a\in A\), put

\[
  r_a=t a(\phi(a)t)^{-1}=tat^{-1}\phi(a)^{-1}\in C.
  \tag{1.2}
\]

These are exactly `HNNFinitePresentation.relator`.  Let

\[
  R_A=\{r_a:a\in A\}.
\]

The canonical map

\[
  q_A:C\twoheadrightarrow H
\]

is `HNNFinitePresentation.toHNN`.  Its kernel is

\[
  \ker q_A=\langle\!\langle R_A\rangle\!\rangle_C.
  \tag{1.3}
\]

This is not an extra presentation assumption.  Mathlib defines the HNN
extension as this quotient, and the repository identifies the quotient by a
generating family of edge relators with the HNN extension in
`HNNFinitePresentation.quotientEquiv`.  Taking the generating family to be all
of \(A\) gives (1.3).  The same quotient description, or
`HNNExtension.induction_on`, gives surjectivity of \(q_A\).

The group \(C\) is finitely presented because \(G\) and the infinite cyclic
group are finitely presented and finite presentability is closed under free
products.  Since \(H\) is finitely presented,
`Tietze.ker_isFinitelyNormallyGenerated` applied to \(q_A\) gives a finite set
\(X\subseteq\ker q_A\) such that

\[
  \ker q_A=\langle\!\langle X\rangle\!\rangle_C.
  \tag{1.4}
\]

Every member of \(X\) lies in the normal closure in (1.3).  Normal generation
is compact: `Tietze.exists_finite_subset_subset_normalClosure` supplies a finite
\(R_0\subseteq R_A\) for which

\[
  X\subseteq\langle\!\langle R_0\rangle\!\rangle_C.
\]

Choose a finite set \(S\subseteq A\) containing one index for every relator in
\(R_0\).  Then

\[
\begin{aligned}
  \ker q_A
    &=\langle\!\langle X\rangle\!\rangle_C\\
    &\leq\langle\!\langle r_s:s\in S\rangle\!\rangle_C\\
    &\leq\langle\!\langle R_A\rangle\!\rangle_C
     =\ker q_A.
\end{aligned}
\]

Consequently

\[
  \boxed{\ker q_A=
    \langle\!\langle r_s:s\in S\rangle\!\rangle_C.}
  \tag{1.5}
\]

Let \(A_0=\langle S\rangle\leq A\), viewed also as a subgroup of \(G\), and let
\(B_0=\phi(A_0)\).  Restricting \(\phi\) gives

\[
  \phi_0:A_0\mathbin{\cong}B_0.
\]

The quotient imposing only the relations indexed by \(S\) is

\[
  C/\langle\!\langle r_s:s\in S\rangle\!\rangle_C
  \cong \operatorname{HNN}(G,A_0,B_0,\phi_0).
  \tag{1.6}
\]

Indeed, this is `HNNFinitePresentation.quotientEquiv` applied to \(A_0\): the
images of \(S\) generate \(A_0\), and the equalizer argument
`HNNFinitePresentation.conjHom_eq_phiHom` derives precisely the relations for
all of \(A_0\).

Fix \(a\in A\).  Equation (1.5) says that \(r_a\) is trivial in the smaller HNN
extension (1.6).  Therefore

\[
  t a t^{-1}=\phi(a)
  \tag{1.7}
\]

there.  The right side is in the canonical copy of \(G\).  The exact Britton
criterion `HNNBritton.t_conj_mem_range_iff` for the smaller HNN extension says

\[
  tat^{-1}\text{ lies in the base copy}
  \quad\Longleftrightarrow\quad a\in A_0.
\]

Thus \(a\in A_0\).  Since \(a\in A\) was arbitrary,
\(A=A_0=\langle S\rangle\).  The set \(S\) is finite, so \(A\) is finitely
generated. \(\square\)

### Corollary 1.2 — the repository hypothesis is exact

For a finitely presented base \(G\),

\[
  \operatorname{HNN}(G,A,B,\phi)\text{ is finitely presented}
  \quad\Longleftrightarrow\quad A\text{ is finitely generated}.
  \tag{1.8}
\]

The forward implication is Theorem 1.1.  The reverse implication is the proved
repository theorem
`HNNFinitePresentation.isFinitelyPresented_hnnExtension`.  Since \(A\cong B\),
either associated subgroup is finitely generated exactly when the other is.

Thus `[Group.FG A]` in the repository theorem is not merely sufficient
bookkeeping.  For a finitely presented base it is necessary.

## 2. The finite-support certificate

The proof gives a sharper statement without any finite-presentability
assumption.

### Proposition 2.1 — every omitted edge element is detected

Let \(S\subseteq A\), put \(A_0=\langle S\rangle\), and suppose
\(a\in A\setminus A_0\).  In the quotient of \(G*\langle t\rangle\) imposing
only

\[
  tst^{-1}=\phi(s)\qquad(s\in S),
\]

the omitted relator \(r_a\) is nontrivial.

### Proof

The partial quotient is the smaller HNN extension (1.6).  If \(r_a\) were
trivial, then \(tat^{-1}=\phi(a)\) would lie in its base copy.  The repository
pinch criterion `HNNBritton.t_conj_mem_range_iff` would force \(a\in A_0\), a
contradiction. \(\square\)

If \(A\) is not finitely generated, every finite \(S\subseteq A\) omits such an
\(a\).  Hence no finite subset of the HNN edge relations normally generates
all of them.  This is the exact obstruction consumed by the Tietze argument;
it does not rely on counting relators or on the absence of a presently known
presentation.

## 3. The countable HNN embedding is never an FP repair

Retain the notation of `Higman/HNNEmbedding.lean`.  For a group \(Q\) and an
enumeration \(g:\mathbb N\to Q\), the base is

\[
  P=Q*F(x,y),
\]

and

\[
  a_i=x^{-i}yx^i,
  \qquad
  b_i=g_i a_i.
\]

The repository proves:

* `HNNEmb.aHom_injective` and `HNNEmb.aEquiv`: the \(a_i\) freely generate an
  associated subgroup `Asub` isomorphic to `FreeGroup ℕ`;
* the corresponding statements `HNNEmb.bHom_injective` and `HNNEmb.bEquiv`
  for `Bsub`;
* `HNNEmb.Ext` is the HNN extension of \(P\) identifying \(a_i\) with \(b_i\);
* `HNNEmb.fg_ext`: when \(g\) is surjective, this extension is generated by
  three elements.

The free group on the basis indexed by \(\mathbb N\) is not finitely generated.
For completeness, a finite set of free words uses only finitely many basis
letters; sending all those letters to \(0\in\mathbb Z\) and one omitted letter
to \(1\in\mathbb Z\) proves that the omitted letter is outside the subgroup they
generate.  Hence `Asub` is not finitely generated.

If \(Q\) is finitely presented, then \(P=Q*F_2\) is finitely presented.
Theorem 1.1 therefore gives the exact conclusion

\[
  \boxed{\text{if }Q\text{ is finitely presented, then }
  \texttt{HNNEmb.Ext g}\text{ is not finitely presented}.}
  \tag{3.1}
\]

This holds for every enumeration \(g\); surjectivity is needed for
`HNNEmb.fg_ext`, not for (3.1).  When \(g\) is surjective, the construction is
therefore an explicit three-generated, non-finitely-presented overgroup.

The finite-support certificate is also explicit.  Given finitely many edge
relations, collect the finitely many basis letters of `FreeGroup ℕ` occurring
in their `Asub` indices.  Choose \(j\) outside that support.  In the partial HNN
extension the relation

\[
  t a_j t^{-1}=b_j

\]

is nontrivial by Proposition 2.1.  Thus no hidden Tietze compression can turn
this literal infinite-edge HNN table into a finite presentation.

This upgrades Route C of
`research/artifacts/conjugator-graph-finite-edge-trilemma-2026-08-26.md`:
`HNNEmbedding` is not merely a finite-generation device for which the current
finite-presentation API does not apply.  Over an FP payload base, its exact HNN
extension cannot be finitely presented.

## 4. The literal conjugator-graph HNN also fails

Use the notation of `Higman/TransportStar.lean`:

\[
  D=F_3\times F_3,
  \qquad
  \Gamma=\langle\gamma_h:h\in K\rangle,
  \qquad
  \gamma_h=(h^{-1}ah,h).
\]

`Star.graphHom_injective` shows that the displayed family is a free basis of
\(\Gamma\).  Since \(K=F(b,c)\) is infinite, \(\Gamma\) has infinite free rank
and is not finitely generated.

For \(k\in\{b,c\}\), the basis permutation

\[
  \gamma_h\longmapsto\gamma_{hk}
  \tag{4.1}
\]

extends to an automorphism of the abstract group \(\Gamma\).  Suppose one uses
this automorphism literally as the associated isomorphism of a one-letter HNN
extension of the finitely presented base \(D\).  Theorem 1.1 gives

\[
  \boxed{\operatorname{HNN}(D,\Gamma,\Gamma,\alpha_k)
  \text{ is not finitely presented}.}
  \tag{4.2}
\]

More generally, every one-letter HNN extension of an FP base whose associated
subgroup is this whole graph is non-finitely-presented, independently of which
isomorphism is put on the edge.

This closes one precise fake route: one cannot install the already valid
infinite-rank graph shift as a literal HNN edge and hope that its infinitely
many relations are accidentally consequences of finitely many of them.

It does **not** rule out a finite-rank edge in a larger base, several interacting
stable letters, or a finitely generated cutter whose intersection with \(D\)
is \(\Gamma\).  Those are different groups and are exactly the room a genuine
benign witness may use.

## 5. Exact remaining compiler boundary

The current Section 5 chain is now:

1. `Transport.codeRE` in `Higman/TransportCodeRE.lean` inhabits
   `Transport.CodeRE`.
2. `Star.unConjugation_of_graphBenign` turns
   `BenignTF Star.graphSub` into `Transport.UnConjugation`.
3. `Transport.transportSectionFive_of_parts` combines those two inputs into
   `TransportSectionFive`.

Therefore the strongest honest single semantic leaf in the current Section 5
chain is exactly

\[
  \boxed{\texttt{Higman.Star.ConjugatorGraph.graph_benign}.}
  \tag{5.1}
\]

Equivalently, one must construct a torsion-free finitely presented overgroup
\(W\) of \(D\) and a finitely generated subgroup \(L\leq W\) such that

\[
  D\cap L=\Gamma.
  \tag{5.2}
\]

The combined finite-edge audit is now exact:

* homomorphic un-conjugation is impossible by `Star.eq_one_of_unconj`;
* identifying a flip walker with the commuting value coordinate collapses the
  embedded double, as proved in the finite-edge trilemma;
* the formal Nielsen common envelope is not finitely presented by
  `notes/TRUE_FP_AMALGAM_FORCES_FG_EDGE_AND_NIELSEN_PUSHOUT_FAILS.md`;
* the literal countable-payload HNN and the literal whole-graph HNN are not
  finitely presented by Theorem 1.1 above.

Thus a successful witness must use genuinely finite-rank bridge data that
carries the nonhomomorphic value while changing the ambient group.  None of
the four conclusions above proves that no such bridge exists, and no
impossibility claim about (5.1) is made here.

Finally, (5.1) is a semantic benignness leaf.  Even after it is proved, the
finite-presentation recognition reduction still needs the repository's
separate effective reification and property-safety interfaces.  This note does
not identify semantic finite presentability with an effective compiler and
does not claim finite-presentation \(\Pi^0_2\)-hardness.

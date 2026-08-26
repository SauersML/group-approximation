# Finite presentability forces a finitely generated amalgam edge

## Status

This is a Cairn-only finite-support theorem and its exact application to the
basepointed-Nielsen proposal for
Higman.Star.ConjugatorGraph.graph_benign.

The conclusion is stronger than the status recorded in
research/artifacts/conjugator-graph-basepointed-nielsen-envelope-2026-08-26.md:
the formal common envelope

\[
  (F_3\times F_3)*_{\Gamma}M_0
\]

is not merely missing a finite-presentation proof. It is **not finitely
presented**.

The proof uses only repository-internal results:

* Tietze.ker_isFinitelyNormallyGenerated from
  GroupApproximation/Algebra/FinitePresentationKernel.lean;
* Tietze.exists_finite_subset_subset_normalClosure from
  GroupApproximation/Algebra/FinitePresentationTietze.lean;
* the presented-amalgam/pushout identification in
  GroupApproximation/Higman/AmalgamPushout.lean;
* Amalgam.inf_range_eq_base_range from
  GroupApproximation/Higman/BenignAmbient.lean.

No Lean, build, MSI, or external input was used.

## 1. The general converse theorem

Let \(A,G_1,G_2\) be groups and let

\[
  e_i:A\hookrightarrow G_i\qquad(i=1,2)
\]

be injective homomorphisms. Write

\[
  P=G_1*_{A}G_2
\]

for their amalgamated free product.

### Theorem 1.1 — an FP injective amalgam has an FG edge

If \(G_1\), \(G_2\), and \(P\) are finitely presented, then \(A\) is finitely
generated.

### Proof

Put \(C=G_1*G_2\), and for \(a\in A\) put

\[
  r_a=\iota_1(e_1(a))\,\iota_2(e_2(a))^{-1}\in C.
\]

Let

\[
  R_A=\{r_a:a\in A\}.
\]

The canonical quotient \(q_A:C\twoheadrightarrow P\) has

\[
  \ker q_A=\langle\!\langle R_A\rangle\!\rangle_C.
  \tag{1.1}
\]

This is exactly the quotient Amalg in
Higman/AmalgamPresentation.lean, identified with Mathlib's injective
pushout by Amalgam.pushEquiv.

The free product \(C\) is finitely presented because \(G_1\) and \(G_2\) are.
By the assumed finite presentability of \(P\),
Tietze.ker_isFinitelyNormallyGenerated applied to \(q_A\) gives a finite set
\(X\subseteq\ker q_A\) such that

\[
  \ker q_A=\langle\!\langle X\rangle\!\rangle_C.
  \tag{1.2}
\]

Every \(x\in X\) lies in the normal closure in (1.1). Normal generation is
compact: Tietze.exists_finite_subset_subset_normalClosure supplies one
finite subset \(R_0\subseteq R_A\) with

\[
  X\subseteq\langle\!\langle R_0\rangle\!\rangle_C.
\]

Choose a finite \(T\subseteq A\) containing an index of every relator in
\(R_0\). Then

\[
\begin{aligned}
  \ker q_A
    &=\langle\!\langle X\rangle\!\rangle_C\\
    &\leq\langle\!\langle r_t:t\in T\rangle\!\rangle_C\\
    &\leq\langle\!\langle R_A\rangle\!\rangle_C
     =\ker q_A.
\end{aligned}
\]

Hence

\[
  \boxed{\ker q_A=\langle\!\langle r_t:t\in T\rangle\!\rangle_C.}
  \tag{1.3}
\]

Let \(B=\langle T\rangle\leq A\). Identifying the two copies of each
\(t\in T\) identifies the two copies of every element of \(B\), because the
two maps out of \(B\) agree on a generating set. Consequently

\[
  C/\langle\!\langle r_t:t\in T\rangle\!\rangle_C
  \cong G_1*_{B}G_2.
  \tag{1.4}
\]

Equation (1.3) says that every \(r_a\), \(a\in A\), is already trivial in the
smaller amalgam (1.4). Thus the two factor images of \(e_1(a)\) and \(e_2(a)\)
coincide in \(G_1*_{B}G_2\).

The normal-form identity Amalgam.inf_range_eq_base_range says that the
intersection of the two factor images in this injective amalgam is exactly the
image of \(B\). Therefore there is \(b\in B\) whose two factor values equal
the common value of \(a\). Injectivity of the factor maps
(Amalgam.of_injective_push) and of \(e_1,e_2\) gives \(a=b\). Hence every
\(a\in A\) lies in \(B\), so

\[
  A=B=\langle T\rangle.
\]

The set \(T\) is finite. Therefore \(A\) is finitely generated. \(\square\)

### Corollary 1.2 — the finite-generation hypothesis is exact here

For injective amalgams of finitely presented vertex groups,

\[
  G_1*_{A}G_2\text{ finitely presented}
  \quad\Longleftrightarrow\quad
  A\text{ finitely generated}.
\]

The forward implication is Theorem 1.1. The reverse implication is the
repository theorem Amalgam.isFinitelyPresented_push.

Thus the [Group.FG G] hypothesis of that theorem is not merely a sufficient
hypothesis imposed by its proof. Under the injectivity hypotheses used by the
benign calculus, it is necessary.

## 2. Finite-support form

The proof contains a useful sharper statement. Suppose \(A\) is not finitely
generated. For every finite \(T\subseteq A\), choose

\[
  a\in A\setminus\langle T\rangle.
\]

In the quotient imposing only the edge relations indexed by \(T\), namely

\[
  G_1*_{\langle T\rangle}G_2,
\]

the relator \(r_a\) is nontrivial. Indeed, if it were trivial, the two factor
images of \(a\) would coincide; the intersection theorem would put their
common value in the image of \(\langle T\rangle\), and injectivity would force
\(a\in\langle T\rangle\), a contradiction.

Therefore no finite subset of the edge identifications normally generates all
edge identifications.

## 3. Application to the conjugator graph

Retain the notation of Higman/TransportStar.lean and of the Nielsen-envelope
artifact:

\[
  D=F_3\times F_3,
  \qquad
  U=\mathbb F\{u_h:h\in K\},
  \qquad
  \Gamma=\langle\gamma_h:h\in K\rangle\leq D,
\]

where

\[
  \gamma_h=(h^{-1}ah,h).
\]

The map

\[
  u_h\longmapsto\gamma_h
\]

is injective by Star.graphHom_injective; hence the displayed
\(\gamma_h\)'s are a free basis of \(\Gamma\).

The basepointed-Nielsen artifact constructs the five-generator, two-relator,
torsion-free finitely presented group

\[
  M_0=\langle z,p,q,s,t\mid[z,s]=1,[z,t]=1\rangle
\]

and an embedding \(U\hookrightarrow M_0\), written \(u_h\mapsto j_h\). The
elements \(j_h\) are again a free basis of the embedded copy of \(U\).

The index set \(K=\mathbb F(b,c)\) is infinite: the elements \(b^n\) have
distinct \(b\)-exponents. A free group on the basis \(\{u_h:h\in K\}\) is not
finitely generated. Directly, a finite collection of words uses only finitely
many basis letters; kill those letters and send one omitted basis letter to the
generator of \(\mathbb Z\).

Both edge embeddings

\[
  U\hookrightarrow D,
  \qquad
  U\hookrightarrow M_0
\]

are injective, both vertex groups are finitely presented, and \(U\) is not
finitely generated. Theorem 1.1 therefore gives the exact conclusion

\[
  \boxed{D*_{U}M_0\text{ is not finitely presented}.}
  \tag{3.1}
\]

After identifying \(U\) with its image \(\Gamma\leq D\), this is precisely

\[
  \boxed{(F_3\times F_3)*_{\Gamma}M_0
    \text{ is not finitely presented}.}
\]

### The omitted-basis certificate

For a finite \(S\subseteq K\), impose only

\[
  \gamma_s=j_s\qquad(s\in S).
\]

The quotient is the amalgam of \(D\) and \(M_0\) over the finite-rank free
subgroups generated by the corresponding basis subsets. If \(h\notin S\),
then \(\gamma_h\) and \(j_h\) do not become equal: equality would place their
common value in the intersection of the two factor images, which is exactly
the subgroup generated by the identified \(S\)-basis. But an omitted free
basis element belongs to neither such subgroup.

This is an explicit witness that every finite edge-identification list misses
another required graph value.

## 4. The Nielsen walkers cannot themselves be a finite invariant edge

The same artifact defines evaluation-preserving automorphisms

\[
  \alpha_k(u_1)=u_1,
  \qquad
  \alpha_k(u_h)=u_{hk}u_k^{-1}u_1\quad(h\neq1),
  \qquad k\in\{b,c\}.
\]

### Proposition 4.1

If \(V\leq U\) contains \(u_1,u_b,u_c\) and is invariant under
\(\alpha_b^{\pm1}\) and \(\alpha_c^{\pm1}\), then \(V=U\). In particular, such
a \(V\) is not finitely generated.

### Proof

The forward collection identity is

\[
  u_{hk}=\alpha_k(u_h)u_1^{-1}u_k.
  \tag{4.1}
\]

The explicit inverse from the artifact gives

\[
  u_{k^{-1}}
   =u_1\,\alpha_k^{-1}(u_k)^{-1}u_1
  \tag{4.2}
\]

and, for \(j\neq k\),

\[
  u_{jk^{-1}}
   =\alpha_k^{-1}(u_j)\,
      \alpha_k^{-1}(u_k)^{-1}u_1.
  \tag{4.3}
\]

Starting with \(u_1,u_b,u_c\in V\), invariance and (4.1)--(4.3) append any of
\(b^{\pm1},c^{\pm1}\) to an index already obtained. Induction on reduced word
length gives \(u_h\in V\) for every \(h\in K\). Hence \(V=U\). The final
claim follows because \(U\) has an infinite free basis. \(\square\)

Thus the corrected Nielsen action does solve finite collection in its
five-generator envelope, but it cannot be installed as an HNN action on a
finite-rank invariant edge lying inside the graph subgroup itself.

## 5. Exact boundary for UnConjugation

The following statements are now proved simultaneously:

1. the basepointed-Nielsen automorphisms and their finite envelope are valid;
2. an invariant edge inside the graph that contains the three collector seeds
   has infinite rank;
3. the exact formal common envelope obtained by gluing the original double to
   the Nielsen envelope along the whole graph is not finitely presented;
4. no finite subset of those gluing relations presents the same group.

Consequently the formal pushout cannot inhabit
Higman.Star.ConjugatorGraph, and it cannot close
Higman.Transport.UnConjugation through
Star.unConjugation_of_graphBenign.

This result does not assert that graphSub is not benign. It rules out the
specific common-envelope mechanism exactly: any successful witness must use
additional finite bridge relations that produce a different ambient group,
not a finite presentation of \(D*_{\Gamma}M_0\).

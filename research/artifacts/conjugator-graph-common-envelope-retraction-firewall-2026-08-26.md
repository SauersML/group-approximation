# The conjugator-graph common envelope cannot retract to the original double

## Status

This note continues the Cairn-only audit of
`Higman.Star.ConjugatorGraph.graph_benign`.  It assumes the explicit
basepointed-Nielsen envelope constructed in
`conjugator-graph-basepointed-nielsen-envelope-2026-08-26.md` and proves an
exact obstruction on the still-missing common envelope.

The conclusion is a firewall, not a benign witness:

> Any overgroup that identifies the original conjugator graph with the
> Nielsen envelope loses the first-coordinate projection of the original
> `F₃ × F₃`.  In particular, the original double cannot be a retract of the
> common envelope.

Thus direct-product graph witnesses, foldable symmetric doubles, and
graph-of-groups attachments that collapse back to the original vertex cannot
close the leaf.  A successful finite graph of groups must use a genuinely
nonretractive attachment.  The proof is one seven-letter reduced word and uses
no external result.

## 1. Notation

Let

\[
  A=\mathbb F(a,b,c),\qquad K=\langle b,c\rangle\leq A,
  \qquad D=A\times A.
\]

For \(h\in K\), put

\[
  \gamma_h=(h^{-1}ah,h)\in D.
\]

The conjugator graph is the free subgroup

\[
  \Gamma=\langle \gamma_h:h\in K\rangle.
\]

For \(k\in\{b,c\}\), the basepointed Nielsen automorphism used by the finite
envelope is

\[
  \alpha_k(\gamma_h)=\gamma_{hk}\gamma_k^{-1}\gamma_1.
\]

The formula is uniform at \(h=1\), since its right side then reduces to
\(\gamma_1\).  Its second coordinate is

\[
  hk\,k^{-1}\,1=h,
\]

so it preserves the graph evaluation exactly.

The finite Nielsen envelope contains a walker \(t_k\) satisfying

\[
  t_k^{-1}\gamma_h t_k=\alpha_k(\gamma_h)
  \qquad(h\in K)
\]

after its abstract graph is identified with \(\Gamma\).

## 2. A seven-letter nonconjugacy certificate

Take \(k=b\) and \(h=b\).  The first coordinate of
\(\alpha_b(\gamma_b)\) is

\[
\begin{aligned}
  (b^{-2}ab^2)(b^{-1}ab)^{-1}a
    &=b^{-2}ab^2b^{-1}a^{-1}ba\\
    &=\boxed{b^{-2}aba^{-1}ba}.
\end{aligned}
\]

Written in the free basis \(a,b,c\), this is the seven-letter word

\[
  b^{-1}b^{-1}ab a^{-1}ba.
\]

It is freely reduced: every adjacent pair uses different basis letters except
the first two, which have the same sign.  It is cyclically reduced as well,
because its first letter is \(b^{-1}\) and its last letter is \(a\).

It is not conjugate to \(a\).  Here is the full normal-form argument.  In a
free group, cyclically reducing a conjugate \(x^{-1}ax\) removes matching
outer letters until the one-letter cyclic core \(a\) remains.  Equivalently,
write \(x=ya^m\) with \(y\) either empty or ending in a letter other than
\(a^{\pm1}\); then

\[
  x^{-1}ax=a^{-m}y^{-1}ay a^m
\]

and cyclic cancellation removes \(a^{-m},a^m\) and then \(y^{-1},y\), leaving
\(a\).  Hence every conjugate of \(a\) has cyclically reduced length one.
The displayed word is already cyclically reduced of length seven, so it cannot
be a conjugate of \(a\).

We record the conclusion:

\[
  \boxed{
    \operatorname{fst}(\alpha_b(\gamma_b))
    =b^{-2}aba^{-1}ba
    \text{ is not conjugate to }a.}
\]

## 3. The first-coordinate extension firewall

### Theorem 3.1

Let \(P\) be a group containing an injective copy of \(D\).  Suppose
\(t\in P\) satisfies

\[
  t^{-1}\gamma_h t=\alpha_b(\gamma_h)
  \qquad(h\in K).
\]

There is no homomorphism

\[
  \Pi:P\longrightarrow A
\]

whose restriction to \(D\) is the first projection
\(\operatorname{fst}:D\to A\).

### Proof

Assume such \(\Pi\) exists and put \(x=\Pi(t)\).  Apply \(\Pi\) to the walker
relation at \(h=b\).  Its left side becomes

\[
  x^{-1}(b^{-1}ab)x,
\]

which is a conjugate of \(a\).  Its right side becomes the first coordinate of
\(\alpha_b(\gamma_b)\), namely

\[
  b^{-2}aba^{-1}ba.
\]

Section 2 proves that this word is not conjugate to \(a\), a contradiction.
\(\square\)

Only one walker relation is used.  Thus weakening the construction by keeping
just the \(b\)-walker or by discarding all but the \(h=b\) covariance equation
does not evade the obstruction.

### Corollary 3.2 — no retraction

Under the hypotheses of Theorem 3.1, there is no retraction

\[
  r:P\longrightarrow D
\]

fixing the embedded copy of \(D\).

Indeed, \(\operatorname{fst}\circ r\) would be the forbidden map \(\Pi\).

### Corollary 3.3 — no coordinate-preserving direct-product witness

The missing common envelope cannot be obtained inside any group equipped with
a homomorphism to \(A\) extending the first projection of the original
double.  In particular, adjoining auxiliary direct factors and using their
coordinate projections cannot realize the Nielsen envelope over \(\Gamma\).

This is independent of whether those auxiliary factors are free, finitely
presented, torsion-free, or themselves benign.

## 4. Exact graph-of-groups scope

Theorem 3.1 does not say that no finite graph-of-groups common envelope exists.
It says precisely which large class cannot work.

Consider a finite graph-of-groups presentation with a distinguished vertex
group \(D\).  Suppose the presentation admits a vertexwise collapse to \(D\):

1. the map on the distinguished vertex is the identity;
2. every other vertex group has a homomorphism to \(D\);
3. the two maps agree on every edge group; and
4. images chosen for stable letters satisfy the corresponding edge-conjugacy
   equations.

The defining presentation then gives a homomorphism from the fundamental group
to \(D\) fixing its distinguished vertex.  This is a retraction.  Corollary
3.2 therefore proves:

\[
  \boxed{
  \text{No such foldable finite graph of groups can contain the Nielsen
  walker over the original graph.}}
\]

This excludes, in particular:

* a free or direct auxiliary factor that is killed by the collapse;
* a central HNN letter sent to the identity;
* a symmetric double equipped with its ordinary fold map;
* any tree of auxiliary vertices whose attaching maps have compatible
  extensions back to \(D\).

The statement is deliberately limited.  A nonretractive graph of groups can
make two elements of \(D\) conjugate even when their first coordinates were
not conjugate in \(A\); that is exactly what an HNN edge is allowed to do.
The theorem does not rule such a construction out.

## 5. Why changing the projection is not cosmetic

The second projection behaves differently.  Since \(\alpha_k\) preserves
evaluation, a prospective extension of the second projection may simply kill
the Nielsen walkers.  The contradiction is specific to the first coordinate,
where \(\alpha_b(\gamma_b)\) changes a conjugate of \(a\) into a product of
three conjugates whose cyclic core has length seven.

Consequently a successful common envelope must satisfy both of the following:

1. it must retain the embedded original double, so its internal first
   projection remains meaningful on that subgroup;
2. it must prevent that projection from extending to the ambient group.

That is a useful design constraint.  Any proposed witness that still has an
obvious map back to either the first factor or the whole original double is
dead before an intersection calculation begins.

## 6. Remaining exact problem

The finite Nielsen envelope supplies a finitely generated cutter and a finite,
torsion-free presentation.  The current note proves that it cannot be attached
by any construction retaining a fold or retraction onto \(D\).

What remains is therefore the strictly nonretractive problem:

> Construct a finitely presented torsion-free group \(P\) containing both
> \(D\) and the Nielsen envelope, identifying their copies of \(\Gamma\),
> while deliberately making the first-coordinate projection of \(D\)
> nonextendable; then prove by normal forms that the intersection of the two
> embedded factors is exactly \(\Gamma\).

The formal amalgam \(D*_{\Gamma}M_0\) has exactly these properties except for
the missing finite-presentation proof.  The firewall shows that any finite
replacement must preserve its nonretractive character rather than trying to
recover a direct-product or foldable benign witness.

No inhabitant of `ConjugatorGraph` is claimed here.

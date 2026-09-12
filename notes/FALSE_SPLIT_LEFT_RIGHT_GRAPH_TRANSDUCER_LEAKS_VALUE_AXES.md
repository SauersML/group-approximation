# A split left/right graph transducer leaks the value axes

## Status

This is a Cairn-only obstruction to a new finite-rank candidate for
`Higman.Star.ConjugatorGraph.graph_benign`.

The candidate is attractive because it really does carry the nonhomomorphic
value with finitely many transition letters.  In

\[
  D=F(a,b,c)\times F(a,b,c),
  \qquad K=\langle b,c\rangle,
\]

every graph generator has the synchronized spelling

\[
  \gamma_h=(h^{-1}ah,h)
    =(h,1)^{-1}(a,1)(h,h).
  \tag{0.1}
\]

Thus the five fixed elements

\[
  (a,1),\quad (b,1),\quad(c,1),\quad(b,b),\quad(c,c)
  \tag{0.2}
\]

appear to be a finite-rank value transducer: spell the input path in the left
copy, spell the same path in the diagonal copy, and place \((a,1)\) between
them.

The construction fails exactly because a subgroup cannot enforce that the two
paths have the same spelling.  It contains the left and diagonal transition
for each alphabet letter separately, so their quotient is a pure value letter:

\[
  (b,1)^{-1}(b,b)=(1,b),
  \qquad
  (c,1)^{-1}(c,c)=(1,c).
\]

In fact the five elements in (0.2) generate all of

\[
  F(a,b,c)\times K,
\]

which strictly contains the conjugator graph.  The theorem below proves the
general identity, its overgroup form, and the precise design constraint it
places on a future multi-letter Britton bridge.

The proof uses only the repository notation and elementary subgroup algebra.
No Lean, build, MSI, or external input was used.

## 1. The abstract leakage identity

Let \(G\) be a group, let \(x\in G\), and let \(S\subseteq G\).  Put

\[
  H=\langle\{x\}\cup S\rangle\leq G,
  \qquad
  J=\langle S\rangle\leq G.
\]

Inside \(G\times G\), define

\[
  T(x,S)=
  \left\langle
    (x,1),\ (s,1),\ (s,s)\ :\ s\in S
  \right\rangle.
  \tag{1.1}
\]

### Theorem 1.1 — split-transition leakage

\[
  \boxed{T(x,S)=H\times J.}
  \tag{1.2}
\]

### Proof

Every generator in (1.1) lies in \(H\times J\), so

\[
  T(x,S)\leq H\times J.
  \tag{1.3}
\]

Conversely, \((x,1)\) and all \((s,1)\), \(s\in S\), generate
\(H\times1\).  For every \(s\in S\), both factors below lie in \(T(x,S)\),
and hence

\[
  (s,1)^{-1}(s,s)=(1,s)\in T(x,S).
  \tag{1.4}
\]

The elements in (1.4) generate \(1\times J\).  Since

\[
  (h,j)=(h,1)(1,j),
\]

the two axes generate \(H\times J\).  This proves the reverse inclusion in
(1.3), and hence (1.2). \(\square\)

Nothing in the proof uses finite generation, freeness, finite presentability,
or normal forms.  It is an algebraic leakage identity for any alphabet \(S\).

## 2. Exact application to the conjugator graph

Use the notation of `GroupApproximation/Higman/TransportStar.lean`:

\[
  F_3=F(a,b,c),
  \qquad K=\langle b,c\rangle,
  \qquad D=F_3\times F_3,
\]

and

\[
  \Gamma=
  \left\langle\gamma_h=(h^{-1}ah,h):h\in K\right\rangle.
\]

Take \(x=a\) and \(S=\{b,c\}\) in Theorem 1.1.  Since

\[
  \langle a,b,c\rangle=F_3,
  \qquad
  \langle b,c\rangle=K,
\]

we obtain the exact identity

\[
  \boxed{
  \left\langle
    (a,1),(b,1),(c,1),(b,b),(c,c)
  \right\rangle
  =F_3\times K.}
  \tag{2.1}
\]

### Proposition 2.1 — the synchronized spellings are present

For every \(h\in K\), the left side of (2.1) contains \(\gamma_h\).

### Proof

The left transitions \((b,1),(c,1)\) generate every \((h,1)\), \(h\in K\),
and the diagonal transitions \((b,b),(c,c)\) generate every \((h,h)\).  Thus
the subgroup contains

\[
  (h,1)^{-1}(a,1)(h,h)=(h^{-1}ah,h)=\gamma_h.
\]

Taking generated subgroups gives \(\Gamma\leq F_3\times K\), as expected.
\(\square\)

### Proposition 2.2 — the leakage is strict

\[
  (1,b)\in F_3\times K
  \qquad\text{but}\qquad
  (1,b)\notin\Gamma.
  \tag{2.2}
\]

### Proof

Membership in the product is immediate.  For the second statement, the
repository defines

\[
  \mathsf{graphHom}(w)
   =(\mathsf{cbHom}(w),\mathsf{evalHom}(w))
\]

and `Star.graphSub` is its range.  If \((1,b)=\mathsf{graphHom}(w)\), then the
first coordinate gives \(\mathsf{cbHom}(w)=1\).  The proved theorem
`Conj.cbHom_injective` forces \(w=1\), and then the second coordinate is
\(\mathsf{evalHom}(1)=1\).  This contradicts `Star.b_ne_one`. \(\square\)

Combining (2.1) and (2.2), the split transducer does not merely produce a few
unwanted words.  It produces the whole finite-rank-coordinate ambient
subgroup \(F_3\times K\), already strictly larger than the target.

## 3. The overgroup form

The leakage cannot be repaired by placing the five transitions in a larger
group.

### Corollary 3.1 — ambient enlargement does not remove leakage

Let \(P\) be any group and let

\[
  e:D\hookrightarrow P
\]

be an injective homomorphism.  If a subgroup \(L\leq P\) contains

\[
  e(a,1),\ e(b,1),\ e(c,1),\ e(b,b),\ e(c,c),
  \tag{3.1}
\]

then

\[
  e(F_3\times K)\leq L\cap e(D).
  \tag{3.2}
\]

In particular,

\[
  L\cap e(D)\neq e(\Gamma).
  \tag{3.3}
\]

### Proof

Theorem 1.1 and (3.1) give \(e(F_3\times K)\leq L\).  It is also contained in
\(e(D)\), proving (3.2).  The element \(e(1,b)\) belongs to the left side of
(3.2), while injectivity of \(e\) and Proposition 2.2 show that it does not
belong to \(e(\Gamma)\).  Hence (3.3). \(\square\)

This conclusion is independent of the presentation, torsion, retractions, or
normal-form theory of \(P\).  Later HNN or amalgam letters cannot make an
already present element of \(L\cap e(D)\) disappear.

## 4. What a viable finite-rank bridge must do

Equation (0.1) shows that finite-rank nonhomomorphic value transport is not
itself the missing idea: a five-letter split spelling already transports the
value exactly.  The missing resource is **synchronization under subgroup
generation**.

The failure can be stated without coordinates.  For each transition letter
\(s\), the split design exposes two cutter elements \(\ell_s,r_s\) with

\[
  \ell_s=e(s,1),
  \qquad
  r_s=e(s,s).
\]

Because a cutter is a group, it also exposes

\[
  \ell_s^{-1}r_s=e(1,s),
\]

and the synchronization invariant is gone before a graph word is read.

Therefore a successful multi-letter bridge must satisfy the following exact
constraint:

> The synchronized composite representing
> \((h,1)^{-1}(a,1)(h,h)\) may return to the embedded double, but the left and
> output-bearing transition paths may not both return to the embedded double
> as independently available cutter elements.

This is the role a genuine Britton bridge would have to play.  Its transition
legs must remain outside the base, and normal form must allow a matched pair to
collapse to \(\gamma_h\) while every mismatched pair remains Britton-reduced
outside the base.  If both legs collapse separately, Corollary 3.1 applies and
the value axes leak.

The result does not rule out such a hidden-leg HNN construction, and it makes
no claim that `Star.graphSub` is non-benign.  It rules out precisely the
finite-rank split-path transducer (0.2), including every ambient enlargement
that places its five transition values themselves in the cutter.

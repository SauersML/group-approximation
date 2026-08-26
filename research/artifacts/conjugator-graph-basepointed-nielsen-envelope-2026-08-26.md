# The conjugator graph has a finite basepointed-Nielsen envelope

## Status

This note attacks the remaining `Higman.Star.ConjugatorGraph.graph_benign`
leaf directly and without external inputs.

It does **not** close the leaf.  It does two substantive things:

1. It proves an exact obstruction to every finite walker construction that
   permutes the graph basis while extending the evaluation map.
2. It gives the smallest escape from that obstruction: explicit
   basepointed Nielsen automorphisms.  They preserve evaluation, generate the
   whole infinite graph basis from three seeds, and produce an explicit
   five-generator, two-relator, finitely presented torsion-free envelope of
   the abstract graph subgroup.

The sole remaining step is now sharply isolated: place this Nielsen envelope
and the original copy of `F₃ × F₃` in one finitely presented torsion-free
group so that their intersection is exactly the conjugator graph.  The naive
amalgam identifies an infinitely generated edge, and the Nielsen walkers do
not extend to automorphisms of the original double.  No assertion below hides
that step.

## 1. The abstract graph and its evaluation

Let

\[
  K=\mathbb F(b,c)
\]

and let

\[
  U=\mathbb F\{u_h:h\in K\}
\]

be the free group on the underlying set of \(K\).  Define

\[
  \varepsilon:U\longrightarrow K,
  \qquad \varepsilon(u_h)=h.
\]

The repository's `Star.graphHom` identifies \(U\) with

\[
  \Gamma=
  \left\langle (a^h,h):h\in K\right\rangle
  \leq F_3\times F_3
\]

by

\[
  u_h\longmapsto(a^h,h).
\]

Injectivity is exactly `Conj.cbHom_injective`, spent in the first coordinate.
Thus it is enough in this note to work with \(U\), remembering that
\(\varepsilon\) is the second projection of the original graph.

## 2. Why basis-permuting walkers cannot work

The first natural design is a finitely generated group \(L\) containing
\(U\), together with a homomorphism

\[
  \psi:L\longrightarrow K
\]

extending \(\varepsilon\), and finitely many walker elements \(t\in L\) that
normalize \(U\) and permute its distinguished free basis:

\[
  t^{-1}u_h t=u_{\sigma_t(h)}.
\]

This design is impossible for a reason stronger than “right multiplication is
not a homomorphism.”

### Proposition 2.1 — evaluation-compatible permutation walkers are inner

Under the hypotheses above, if \(q=\psi(t)\), then

\[
  \boxed{\sigma_t(h)=q^{-1}hq\qquad(h\in K).}
\]

### Proof

Apply \(\psi\) to the walker relation:

\[
\begin{aligned}
  \sigma_t(h)
    &=\psi(u_{\sigma_t(h)})\\
    &=\psi(t)^{-1}\psi(u_h)\psi(t)\\
    &=q^{-1}hq.
\end{aligned}
\]

There is no additional group theory in the argument. \(\square\)

### Corollary 2.2 — finitely many permutation walkers and seeds do not collect
the graph basis

Let \(T\subseteq L\) and \(S\subseteq K\) be finite.  The basis elements
reachable from \(\{u_s:s\in S\}\) by conjugating with words in \(T\) have
indices lying in finitely many conjugacy classes of \(K\).  They cannot contain
all \(u_h\), \(h\in K\).

Indeed Proposition 2.1 says that every walker word acts by an inner
automorphism of \(K\), so each seed stays in its conjugacy class.  A finite
union of conjugacy classes does not cover \(K\): abelianization is constant on
a conjugacy class, while

\[
  b,b^2,b^3,\ldots
\]

have pairwise distinct abelianizations \((1,0),(2,0),(3,0),\ldots\).

Finally, because \(U\) is free on the displayed basis, the subgroup generated
by a subset of that basis contains no omitted basis element.  One may see this
without a free-factor theorem: kill every chosen basis element and send one
omitted basis element to the generator of \(\mathbb Z\).  The resulting
homomorphism kills the generated subgroup but not the omitted element.

This rules out every finite HNN walker whose conjugation merely permutes the
graph generators and whose cutter carries an extension of the second-coordinate
evaluation.  In particular it rules out left shifts, right shifts and affine
permutations after any attempt to make evaluation extend.

## 3. The basepointed Nielsen correction

The permutation requirement is the part to discard.  Fix a nontrivial
\(k\in K\).  Define a homomorphism \(\alpha_k:U\to U\) on the free basis by

\[
  \alpha_k(u_1)=u_1
\]

and, for \(h\neq1\),

\[
  \boxed{
  \alpha_k(u_h)=u_{hk},u_k^{-1},u_1.}
\]

This is right translation with a basepoint correction.  The correction is
exactly what the evaluation map needs:

\[
  \varepsilon(\alpha_k(u_h))
  =hk\,k^{-1}\,1=h
\]

for \(h\neq1\), and the equality is immediate at \(h=1\).  Hence

\[
  \boxed{\varepsilon\alpha_k=\varepsilon.}
\]

Unlike raw right translation, \(\alpha_k\) is an automorphism.

### Proposition 3.1 — explicit inverse

Define \(\beta_k:U\to U\) on the free basis by

\[
  \beta_k(u_1)=u_1,
\]

\[
  \beta_k(u_k)=u_1u_{k^{-1}}^{-1}u_1,
\]

and, for \(j\neq k\),

\[
  \beta_k(u_j)
  =u_{jk^{-1}}u_1^{-1}\beta_k(u_k).
\]

Then

\[
  \beta_k\alpha_k=1_U,
  \qquad
  \alpha_k\beta_k=1_U.
\]

### Proof

It is enough to check the free basis.

At \(u_1\), both composites are visibly the identity.  If \(h\neq1\), then
\(hk\neq k\), so

\[
\begin{aligned}
  \beta_k(\alpha_k(u_h))
    &=\beta_k(u_{hk})\beta_k(u_k)^{-1}\beta_k(u_1)\\
    &=u_hu_1^{-1}\beta_k(u_k)\beta_k(u_k)^{-1}u_1\\
    &=u_h.
\end{aligned}
\]

For the other composite, first

\[
\begin{aligned}
  \alpha_k(\beta_k(u_k))
    &=u_1\bigl(u_1u_k^{-1}u_1\bigr)^{-1}u_1\\
    &=u_k.
\end{aligned}
\]

If \(j\neq k\), then \(jk^{-1}\neq1\), and therefore

\[
\begin{aligned}
  \alpha_k(\beta_k(u_j))
    &=\bigl(u_ju_k^{-1}u_1\bigr)u_1^{-1}u_k\\
    &=u_j.
\end{aligned}
\]

Thus \(\beta_k=\alpha_k^{-1}\). \(\square\)

Applying \(\varepsilon\) to the formulas also gives
\(\varepsilon\beta_k=\varepsilon\).

## 4. Two corrected walkers collect every graph generator

Use \(\alpha_b\) and \(\alpha_c\), and form the semidirect product

\[
  M=U\rtimes_{\alpha}\mathbb F(t_b,t_c),
\]

with convention

\[
  t_k^{-1}ut_k=\alpha_k(u),\qquad k\in\{b,c\}.
\]

The group \(M\) is generated by only

\[
  u_1,u_b,u_c,t_b,t_c.
\]

Here is the direct collection proof.  From the defining formula,

\[
  \boxed{
  u_{hk}=t_k^{-1}u_ht_k,u_1^{-1}u_k}
\]

for \(k=b,c\); the formula also holds at \(h=1\), because \(t_k\) commutes
with \(u_1\).

The inverse formula first gives

\[
  t_ku_kt_k^{-1}=u_1u_{k^{-1}}^{-1}u_1,
\]

and hence

\[
  \boxed{
  u_{k^{-1}}
  =u_1\bigl(t_ku_kt_k^{-1}\bigr)^{-1}u_1.}
\]

For arbitrary \(j\neq k\), it gives

\[
  t_ku_jt_k^{-1}
  =u_{jk^{-1}}u_1^{-1}(t_ku_kt_k^{-1}),
\]

so

\[
  \boxed{
  u_{jk^{-1}}
  =(t_ku_jt_k^{-1})(t_ku_kt_k^{-1})^{-1}u_1.}
\]

Starting at \(u_1,u_b,u_c\), these formulas append
\(b^{\pm1},c^{\pm1}\) to the index.  Induction on reduced word length gives
every \(u_h\).

## 5. The envelope is five-generator, two-relator and torsion-free

The preceding semidirect product has a much smaller finite presentation than
its definition suggests.

Let

\[
  M_0=
  \left\langle
    z,p,q,s,t
  \ \middle|\ [z,s]=1,\ [z,t]=1
  \right\rangle.
\]

Thus

\[
  M_0\cong
  \bigl(\langle z\rangle\times\mathbb F(s,t)\bigr)
  *\mathbb F(p,q).
\]

### Theorem 5.1

There is an isomorphism \(M\cong M_0\) carrying

\[
  u_1\mapsto z,quad u_b\mapsto p,quad u_c\mapsto q,quad
  t_b\mapsto s,quad t_c\mapsto t.
\]

### Proof

For \(k=b,c\), define a bijection of the underlying set of \(M_0\):

\[
  F_k(x)=t_k^{-1}xt_kz^{-1}u_k,
\]

where \((t_b,u_b)=(s,p)\) and \((t_c,u_c)=(t,q)\).  Its inverse is

\[
  F_k^{-1}(y)=t_k y u_k^{-1}z t_k^{-1}.
\]

The two displayed commutator relations give

\[
  F_b(z)=p,qquad F_c(z)=q.
\]

Because \(K=\mathbb F(b,c)\), the bijections \(F_b,F_c\) define a set action
of \(K\) on \(M_0\).  Put

\[
  j_h=F_h(z).
\]

Then \(j_1=z,j_b=p,j_c=q\), and by definition

\[
  t_k^{-1}j_ht_k=j_{hk}u_k^{-1}z.
\]

At \(h=1\) this is just \([z,t_k]=1\); at \(h\neq1\) it is exactly the
relation saying that \(u_h\mapsto j_h\) intertwines \(\alpha_k\) with
conjugation by \(t_k\).  Hence the assignment \(u_h\mapsto j_h\), together
with the identity assignment on \(t_b,t_c\), defines a homomorphism
\(M\to M_0\).

Conversely, send

\[
  z\mapsto u_1,quad p\mapsto u_b,quad q\mapsto u_c,quad
  s\mapsto t_b,quad t\mapsto t_c.
\]

The only two relations hold because both \(\alpha_b\) and \(\alpha_c\) fix
\(u_1\).  This defines a homomorphism \(M_0\to M\).

The composite on \(M_0\) fixes its five displayed generators.  The other
composite fixes the two stable letters, and it fixes every \(u_h\) by induction
on a reduced spelling of \(h\): the transformations \(F_k^{\pm1}\) become,
inside \(M\), exactly the forward and inverse collection formulas of Section
4.  Thus the maps are inverse. \(\square\)

The group \(M_0\) is finitely presented by display.  It is torsion-free by a
two-step direct normal-form argument:

* \(\langle z\rangle\times\mathbb F(s,t)\) is torsion-free, because a finite
  power equal to one vanishes in each coordinate, and free groups are
  torsion-free by cyclic reduction;
* a nontrivial finite-order element of a free product is conjugate to a
  cyclically reduced word; a cyclically reduced word using both factors has
  all positive powers reduced and nonempty, while a word lying in one factor
  has infinite order by the first bullet.

Thus \(M\) is an explicit finitely presented torsion-free overgroup of the
abstract graph group \(U\).

## 6. Evaluation extends over the finite envelope

Define

\[
  \Psi:M_0\longrightarrow K
\]

by

\[
  \Psi(z)=\Psi(s)=\Psi(t)=1,qquad
  \Psi(p)=b,quad\Psi(q)=c.
\]

The two relators are respected.  Moreover

\[
  \Psi(F_k(x))=\Psi(x)k,qquad
  \Psi(F_k^{-1}(x))=\Psi(x)k^{-1}.
\]

Induction on a reduced word for \(h\) gives

\[
  \boxed{\Psi(j_h)=h.}
\]

Therefore the embedding \(U\hookrightarrow M_0\), \(u_h\mapsto j_h\), is
evaluation-compatible:

\[
  \Psi|_U=\varepsilon.
\]

This is precisely what raw right-translation walkers could not achieve.

## 7. Why this is not yet `graph_benign`

The result above proves that the abstract graph subgroup has a remarkably
small torsion-free finitely presented envelope.  Benignness asks for more:
an embedding

\[
  F_3\times F_3\hookrightarrow P
\]

and a finitely generated \(L\leq P\) such that

\[
  (F_3\times F_3)\cap L=\Gamma.
\]

The formal pushout

\[
  (F_3\times F_3)*_{\Gamma}M_0
\]

has the correct intersection by the amalgam normal form, and its \(M_0\)
factor is a finitely generated cutter.  But \(\Gamma\cong U\) is not finitely
generated, so the repository's finite-presentation theorem for an amalgam does
not apply.  The presentation contains the infinite family

\[
  (a^h,h)=j_h\qquad(h\in K).
\]

The five-generator presentation of \(M_0\) does not by itself make these
identifications finite: propagating from \(h\) to \(hk\) uses conjugation by
the Nielsen walker in \(M_0\), while the basepointed Nielsen automorphism

\[
  u_h\longmapsto u_{hk}u_k^{-1}u_1
\]

does not extend to an automorphism of the original direct product.  It sends a
single graph basis element to a three-letter graph word, whereas the obvious
automorphisms of the first free factor preserve the property “conjugate of
\(a\).”  Thus finite seed identifications do not currently propagate across
the original factor.

This is the exact remaining construction problem:

> Build a finitely presented torsion-free common envelope in which the two
> basepointed Nielsen walkers act on the embedded conjugator graph, while the
> original `F₃ × F₃` remains embedded.

It is strictly narrower than the former `ConjugatorGraph` leaf.  The abstract
infinite graph, its evaluation map, the finite collection mechanism, finite
presentation, and torsion-freeness are all now explicit.

## 8. Lean-facing consequences, not yet code

A future formalization can be split into four independent modules:

1. `Star.BasepointedNielsen`: definitions of \(\alpha_k,\beta_k\), inverse
   proofs, and `evalHom` invariance.
2. `Star.NielsenCollection`: generation of all \(u_h\) from
   \(u_1,u_b,u_c,t_b,t_c\).
3. `Star.NielsenEnvelope`: the isomorphism with
   `⟨z,p,q,s,t | [z,s],[z,t]⟩` and its torsion-free finite presentation.
4. One genuinely new ambient-extension theorem.  Only this fourth item may
   inhabit `ConjugatorGraph`.

The first three are unconditional algebra and should not be advertised as the
missing benign witness.  Unrestricted image transport remains false and is
not used anywhere in this note.


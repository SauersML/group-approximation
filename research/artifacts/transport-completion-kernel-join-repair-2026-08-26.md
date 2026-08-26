# Repairing the Section-5 completion: normal closure is still too small

## Scope and verdict

This note audits the false `Higman.Transport.CompletionLemma` in
`GroupApproximation/Higman/TransportFive.lean`.  It uses no external theorem as
an input.  Every group used below is given explicitly, and every normal-form or
torsion claim needed by the repair is proved directly.

Write

\[
  \delta_n:\mathbb F(\mathbb Z)\longrightarrow
  \mathbb F(\operatorname{Fin}(n+1))
\]

for `Transport.decodeHom n`, and

\[
  s_n:\mathbb F(\operatorname{Fin}(n+1))\longrightarrow
  \mathbb F(\mathbb Z)
\]

for `Transport.sectionHom n`.  Thus \(\delta_n s_n=1\).  For a subgroup
\(N\leq \mathbb F(\operatorname{Fin}(n+1))\), let

\[
  C_N=
  \left\langle\operatorname{Seq.elt}(f):f\in\operatorname{codeSet}(n,N)
  \right\rangle .
\]

This is the current `codeSub n N`.

The conclusions are:

1. Replacing \(C_N\) by the normal closure of the same generators does **not**
   make the section inclusion true.  A counterexample already exists in rank
   two with \(N=\langle\!\langle a^3\rangle\!\rangle\).
2. The smallest algebraic repair is instead

   \[
     \widehat C_N=C_N\vee\ker\delta_n.
   \]

   In fact

   \[
     \boxed{\widehat C_N=\delta_n^{-1}(N)}
   \]

   for every subgroup \(N\), without a normality hypothesis.
3. The existing un-conjugation output can consume this repair.  Its old row
   subgroup is joined with one fixed periodic-row kernel.  That kernel is
   benign with a torsion-free witness by an explicit finite cyclic-shift
   mapping torus.  No new RE hypothesis is needed.

Thus `CompletionLemma` should be deleted, not proved.  Its replacement is an
exact kernel-join identity plus a uniform periodic-row-kernel lemma.

## 1. Why normal closure does not repair completion

Take \(n=1\), so the decoded free group is

\[
  F=\mathbb F(a,b).
\]

Let

\[
  N=\langle\!\langle a^3\rangle\!\rangle_F.
\]

This is normal.  No raw word of length one represents an element of \(N\).
Indeed, map \(F\) to \(C_3\times C_2\) by

\[
  a\longmapsto (1,0),\qquad b\longmapsto(0,1).
\]

The element \(a^3\) dies, so \(N\) lies in the kernel, while
\(a,a^{-1},b,b^{-1}\) all survive.  Those are exactly the four possible
values of a one-letter raw word.

Let \(T=C_2=\{1,t\}\).  Define a homomorphism

\[
  \chi:\mathbb F(\mathbb Z)\longrightarrow T
\]

on the free generators \(x_p\), \(p\in\mathbb Z\), as follows:

\[
  \chi(x_p)=
  \begin{cases}
    t,&0\leq p<4,\\
    1,&\text{otherwise}.
  \end{cases}
\]

For `codeSeq 1 v 0`, the letter in raw position \(k\) is placed at

\[
  2k+(i_k\bmod 2).
\]

Consequently the first two letters of every code land in the interval
\([0,4)\), and every later letter lands outside it.  Signs do not matter in
\(C_2\).  Therefore

\[
  \chi(\operatorname{Seq.elt}(\operatorname{codeSeq}(1,v,0)))=1
\]

whenever \(v\) has length zero or at least two: for length at least two the
first two letters contribute \(t^2=1\), and all later letters contribute
\(1\).

Every code belonging to `codeSet 1 N` has length zero or at least two, by the
one-letter observation above.  Hence \(\chi\) kills every code generator and
therefore kills even their normal closure

\[
  D_N=\left\langle\!\left\langle
    \operatorname{Seq.elt}(f):f\in\operatorname{codeSet}(1,N)
  \right\rangle\!\right\rangle .
\]

On the other hand the section sends \(a\) to \(x_0\), so

\[
  \chi(s_1(a^3))=\chi(x_0^3)=t\neq1.
\]

Thus

\[
  a^3\in N,
  \qquad
  s_1(a^3)\notin D_N.
\]

This refutes both the old subgroup-generated completion and the proposed
normal-closure completion.

It also refutes the desired exact comap for the normal-closure variant.  The
row homomorphism is injective, so membership of
`rowHom (sectionHom 1 (a^3))` in `D_N.map rowHom` would force
`sectionHom 1 (a^3) \in D_N`, contrary to the character \(\chi\).

The failure is structural.  A block code remembers its first two time slots.
Normal conjugation changes the surrounding group word but does not relabel
those free generators.  Normal closure therefore does not erase the finite
prefix state carried by the coding.

## 2. The exact algebraic repair

Return to arbitrary \(n\) and arbitrary \(N\leq F_n\), where

\[
  F_n=\mathbb F(\operatorname{Fin}(n+1)).
\]

Define

\[
  \widehat C_N=C_N\vee\ker\delta_n.
\]

### Theorem 2.1

For every subgroup \(N\leq F_n\),

\[
  \boxed{\widehat C_N=N.\operatorname{comap}(\delta_n).}
\]

In particular, for every \(w\in F_n\),

\[
  w\in N\quad\Longleftrightarrow\quad s_n(w)\in\widehat C_N.
\]

### Proof

The proved theorem `map_decodeHom_codeSub_le` says

\[
  \delta_n(C_N)\leq N.
\]

The kernel maps to \(1\), so

\[
  \widehat C_N\leq\delta_n^{-1}(N).
\]

For the reverse inclusion, take \(x\in\delta_n^{-1}(N)\), and put
\(w=\delta_n(x)\).  The proved completeness theorem `exists_mem_codeSet`
supplies \(c\in C_N\) with

\[
  \delta_n(c)=w.
\]

Then

\[
  k=s_n(w)c^{-1}\in\ker\delta_n
\]

because \(\delta_n s_n=1\).  Hence \(s_n(w)=kc\in\widehat C_N\).  Also

\[
  x s_n(w)^{-1}\in\ker\delta_n,
\]

so \(x\in\widehat C_N\).  This proves equality.

Applying the equality to \(s_n(w)\), and again using
\(\delta_n s_n=1\), gives the displayed equivalence.  Notice that normality
of \(N\) was never used.  \(\square\)

This is more precise than merely asking for normal closure: it adds exactly
the equivalence relation that the decoder forgets.  When \(N\) is normal, the
resulting subgroup is itself normal and therefore contains the normal closure
of the code words; the counterexample above says that containment can be
strict.

## 3. The repaired row identity

Let \(R=\operatorname{Seq.rowHom}\), and define the fixed periodic-row kernel

\[
  P_n=R(\ker\delta_n)\leq F_3.
\]

Since homomorphisms preserve joins and the current
`map_rowHom_codeSub` theorem identifies the first summand,

\[
  R(\widehat C_N)
  =
  \operatorname{closure}(\operatorname{Seq.bElt}''\operatorname{codeSet}(n,N))
  \vee P_n.
\]

Therefore Theorem 2.1 and injectivity of `Seq.rowHom` give

\[
\boxed{
  \left(
    \operatorname{closure}(\operatorname{Seq.bElt}''\operatorname{codeSet}(n,N))
    \vee P_n
  \right).\operatorname{comap}(\operatorname{rowSection}(n))
  =N.}
\]

The proof is the same two-line witness argument as the present
`comap_rowSection_eq`, with `codeSub` replaced by `completedCodeSub`; no
normality hypothesis is required.

This is exactly the shape the existing downstream assembly can use:

1. `CodeRE` makes `codeSet n N` recursively enumerable.
2. Theorem 4 gives benignness of its conjugated family.
3. `UnConjugation` gives benignness of the old ordinary row closure.
4. The fixed subgroup \(P_n\) is benign with a torsion-free witness, by the
   construction in the next section.
5. `BenignTF.sup` gives benignness of their join.
6. `BenignTF.comap` along `rowSection n` and the boxed identity give
   benignness of \(N\).

In contrast, the proposed normal closure is not consumable by the existing
assembly even if its false completion claim were ignored:
`UnConjugation.unconj` returns the ordinary subgroup closure of the row words,
not their normal closure.  No current map identity turns that output into the
normal closure.

## 4. A torsion-free benign witness for the periodic-row kernel

It remains to justify, without importing a theorem, that \(P_n\) is benign
with a torsion-free witness.  Put \(m=n+1\), so \(m\geq1\).

### 4.1 The row group inside a rank-two free group

Let

\[
  F_0=\mathbb F(b,c),
  \qquad b_i=c^{-i}bc^i\quad(i\in\mathbb Z).
\]

The map

\[
  \rho:\mathbb F(\mathbb Z)\longrightarrow F_0,
  \qquad x_i\longmapsto b_i
\]

is injective; this is already `Row.basisHom_injective` in the repository.  Its
range is the kernel of the exponent homomorphism

\[
  e_c:F_0\longrightarrow\mathbb Z,
  \qquad e_c(b)=0,\quad e_c(c)=1.
\]

Here is a direct proof of the only non-immediate inclusion.  Read a reduced
word in \(b^{\pm1},c^{\pm1}\) from left to right while recording the current
total \(c\)-exponent.  Move every occurrence of \(c\) to the right using

\[
  c^r b^\varepsilon
  = (c^r b^\varepsilon c^{-r})c^r.
\]

The word becomes a product of elements \(b_i^{\pm1}\), followed by
\(c^{e_c(w)}\).  If \(e_c(w)=0\), only the row product remains.

The subgroup \(\ker e_c\) is benign with a torsion-free witness by the explicit
graph construction: embed \(F_0\) into \(F_0\times\mathbb Z\) as
\(g\mapsto(g,1)\), and take the graph of \(e_c\) as the cutting subgroup.
The graph is generated by the images of \(b,c\); the ambient direct product is
finitely presented and torsion-free.

### 4.2 The finite cyclic-shift mapping torus

Let

\[
  B_m=\mathbb F(y_0,\ldots,y_{m-1})
\]

and let \(\alpha\) cyclically permute the free basis:

\[
  \alpha(y_i)=y_{i-1\bmod m}.
\]

(Equivalently, \(\alpha^{-1}(y_i)=y_{i+1\bmod m}\).)

Define the group \(Q_m\) on the set \(B_m\times\mathbb Z\) by

\[
  (u,r)(v,s)=(u\alpha^r(v),r+s).
\]

Associativity follows immediately from
\(\alpha^{r+s}=\alpha^r\alpha^s\); the identity is \((1,0)\), and

\[
  (u,r)^{-1}=(\alpha^{-r}(u^{-1}),-r).
\]

Thus this is a group, with \(B_m\) embedded as the first coordinate and with
\(z=(1,1)\) satisfying

\[
  z^{-1}(y_i,0)z=(y_{i+1\bmod m},0)
\]
by the displayed choice of orientation for \(\alpha\).

It has the finite presentation

\[
  \left\langle y_0,\ldots,y_{m-1},z\ \middle|\
  z^{-1}y_i z=y_{i+1\bmod m}\ (0\leq i<m)
  \right\rangle .
\]

To verify this without a presentation theorem, send the displayed generators
to the explicit pairs above.  Conversely, use the relations to move every
\(z\)-letter to the right; every presented word becomes uniquely
\(u z^r\).  Multiplication of these normal forms is exactly the displayed
pair multiplication, so the two maps are inverse.

The group is torsion-free.  If \((u,r)^d=1\) for \(d>0\), its second coordinate
gives \(dr=0\), hence \(r=0\).  Then \(u^d=1\) in the free group \(B_m\), so
\(u=1\): a nonempty cyclically reduced free word has nonempty powers, while an
arbitrary nontrivial free word is conjugate to a nonempty cyclically reduced
one.

Define

\[
  \pi_m:F_0\longrightarrow Q_m,
  \qquad b\longmapsto(y_0,0),\quad c\longmapsto z.
\]

Then

\[
  \pi_m(b_i)=(y_{i\bmod m},0).
\]

Consequently the square

\[
\begin{array}{ccc}
\mathbb F(\mathbb Z)&\xrightarrow{\rho}&F_0\\
\delta_n\downarrow&&\downarrow\pi_m\\
B_m&\hookrightarrow&Q_m
\end{array}
\]

commutes, after identifying the basis of \(B_m\) with
`Fin (n+1)`.  The bottom arrow is injective because it is literally
\(u\mapsto(u,0)\).  Hence

\[
  \rho(\ker\delta_n)=\rho(\mathbb F(\mathbb Z))\cap\ker\pi_m
  =\ker e_c\cap\ker\pi_m.
\]

### 4.3 Benignness and the torsion clause

Exactly as for \(e_c\), the graph construction makes \(\ker\pi_m\) benign in
\(F_0\) with torsion-free witness \(F_0\times Q_m\): both factors are finitely
presented and torsion-free, and the graph is finitely generated because \(F_0\)
is generated by \(b,c\).

The direct-product intersection construction applied to
\(\ker e_c\) and \(\ker\pi_m\) therefore makes

\[
  \rho(\ker\delta_n)
\]

benign with a torsion-free witness in \(F_0\).  Finally embed
\(F_0=\langle b,c\rangle\) into
\(F_3=\langle a,b,c\rangle\).  The inclusion has the retraction killing
\(a\), so it is injective; the existing `BenignTF.mapEmb` construction carries
the witness to

\[
  P_n=(\ker\delta_n).\operatorname{map}(\operatorname{Seq.rowHom}).
\]

This proves the required periodic-row-kernel statement with no unresolved
group-theoretic input.

The construction is uniform in \(n\): the presentation of \(Q_{n+1}\) has
\(n+2\) generators and \(n+1\) cyclic-shift relators, all obtained by bounded
finite iteration.  Thus the repair introduces no non-effective choice.

## 5. RE accounting

The recursively enumerable object remains exactly `codeSet n N`.  No
membership test for \(\ker\delta_n\) is fed into Theorem 4 and no saturation of
the code set is required.

The two summands are handled by different mechanisms:

* the input-dependent summand \(C_N\) uses `CodeRE`, Theorem 4 and
  `UnConjugation`;
* the input-independent summand \(\ker\delta_n\) uses the explicit finite
  cyclic-shift witness above.

They are joined only after both torsion-free benign witnesses exist.  Therefore
RE-ness is preserved exactly as in the current assembly, and the added kernel
cost is finite and uniform.

## 6. Precise replacement package

The Lean-facing redesign should have the following declarations (names are
suggestive, not commitments):

```text
completedCodeSub n N :=
  codeSub n N ⊔ MonoidHom.ker (decodeHom n)

completedCodeSub_eq_comap :
  completedCodeSub n N = N.comap (decodeHom n)

periodicRowKernel n :=
  (MonoidHom.ker (decodeHom n)).map Seq.rowHom

benignTF_periodicRowKernel :
  ∀ n, BenignTF (periodicRowKernel n)

map_rowHom_completedCodeSub :
  (completedCodeSub n N).map Seq.rowHom =
    Subgroup.closure (Seq.bElt '' codeSet n N) ⊔ periodicRowKernel n

comap_completedRowSection_eq :
  (Subgroup.closure (Seq.bElt '' codeSet n N) ⊔
    periodicRowKernel n).comap (rowSection n) = N
```

Then `transportSectionFive_of_parts` needs only `CodeRE` and `UnConjugation`;
the `CompletionLemma` argument disappears.  After un-conjugation, take one
`BenignTF.sup` with `benignTF_periodicRowKernel`, then the existing comap.

## Final audit

* **Normal closure of the old code family:** false, by the explicit
  \(F(a,b),\langle\!\langle a^3\rangle\!\rangle,C_2\) character.
* **Section inclusion after kernel join:** true, and strengthened to the exact
  equality \(C_N\vee\ker\delta_n=\delta_n^{-1}(N)\).
* **Exact decoded comap:** true after the kernel join, with no normality
  hypothesis.
* **Compatibility with the current un-conjugation assembly:** yes; ordinary
  closure remains untouched, and the fixed kernel image is added by a join.
* **RE:** unchanged.
* **Torsion-free benignness of the added piece:** explicit and uniform via the
  cyclic-shift mapping torus \(F_{n+1}\rtimes\mathbb Z\).
* **Remaining Section-5 obstruction:** `UnConjugation` remains a separate real
  leaf.  This repair neither assumes nor launders it.

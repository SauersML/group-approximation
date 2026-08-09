# Global quasi-cocycle rigidity for the binary Leavitt elementary group

Let

\[
L=L_{\mathbf F_2}(1,2),\qquad G=E_5(L)=GL_5(L),
\]

and let

\[
H=\operatorname{diag}(E_4(L),1)=\operatorname{diag}(GL_4(L),1).
\]

This note proves that (G) has property ((TT)/T).  The same proof gives
Mimura's ((FF_{L_p})/T), (1<p<\infty).  The point not supplied by the
general noncommutative-universal-lattice theorem is bounded generation; it
follows here from the strong two-sided division property of (L).

## Inputs

The following algebraic inputs are proved in the repository.

1. Every nonzero (x\in L) admits (p,q\in L) such that (pxq=1)
   (`Leavitt/LeavittSimplicity.lean`).
2. (GL_m(L)=E_m(L)) for every (m\geq2)
   (`KOne/AllRanksElementary.lean`).

For the rigidity input, write (A=\mathbf Z\langle X_1,\ldots,X_k\rangle)
for a finite free noncommutative ring mapping onto (L).  Mimura,
Proposition 9.2.8, proves that

\[
E_5(A)\geq E_4(A)
\]

has relative ((TT)/T), and relative ((FF_{L_p})/T) for every
(1<p<\infty).  These relative properties pass to quotient pairs, so they
hold for (G\geq H).

## Uniform elimination

### Lemma

Let (R\neq0) be a ring satisfying

\[
x\neq0\Longrightarrow \exists p,q\in R\quad pxq=1.
\]

For every (n\geq2) and (A\in GL_n(R)), there are products (E,F) of
elementary transvections and (u\in R^\times) such that

\[
EAF=\operatorname{diag}(u,1,\ldots,1),
\]

where the total number of transvections occurring in (E) and (F) is at
most

\[
n^2+4n-5.
\]

### Proof

Induct on (n).  The first row of an invertible matrix is nonzero.  Using
at most three elementary transvections for a signed column swap, arrange
that (a=A_{11}\neq0).  Put (b=A_{12}), and choose (p,q\in R) with
(paq=1).  Set

\[
\rho=q(1-pb).
\]

Right multiplication by (t_{12}(\rho)) changes the ((1,2))-entry to

\[
b'=a\rho+b,
\qquad pb'=pa q(1-pb)+pb=1.
\]

Let (d') denote the resulting ((2,2))-entry.  Left multiplication by

\[
t_{21}((1-d')p)
\]

makes the ((2,2))-entry equal to

\[
(1-d')pb'+d'=1.
\]

Now left multiply by (t_{12}(-b')), and right multiply by
(t_{21}(-c')), where (c') is the then-current ((2,1))-entry.  This
clears positions ((1,2)) and ((2,1)).

For each (j\geq3), right multiply by
(t_{2j}(-A_{2j})).  Since (A_{22}=1), these operations make row (2)
the second standard row.  Then, for each (i\geq3), left multiply by
(t_{i2}(-A_{i2})).  These operations clear column (2) without changing
the complementary block.  The resulting matrix is (B\oplus1), with
(B\in GL_{n-1}(R)) on coordinates (1,3,\ldots,n).  Apply the inductive
hypothesis to (B).

At block size (m), the construction uses at most

\[
3+4+2(m-2)=2m+3
\]

transvections.  Hence the total is at most

\[
\sum_{m=2}^n(2m+3)=n^2+4n-5.
\]

This proves the lemma.  (square)

## Bounded generation in rank five

Apply the lemma to (R=L) and (n=5).  It uses at most (40)
transvections.  The remaining diagonal belongs to (H), because

\[
\operatorname{diag}(u,1,1,1)\in GL_4(L)=E_4(L).
\]

Let

\[
N_+=\langle t_{i5}(a):1\leq i\leq4, a\in L\rangle,
\qquad
N_-=\langle t_{5j}(a):1\leq j\leq4, a\in L\rangle.
\]

Every elementary transvection avoiding coordinate (5) lies in (H),
and every remaining transvection lies in (N_+\cup N_-).  Moving the left
elementary factors across the equality only replaces transvections by
their inverses.  Therefore

\[
G=(H\cup N_+\cup N_-)^{41}. \tag{1}
\]

This is exactly the bounded-generation hypothesis absent from the general
noncommutative case in Mimura's Proposition 9.2.8.

There is also a subgroup-only form.  A root using coordinate (5) lies in
a conjugate of (H) by a coordinate permutation which swaps (5) with a
coordinate not used by that root.  Only finitely many such permutations
are needed, and they belong to (GL_5(L)=E_5(L)).  Consequently there are
fixed conjugates (H_1,\ldots,H_s) of (H) such that

\[
G=(H_1\cup\cdots\cup H_s)^{41}. \tag{2}
\]

## Consequences

### Theorem

The group (E_5(L_{\mathbf F_2}(1,2))) has property ((TT)/T).

### Proof

The quotient of Mimura's relative theorem gives relative ((TT)/T) for
(G\geq H).  Equivalently, a quasi-cocycle into a unitary representation
without invariant vectors is bounded on (H).  It is then bounded on each
fixed conjugate (H_i): expand (b(g_i h g_i^{-1})) and use the fixed
values (b(g_i)), (b(g_i^{-1})) and the quasi-cocycle defect.  Equation
(2), followed by the quasi-cocycle triangle inequality at most (40)
times, bounds it on (G).  (square)

Mimura's Theorem 8.1.7 and Proposition 9.2.8 give, with the same equation
(1), the Banach strengthening

\[
E_5(L_{\mathbf F_2}(1,2))\text{ has }(FF_{L_p})/T
\quad(1<p<\infty).
\]

Finally, property ((TT)/T) is invariant under central quotients and under
central extensions whose total group has property ((T)).  Hence the
universal Steinberg cover

\[
St_5(L)\longrightarrow E_5(L)
\]

also has property ((TT)/T).

## Exact remaining frontier

For the Steinberg cover (U=St_5(L)), superperfectness handles trivial
coefficients and the theorem above makes the comparison map

\[
H_b^2(U,\mathcal H_\pi)\longrightarrow H^2(U,\mathcal H_\pi)
\]

injective whenever (pi) has no invariant vectors.  What is not proved is

\[
H^2(U,\mathcal H_\pi)=0
\quad\text{for every unitary }\pi.
\]

That is the remaining (2)-Kazhdan/cohomological correction problem.  The
present theorem does not by itself prove Frobenius stability, normalized
Hilbert--Schmidt stability, nonhyperlinearity, or a hyperlinear nonsofic
counterexample.

## Source pin

Masato Mimura, *Rigidity theorems for universal and symplectic universal
lattices*, Proposition 9.2.8 and Theorem 8.1.7.  Proposition 9.2.8 states
relative ((TT)/T) for (E_m(A)\geq E_{m-1}(A)), (m\geq3), and relative
((FF_{L_p})/T), (m\geq4), for a finite free noncommutative ring (A).
Its proof explicitly identifies bounded generation as the missing condition
for the corresponding global conclusion.

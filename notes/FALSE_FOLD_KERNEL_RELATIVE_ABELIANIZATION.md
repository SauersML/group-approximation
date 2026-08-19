# Finite fold kernels reduce to relative abelianization

Date: 2026-08-12

## 1. Outcome

Let

\[
D=G*_{\Gamma}G
\]

be the symmetric double, let (r:D\to G) be the fold retraction, and put

\[
F=\ker r.
\]

For a quotient (q:G\twoheadrightarrow Q), write (N=\ker q) and

\[
K=\ker(qr)=r^{-1}(N).
\]

There are canonical identifications

\[
F_{\rm ab}\cong I_{G/\Gamma},
\qquad
K_{\rm ab}\cong (I_{G/\Gamma})_N\oplus N_{\rm ab},
\tag{FRA1}
\]

where (I_X=\ker(\mathbb Z[X]\to\mathbb Z)) is the augmentation module
and the subscript denotes coinvariants.  Under these identifications the
fold word

\[
w_h=i_2(h)i_1(h)^{-1}
\]

maps to

\[
[h\Gamma]-[\Gamma]\in (I_{G/\Gamma})_N.
\tag{FRA2}
\]

If (q(\Gamma)=Q), then (N) acts transitively on (G/\Gamma) and

\[
(I_{G/\Gamma})_N
\cong
N/([N,N](N\cap\Gamma)).
\tag{FRA3}
\]

If (q(h)=q(\gamma)) for (gamma\in\Gamma), the class in `(FRA2)`
corresponds, up to the global orientation convention, to the class of

\[
n=h\gamma^{-1}\in N
\tag{FRA4}
\]

in `(FRA3)`.

For the natural exponent-period quotient of the Laurent/polynomial pair,
this class vanishes by one explicit elementary commutator.  Thus the long
inverse-root collision is already absorbed in the **ordinary abelianization
of the finite fold kernel**.  No Schur-multiplier calculation is needed to
prove exact absorption.

This does not close the asymptotic branch-cut route.  The positive element
and the commutator filling used below have degree growing with the period.
They therefore give no bounded-word identity in the original group.

## 2. The free fold kernel

Let (T) be the Bass--Serre tree of (D).  The fold kernel (F) meets
every conjugate of either vertex group trivially, so (F) acts freely on
(T).  The quotient graph (F\backslash T) has two vertices and one edge
for every point of (G/\Gamma).  Every edge joins the two vertices.

Consequently (F) is free and its abelianization is the first cellular
homology of this quotient graph:

\[
F_{\rm ab}
\cong
\ker\bigl(\mathbb Z[G/\Gamma]\xrightarrow{\rm aug}\mathbb Z\bigr)
=I_{G/\Gamma}.
\tag{FRA5}
\]

The first vertex copy splits the fold map.  Conjugation by it acts on the
edge set by left translation, so `(FRA5)` is an isomorphism of
(\mathbb ZG)-modules.  Taking the edge (Gamma) as the spanning-tree
edge shows directly that

\[
i_2(g)i_1(g)^{-1}
\longmapsto
[g\Gamma]-[\Gamma].
\tag{FRA6}
\]

## 3. Passing to a finite vertex quotient

The restriction (r:K\to N) is split by the first vertex copy.  Hence

\[
K=F\rtimes N.
\tag{FRA7}
\]

Abelianizing a split semidirect product gives

\[
K_{\rm ab}
\cong
(F_{\rm ab})_N\oplus N_{\rm ab},
\tag{FRA8}
\]

which proves `(FRA1)`.  Since every (w_h) lies in (F), its second
coordinate is zero and `(FRA2)` follows from `(FRA6)`.

There is a useful general description of the first summand.  Choose
representatives (g_j\Gamma) for the (N)-orbits in (G/\Gamma), and put

\[
L_j=N\cap g_j\Gamma g_j^{-1}.
\]

Apply (N)-homology to

\[
0\longrightarrow I_{G/\Gamma}
\longrightarrow\mathbb Z[G/\Gamma]
\longrightarrow\mathbb Z\longrightarrow0.
\]

Shapiro's lemma and the degree-zero orbit decomposition give the exact
sequence

\[
\bigoplus_j (L_j)_{\rm ab}
\longrightarrow N_{\rm ab}
\longrightarrow (I_{G/\Gamma})_N
\longrightarrow I_{N\backslash G/\Gamma}
\longrightarrow0.
\tag{FRA9}
\]

Thus, in a general quotient, the relative carrier is (N_{\rm ab}) modulo
the images of **all** orbit stabilizers, followed by a free orbit-augmentation
part.  It is not correct in general to quotient only by (N\cap\Gamma).

If (q(\Gamma)=Q), then (N\backslash G/\Gamma) is a singleton.  There is
one stabilizer (N\cap\Gamma), `(FRA9)` reduces to `(FRA3)`, and the
connecting homomorphism sends (n\in N) to

\[
[n\Gamma]-[\Gamma].
\tag{FRA10}
\]

Writing (h=n\gamma) with (gamma\in\Gamma) proves `(FRA4)`.

## 4. Explicit absorption in the exponent-period quotient

Use one Laurent variable (x), put

\[
t=x^M-1,
\]

and reduce the coefficient ring modulo an ideal containing (t).  In this
quotient (x^{-1}=x^{M-1}), so the positive and Laurent coefficient images
coincide.  In particular (q(\Gamma)=q(G)), and `(FRA3)` applies.

Take the inverse-root translation

\[
h=e_{12}(x^{-1})
\]

and its positive lift

\[
\gamma=e_{12}(x^{M-1})\in\Gamma.
\]

Then

\[
n=h\gamma^{-1}=e_{12}(-x^{-1}t)\in N.
\tag{FRA11}
\]

There is also a positive kernel element

\[
u=e_{12}(-x^{M-1}t)\in N\cap\Gamma.
\tag{FRA12}
\]

Using (e_{12}(a)e_{12}(b)=e_{12}(a+b)), one obtains

\[
nu^{-1}=e_{12}(x^{-1}t^2).
\tag{FRA13}
\]

For the commutator convention ([a,b]=aba^{-1}b^{-1}), the elementary
Steinberg relation gives

\[
[e_{13}(t),e_{32}(x^{-1}t)]
=e_{12}(x^{-1}t^2).
\tag{FRA14}
\]

Both entries on the left of `(FRA14)` belong to (N).  Equations
`(FRA12)--(FRA14)` therefore prove

\[
n\in [N,N](N\cap\Gamma).
\tag{FRA15}
\]

By `(FRA3)--(FRA4)`, the image of (w_h) in (K_{\rm ab}) is zero.

The same calculation works in several variables by imposing a period on
the selected variable and leaving the other variables unchanged.

## 5. What this settles and what remains

The theorem gives a short group-theoretic explanation of the exact
absorption proved in
`FALSE_NATURAL_FINITE_CLOCK_RELATIVE_ABSORPTION.md`:

1. the finite fold word lands in the relative abelianization `(FRA3)`;
2. its inverse-root discrepancy is the element `(FRA11)`;
3. a positive kernel correction removes the first-order (t)-term; and
4. the remaining (t^2)-term is the elementary commutator `(FRA14)`.

The construction is deliberately nonuniform.  The coefficient of (u)
has degree (2M-1), and the positive word length required to represent the
inverse root grows at least linearly with (M); see
`FALSE_POSITIVE_INVERSE_ROOT_LINEAR_DISTORTION.md`.  Therefore `(FRA15)`
does not supply a fixed relation that kills an asymptotic clock phase.

The live quantitative question is whether this growing filling can be
distributed so that every fixed carry coordinate has vanishing normalized
Hilbert--Schmidt cost while the marked fold accumulates a nontrivial phase.
Equivalently, exact relative abelianization is now finished; only its
metric restriction profile remains.

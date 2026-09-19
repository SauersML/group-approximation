# The finite-representation matching barrier

This note isolates a quantitative obstruction to constructing a
fold-sensitive trace on the Kun--Thom symmetric double from exact
finite-dimensional representations of its vertex group.

Let \(\Gamma<G\) have property \((T)\).  Assume that \(t\in G\) is a strict
compressor,

\[
 t\Gamma t^{-1}\leq\Gamma,
\]

and let \(S\subset\Gamma\) be a finite Kazhdan set.  Fix a constant
\(\kappa>0\) such that, for every unitary representation \(\beta\) of
\(\Gamma\) on a finite-dimensional Hilbert space and every vector \(\xi\),

\[
 \operatorname{dist}(\xi,\operatorname{Fix}_\Gamma(\beta))
 \leq \kappa^{-1}\max_{s\in S}\|\beta(s)\xi-\xi\|.
 \tag{1}
\]

Such a spectral-gap formulation is equivalent to property \((T)\), after
changing the Kazhdan constant by an inessential fixed factor.

## The quantitative theorem

**Theorem.**  Let

\[
 \pi,\sigma:G\longrightarrow U(d)
\]

be arbitrary exact finite-dimensional unitary representations and let
\(U\in U(d)\).  For every \(\gamma\in\Gamma\), put

\[
 h=t^{-1}\gamma t.
\]

Then

\[
 \|\pi(h)-U\sigma(h)U^*\|_{2,d}
 \leq
 {2\over\kappa}
 \max_{s\in S}\|\pi(s)-U\sigma(s)U^*\|_{2,d}.
 \tag{2}
\]

Here \(\|\cdot\|_{2,d}\) is the normalized Hilbert--Schmidt norm.

**Proof.**  Give \(M_d(\mathbb C)\) its normalized Hilbert--Schmidt inner
product and define a unitary representation of \(G\) by

\[
 \beta(g)X=\pi(g)X\sigma(g)^*.
 \tag{3}
\]

Write

\[
 V_\Gamma=\operatorname{Fix}_\Gamma(\beta).
\]

The compressor acts invariantly on this fixed space.  Indeed,

\[
 \beta(t)V_\Gamma
 =\operatorname{Fix}_{t\Gamma t^{-1}}(\beta).
 \tag{4}
\]

Since \(t\Gamma t^{-1}\leq\Gamma\),

\[
 V_\Gamma
 \subseteq \operatorname{Fix}_{t\Gamma t^{-1}}(\beta).
 \tag{5}
\]

The two spaces in (5) have equal finite dimension by (4), because
\(\beta(t)\) is unitary.  Hence equality holds and

\[
 \beta(t)V_\Gamma=V_\Gamma.                            \tag{6}
\]

Every \(\beta(\gamma)\), \(\gamma\in\Gamma\), acts as the identity on
\(V_\Gamma\).  Combining this with (6) shows that

\[
 \beta(t^{-1}\gamma t)|_{V_\Gamma}=1.                 \tag{7}
\]

Let \(P\) be the orthogonal projection onto \(V_\Gamma\) and set \(V=PU\),
viewing the unitary matrix \(U\) as a Hilbert--Schmidt vector.  By (1),

\[
 \|U-V\|_{2,d}
 \leq \kappa^{-1}\max_{s\in S}\|\beta(s)U-U\|_{2,d}.
 \tag{8}
\]

Equation (7) gives \(\beta(h)V=V\).  Therefore

\[
 \|\beta(h)U-U\|_{2,d}
 \leq 2\|U-V\|_{2,d}.                                 \tag{9}
\]

Finally, unitary invariance of the Hilbert--Schmidt norm gives

\[
 \begin{aligned}
 \|\beta(g)U-U\|_{2,d}
 &=\|\pi(g)U\sigma(g)^*-U\|_{2,d}\\
 &=\|\pi(g)-U\sigma(g)U^*\|_{2,d}.
 \end{aligned}
\]

Substitution into (8)--(9) proves (2). \(\square\)

## Consequence for the weak-MF double

Let

\[
 D=G *_\Gamma G
\]

and let \(h=t^{-1}\gamma t\notin\Gamma\) be the Kun--Thom invisible
element.  Suppose one attempts to construct matrix microstates for \(D\) as
follows:

1. choose exact finite-dimensional representations
   \(\pi_n,\sigma_n:G\to U(d_n)\);
2. conjugate the second representation by \(U_n\in U(d_n)\);
3. arrange that the two copies asymptotically agree on \(\Gamma\), so they
   define an approximate representation of the amalgam.

Agreement on the fixed Kazhdan set means that the right-hand side of (2)
tends to zero.  The theorem then forces

\[
 \|\pi_n(h)-U_n\sigma_n(h)U_n^*\|_{2,d_n}\longrightarrow0. \tag{10}
\]

Thus the fold-difference

\[
 i_2(h)i_1(h)^{-1}
\]

is invisible in the resulting tracial ultraproduct.  This remains true even
when the two exact vertex representations are unrelated, have different
finite images, or are subsequently amplified to equal dimensions.

Consequently, the Connes-embeddable trace required to turn the weak-MF
nonsofic double into a hyperlinear nonsofic image cannot be produced merely
by matching exact finite-dimensional models of the two vertex copies along
\(\Gamma\).  At least one vertex copy must itself be represented by genuinely
nonliftable normalized-Hilbert--Schmidt almost-representations of \(G\).

This locates the remaining exoticity more sharply than the statement that
exact representations of the whole double kill the witness: approximate
amalgamation of *different* exact vertex representations kills it at a
uniform rate controlled by the Kazhdan constant.

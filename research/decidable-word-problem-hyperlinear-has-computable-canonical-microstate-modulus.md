---
rg: 2
id: decidable-word-problem-hyperlinear-has-computable-canonical-microstate-modulus
kind: claim
title: A word-problem decider makes the canonical hyperlinear dimension profile computably bounded
distinct_from:
  hyperlinear-computable-hs-dehn-modulus-solvable-word-problem: that derives a word-problem algorithm from hyperlinearity plus a computable defect modulus for trivial words; this starts with a word-problem algorithm and computes dimensions of canonical microstates, with no stability or defect modulus.
  canonical-profile-kleene-higman: that is a reverse-Kleene nonhyperlinearity criterion for a machine-indexed recursively presented family; this is a direct effective-search theorem for one hyperlinear group.
  mf-recognition-has-a-pi2-upper-bound: that classifies a presentation-level decision predicate; this computes witnesses for one promised hyperlinear group from an explicit word-problem decider.
  clapham-fp-embedding-preserves-word-problem: that constructs a finitely presented decidable envelope; this computes canonical matrix witnesses once a finite generating set and decider are already supplied.
---

**ESTABLISHED.** Let \(\Gamma=\langle x_1,\ldots,x_m\rangle\) be a
finitely generated hyperlinear group, and supply an algorithm \(W\) deciding
whether a word in the \(x_i^{\pm1}\) is trivial in \(\Gamma\). Finite
presentability is not needed.

For \(n,q\ge 1\), call a tuple
\(U=(U_1,\ldots,U_m)\in U(d)^m\) a **canonical \((n,q)\)-microstate** when,
for every freely reduced word \(w\) of length at most \(n\),

\[
\begin{aligned}
 w=_{\Gamma}1&\Longrightarrow
       \|w(U)-I_d\|_{2,d}<2^{-q},\\
 w\ne_{\Gamma}1&\Longrightarrow
       |\operatorname{tr}_d(w(U))|<2^{-q}.
                                                               \tag{CHM1}
\end{aligned}
\]

Here \(\operatorname{tr}_d\) and \(\|\cdot\|_{2,d}\) are normalized. There is
one Turing functional which, from the finite generating alphabet, a code for
\(W\), and \((n,q)\), halts with

\[
(d,U_1,\ldots,U_m),\qquad U_i\in U(d)\cap M_d(\mathbb Q(i)),
                                                               \tag{CHM2}
\]

satisfying \((\mathrm{CHM1})\). Consequently \(\Gamma\) has a total
computable dimension bound

\[
\mu_{\Gamma,W}(n,q)
 \quad\text{such that a canonical \((n,q)\)-microstate exists in some }
 d\le \mu_{\Gamma,W}(n,q).                                  \tag{CHM3}
\]

The bound may be chosen nondecreasing in both variables by taking finite
maxima of the dimensions returned for smaller inputs.

This is also a modulus for the usual finite-ball definition. Choose a
representative word of length at most \(R\) for every element of \(B_R\).
Applying \((\mathrm{CHM1})\) at radius \(3R\) makes the evaluated
representatives approximately multiplicative, because each multiplication
error is a trivial word of length at most \(3R\). For distinct elements
\(g,h\in B_R\),

\[
 \|w_g(U)-w_h(U)\|_{2,d}^2
 =2-2\operatorname{Re}\operatorname{tr}_d(w_g(U)^*w_h(U))
 >2-2^{1-q}.                                               \tag{CHM4}
\]

Thus \(R\) and a rational tolerance effectively determine an input
\((n,q)\) and hence a dimension bound.

## Uniformity boundary

The theorem is uniform **relative to the supplied word-problem decider**.
It is not a presentation-only algorithm promised on the semantic class of
finite presentations which happen to have decidable word problem: there is
no uniform procedure extracting a decider from such a presentation. For a
fixed finitely presented group with a fixed decider, however,
\(\mu_{\Gamma,W}\) is an ordinary total computable function.

The proof is
`decidable-word-problem-hyperlinear-microstate-search-proof`.

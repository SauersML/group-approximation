---
rg: 2
id: dense-homoclinic-algebraic-ce-proof
kind: route
title: Turn Hayes model measures into a diagonal crossed-product embedding
target: dense-homoclinic-algebraic-actions-are-ce
requires: []
---

Fix a sofic approximation
`sigma_i:Lambda -> Sym(d_i)`.  Hayes' Proposition 2.15(ii) says that density
of the homoclinic group of the profinite action supplies probability measures
on `K^(d_i)` converging locally and doubly empirically to Haar measure.
Choose successively typical configurations `x_i in K^(d_i)` for a growing
finite family of continuous functions and actor elements.  Local empirical
convergence gives

```text
(1/d_i) sum_j f(x_i(j)) -> integral_K f dm_K,
```

while concentration on action microstates gives, for every fixed `g`,

```text
(1/d_i) |{j : x_i(sigma_i(g)^(-1)j)
                    is close to g x_i(j)}| -> 1.       (DHP1)
```

For `f in C(K)`, put

```text
Theta_i(f)=diag(f(x_i(1)),...,f(x_i(d_i)))
```

and send the canonical actor unitary `u_g` to the permutation matrix of
`sigma_i(g)`.  Multiplication on `C(K)` is exact, the trace converges to Haar
by the first display, covariance holds in normalized Hilbert--Schmidt norm
by `(DHP1)`, and the actor multiplication laws hold by soficity.  A diagonal
argument therefore produces a unital trace-preserving homomorphism

```text
L^infinity(K) rtimes Lambda -> product_omega M_(d_i)(C).
```

Faithfulness follows from trace preservation.  This is precisely the
Connes-embedding conclusion (and is Păunescu's sofic-action embedding with
the Cartan algebra diagonal).

When `K` is abelian, Pontryagin Fourier transform sends `L^infinity(K)` to
`L(hat K)` and intertwines the action, giving the canonical trace-preserving
isomorphism with `L(hat K rtimes Lambda)`.  Finally, for
`K <= (F_p^m)^Lambda`, a configuration tends to zero off finite sets iff its
support is finite, proving the last assertion.

---
rg: 2
id: homomorphic-group-alphabet-ca-reduction-proof
kind: route
title: Force the local rule onto, split the socle into a permuted nonabelian shift and linear layers, and induct on the quotient
target: homomorphic-group-alphabet-ca-reduce-to-stable-finiteness
requires: []
artifacts:
  - research/artifacts/homomorphic-group-alphabet-surjunctivity-2026-09-16.md
---

## Why sufficient

All section numbers refer to the artifact. Every step is proved there. The only classical inputs are the
Jordan–Hölder theorem and compactness of `V^G` for finite `V`.

**Linear base (Section 1).**
- **Lemma 1.** `alpha -> tau_alpha`, with `tau_alpha(x)(g) = sum_h alpha_h x(gh)`, is an injective
  multiplicative bijection from `M_n(F_p[G])` onto the `F_p`-linear automata on `(F_p^n)^G`.
- **Lemma 2.** Suppose `tau_alpha` is injective.
  - It is a homeomorphism onto its image, and its inverse is linear and equivariant.
  - By compactness the inverse reads a finite window, so the inverse extends to a linear automaton
    `tau_beta` with `beta alpha = 1`.
  - Direct finiteness gives `alpha beta = 1`, so `tau_alpha` is surjective.
  - Conversely, `beta alpha = 1 != alpha beta` makes `tau_alpha` injective and not surjective.

**Group lemmas (Sections 2–3).** Here `K` is finite.
- **Lemma 3.** A surjective homomorphism `mu : K^M -> K` sends each minimal normal subgroup `N`, placed in one
  coordinate, to `1` or to a minimal normal subgroup isomorphic to `N`.
- **Lemma 4.** `Soc(K) = A × S`, where:
  - `S` is the direct product of all nonabelian minimal normal subgroups, has `Z(S) = 1`, and is a product of
    nonabelian simple groups;
  - `A = prod_p A_p` with `A_p` elementary abelian and `p` in `P(K)`.
  - A surjective `mu` preserves `S`, `A` and each `A_p`.
- **Lemma 5.** The normal subgroups of a product of nonabelian simple groups are its sub-products.
- **Lemma 6.** Take an injective homomorphic automaton on `S^G`. Then:
  - its kernel is a sub-product, and every factor survives, by injectivity;
  - an order count forces exactly one surviving coordinate per factor;
  - so the local rule is `nu(x)_{sigma(i)} = alpha_i(x(m_i)_i)`, and the automaton has the explicit inverse
    `rho(y)(h)_i = alpha_i^-1(y(h m_i^-1)_{sigma(i)})`.
  - This holds for every `G`.

**Theorem A (Section 4), by induction on `|K|`.**
- **Step 0.** The hypotheses pass to quotients of `K^M` of smaller order, since their composition factors are
  among those of `K`.
- **Step 1.** If `H = mu(K^M) != K`, the restriction to `H^G` is surjective by induction. Injectivity then puts
  every configuration in `H^G`, a contradiction. So `mu` is surjective.
- **Step 2.** The socle layers are invariant, by Lemma 4.
- **Step 3.** `tau(S^G) = S^G` by Lemma 6.
- **Step 4.** `tau(A_p^G) = A_p^G`, by the hypothesis at `(p, n_p)` with `p^{n_p} <= |K|`, and Lemma 2.
- **Step 5.** So `tau(Soc(K)^G) = Soc(K)^G`.
- **Step 6.** The quotient automaton on `(K/Soc(K))^G` is injective, by Step 5, hence surjective by induction.
- **Step 7.** Every `y` equals `tau(xz)`.

**Corollaries (Section 5).**
- **Part 1** is Theorem A with Lemma 2.
- **Part 2.** `P(K)` is empty, so the hypothesis is vacuous.
- **Part 3.**
  - Weakly surjunctive implies linearly surjunctive, since linear automata are homomorphic.
  - Linearly surjunctive implies stable finiteness of every `F_p[G]`, by Lemma 2 at `F_p^n`.
  - Stable finiteness of every `F_p[G]` implies weakly surjunctive, by Lemma 2 and Theorem A for every `K`.

Section 7 sanity-checks Lemmas 3, 4 and 6 by exhaustive enumeration for `A_5`, `A_5 × Z/2` and `S_4`. It also
exhibits non-surjective local rules that break socle invariance, which shows why Step 1 is needed. The proof does
not depend on this computation.

---
rg: 2
id: linear-strict-pairs-are-transposes-of-post-surjective-automata
kind: claim
title: A linear automaton is injective and not surjective iff its transpose is post-surjective and not pre-injective
distinct_from:
  stable-finiteness-failure-refutes-surjunctivity: that turns a one-sided inverse over a finite field into a failure of surjunctivity; this shows the same linear data is exactly a failure of the dual (post-surjective implies pre-injective) property of the transpose, over any field.
  split-decoders-have-generic-cantor-fibers: that says a split cellular decoder is pre-injective only when bijective, for arbitrary nonlinear maps; this is the exact linear duality between the two surjunctivity properties.
artifacts:
  - research/artifacts/ideas-gottschalk-2-2026-09-14.md
---

Let `G` be a group, `k` any field, `n >= 1`, and `X = (k^n)^G`, with
configurations written as row vectors. Let `M <= G` be finite and `A_m` in
`M_n(k)` for `m` in `M`.

- The **linear automaton** is `τ(x)(g) = Σ_(m in M) x(gm) A_m`.
- Its **transpose** is `τ^T(x)(g) = Σ_(m in M) x(g m^(-1)) A_m^T`.

Two configurations are **asymptotic** if they differ on a finite set. An
automaton `σ` is:
- **pre-injective** if asymptotic `x != x'` always have `σ(x) != σ(x')`;
- **post-surjective** if for every `x`, every `y'` asymptotic to `σ(x)` equals
  `σ(x')` for some `x'` asymptotic to `x`.

The dual property "post-surjective implies pre-injective" was introduced as a
dual to Gottschalk's conjecture by Capobianco, Kari and Taati. This lane did not
re-pin that source; the claim below does not depend on it.

**Theorem.**
1. `τ` is injective and not surjective iff `τ^T` is post-surjective and not
   pre-injective.
2. Equivalently, both conditions hold iff right multiplication by
   `c = Σ_m A_m^T m` is a surjective, non-injective endomorphism of `k[G]^n`.
   That happens iff `M_n(k[G])` contains `dc = I_n != cd`.
3. So over a fixed field, three things are equivalent:
   - some linear automaton over `G` is injective and not surjective;
   - some linear automaton over `G` is post-surjective and not pre-injective;
   - some `M_n(k[G])` is not directly finite.

In characteristic zero none of them occurs, by Kaplansky's theorem. Over a
finite field every witness for `stable-finiteness-failure-refutes-surjunctivity`
also refutes the linear case of dual surjunctivity for `G`, with the finite
alphabet `k^n`.

The route is `linear-strict-transpose-duality-proof`. It uses only linear
duality between `k[G]^n` and its algebraic dual `X`. Part (3) is the classical
equivalence of linear surjunctivity with stable finiteness
(Ceccherini-Silberstein–Coornaert, not re-pinned here), proved directly in the
route.

---
rg: 2
id: bgw-trivial-coefficient-agreement-is-open
kind: claim
title: Whether the Baum--Guentner--Willett reformulation agrees with the classical conjecture at trivial coefficients is open
distinct_from:
  baum-connes-counterexample-group-exists: that asks for a group whose classical reduced assembly map fails; this records that the exact-crossed-product reformulation is not known to coincide with the classical map at trivial coefficients, so its confirming examples say nothing about that root.
---

**ESTABLISHED (citation)** by `bgw-trivial-coefficient-agreement-is-open-citation`.

Let `⋊_(E_M)` be the smallest exact Morita compatible crossed-product functor.
Baum--Guentner--Willett (Ann. K-Theory 1 (2015)) reformulate Baum--Connes as
bijectivity of `mu_E : K^top_*(G; A) -> K_*(A ⋊_(E_M) G)`. It is **not known**
whether

```text
C*_(E_M)(G) := C ⋊_(E_M) G   equals   C*_r(G)
```

for every discrete group `G`. The published claim that it always does
(Buss--Echterhoff--Willett, *The minimal exact crossed product*, Doc. Math.
2018, Corollary 4.6 with Proposition 2.6) rests on Proposition 4.4. The
authors' erratum withdraws Proposition 4.4 and Corollaries 4.5--4.8.

**Consequences for `baum-connes-counterexample-group-exists`.**
- For exact `G` the two group algebras agree, so a counterexample group must be
  non-exact, as the Higson--Lafforgue--Skandalis monsters are.
- The statement "no counterexample to the reformulated conjecture is known"
  does not bear on the classical conjecture with trivial coefficients.
- `mu_r = q_* ∘ mu_E` with `q : C*_(E_M)(G) -> C*_r(G)` the canonical quotient.
  So if `q_*` is not an isomorphism in K-theory, then the reformulated or the
  classical conjecture fails at trivial coefficients for `G`. No mechanism is
  known that decides either `q = id` or `q_*` for a non-exact group.
- **Surviving positive fact** (erratum, Lemma A.1, due to Ozawa). If a
  crossed-product functor has the ideal property, which the reduced one has,
  then every short exact sequence `0 -> I -> A -> C -> 0` of `G`-algebras gives
  an exact sequence of crossed products. So a quotient onto trivial
  coefficients never witnesses non-exactness.

**Bounded literature check.** One web search (2026-09-12) for a later
resolution found only the erratum.

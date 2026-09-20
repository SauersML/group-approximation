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
- For exact `G` the two group algebras agree. Thus a counterexample to
  **agreement of these completions** must be nonexact. This does not prove
  that every ordinary Baum–Connes counterexample must be nonexact:
  equality of targets establishes neither assembly isomorphism.
  (Scope correction, supplied report, 2026-09-20.)
- The statement "no counterexample to the reformulated conjecture is known"
  does not bear on the classical conjecture with trivial coefficients.
- `mu_r = q_* ∘ mu_E` with `q : C*_(E_M)(G) -> C*_r(G)` the canonical quotient.
  So if `q_*` is not an isomorphism in K-theory, then the reformulated or the
  classical conjecture fails at trivial coefficients for `G`. No mechanism is
  known here that decides either `q = id` or `q_*` for a non-exact group.
  A `q_*` defect selects ordinary failure if `mu_E` is additionally known
  to be an isomorphism for that group; that extra theorem is essential.
- **Surviving positive fact** (erratum, Lemma A.1, due to Ozawa). If a
  crossed-product functor has the ideal property, which the reduced one has,
  then every short exact sequence `0 -> I -> A -> ℂ -> 0` of `G`-algebras, with
  quotient the trivial algebra `ℂ`, gives an exact sequence of crossed products.
  So a quotient onto trivial coefficients never witnesses non-exactness.
  *(Notation fixed by ex-verify2-quantum-l2, 2026-09-13.)* The lemma's printed
  proof starts from `ℂ -> M(A)`, `λ -> λ 1`. For an arbitrary quotient `C` the
  statement would be false: the reduced crossed product has the ideal property
  and is not exact over non-exact groups.

**Bounded literature check.** One web search (2026-09-12) for a later
resolution found only the erratum.

**2026-09-20 recheck.** Appendix A of
[arXiv:1804.02725v3](https://arxiv.org/pdf/1804.02725v3) still explicitly
leaves this completion comparison open. This bounded check is not a
claim that every subsequent manuscript has been searched. The separate
module K-inexactness route requires a non-K-exact host; that is a
restriction on its mechanism, not on every ordinary counterexample.

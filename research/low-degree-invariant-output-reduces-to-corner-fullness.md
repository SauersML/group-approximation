---
rg: 2
id: low-degree-invariant-output-reduces-to-corner-fullness
kind: claim
title: Low-degree invariant-output designs over any F_q die in modular characteristic and are matrix corner-fullness equations over the prime field otherwise
distinct_from:
  linear-invariant-output-automata-fail-augmentation: that classifies the linear invariant-output automata; this shows that every nonlinear design with deg sigma * deg tau < q reduces to the same corner questions, at some matrix size over the prime field.
  invariant-output-rules-need-odd-invariant-monomials: that constrains binary encoders of every degree; this kills or linearizes invariant-output designs of low degree over larger fields.
  ternary-leavitt-swap-idempotent-is-full: that is one scalar corner equation on one host; this shows every low-degree invariant-output design, over any field and any host, is a matrix corner equation for the averaging idempotent over F_p[G].
artifacts:
  - research/artifacts/low-degree-strict-pairs-linear-parts-2026-09-12.md
---

Let `H <= G` be finite with `H != 1`, and `F = F_q` with `q = p^k`. Let `tau` be an injective
automaton over `F^m` whose output is right-`H`-invariant, `tau(x)(gh) = tau(x)(g)`, with a
left inverse `sigma` such that `deg sigma * deg tau < q`.

1. If `p` divides `|H|`, no such pair exists.
2. If `p` does not divide `|H|`, put `e = |H|^-1 sum_(h in H) h` in `F_p[G]`. There are
   `B, C` in `M_(mk)(F_p[G])` with `C (e I) B = I`. Conversely, any such pair gives the
   degree-one design `tau_(eB)` with decoder `tau_C`, whose output is invariant.

So large alphabets and low-degree nonlinear rules built from idempotent projections are no
easier than matrix corner fullness of the averaging idempotent. For
`G_3 = L_(F_3)(1,2)^x` and `H = <w>` this is the matrix form of the ternary swap target.
Over every `F_(2^k)` and every even-order `H`, low-degree designs are dead.

**Why.** Invariance forces `h A = A` on the linear part. Then (1) gives augmentation zero
against `CA = I` from `low-degree-strict-pairs-have-one-sided-linear-parts`, and (2) gives
`e A = A`. Restriction of scalars `F -> M_k(F_p)` moves the equation to the prime field.

Proof: Section 3 of the artifact.

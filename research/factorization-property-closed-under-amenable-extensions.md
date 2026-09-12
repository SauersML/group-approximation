---
rg: 2
id: factorization-property-closed-under-amenable-extensions
kind: claim
title: Kirchberg's factorization property survives every extension by a countable amenable group
distinct_from:
  factorization-property-closed-under-amenable-semidirect-products: that is the split case, proved through the crossed-product identification C*(N rtimes Q) = C*(N) rtimes Q and crossed-product trace permanence; this allows nonsplit extensions, whose full group algebras are twisted crossed products, and is proved directly by inducing representations and compressing to Folner windows.
  amenable-crossed-products-preserve-invariant-amenable-traces: that transports one invariant amenable trace through an honest crossed product by a group action; a nonsplit extension gives no action of the quotient on C*(N), so that theorem does not apply and the argument here works at the level of unitary representations instead.
  literal-group-factorization-property: that is the one-group theorem for E = K rtimes Z with locally residually finite K; this is the general permanence statement whose split-and-locally-RF specialization it is.
artifacts:
  - research/artifacts/factorization-amenable-extensions-2026-09-05.md
---

Let `1 -> N -> G -> Q -> 1` be an extension of countable discrete groups with
`Q` amenable.  If `N` has Kirchberg's factorization property, then so does
`G`.  No splitting of the extension is assumed.

**ESTABLISHED** by `factorization-amenable-extension-induced-compression-proof`.
Equivalently (Brown, Theorem 4.1.9): if the canonical trace of `C*(N)` is
amenable, so is the canonical trace of `C*(G)`.

## Consequences

- With `Q` trivial this is the trivial case; with `N` residually finite it
  recovers residually-finite-by-amenable groups; with `N` locally
  residually finite and `G = N rtimes Z` it recovers
  `literal-group-factorization-property`, and locally residually finite
  groups themselves have the property (finite windows are exact there), so
  the class of factorization groups contains all
  (locally residually finite)-by-amenable groups, split or not.
- The class of counterexamples to STW Problem X(1) is closed under amenable
  extensions and under passage to overgroups with the factorization
  property: if `G_0 <= G`, `G` has the factorization property and the
  canonical trace of `C*(G_0)` is not quasidiagonal, then the canonical trace
  of `C*(G)` is amenable and not quasidiagonal, because the canonical trace
  of `C*(G)` restricts to the canonical trace of `C*(G_0)` and
  quasidiagonality of traces passes to subalgebras.  In particular every
  amenable extension of the literal group `E`, and every group with the
  factorization property containing `E`, refutes X(1).
- The same window construction shows the quasidiagonal analogue is false in
  general: `integer-crossed-products-can-destroy-quasidiagonal-traces` and
  the literal group itself, where `K` is locally residually finite and hence
  has quasidiagonal canonical trace while `K rtimes Z = E` does not.

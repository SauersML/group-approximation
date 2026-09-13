---
rg: 2
id: o2-zp-crossed-products-invert-p-in-kk
kind: claim
title: For every Z_p-action on O_2 the crossed product has p and 1 minus the dual automorphism invertible in its KK-ring
distinct_from:
  barlak-li-p-half-iff-zp-actions-fix-cartan: that imports the equivalence between the UCT at p and Cartan-fixing order-p actions; this is a UCT-free structure theorem for the KK-ring of every O_2 crossed product by Z_p.
  o2-zp-cartan-fixing-all-primes-or-at-most-one: that is the at-most-one-prime dichotomy for Cartan-fixing; this is arithmetic of KK-rings at a single prime with no Cartan or UCT input.
---

**ESTABLISHED (derivation, no UCT input).**  Let `p` be prime and
`α : Z_p ↷ O_2` any action: not necessarily outer, approximately representable
or strongly approximately inner.  Put `C = O_2 ⋊_α Z_p`, with `β = α̂` the
generator of the dual action.  Then in `R = KK(C, C)`:

* `1 − [β]` is a unit;
* `Σ_(k<p) [β^k] = 0`;
* `p · [id_C]` is a unit.

So `R` is a unital algebra over `Z[ζ_p, 1/p]` via `ζ_p ↦ [β]`.  For every
separable `D`, `KK^*(D, C)` and `KK^*(C, D)` are uniquely `p`-divisible
`Z[ζ_p, 1/p]`-modules.  Also `C ⋊_β Z` is KK-contractible.

**Consequences for Problem II.**

1. *Absorption at the level of KK.*  The step of Barlak--Li II Theorem 4.16,
   (i) ⟹ (ii), that
   `research/artifacts/uct-o2-cyclic-actions-2026-09-12.md` §3 flags as
   unverified asserts that `O_2 ⋊_α Z_p` is `M_(p^∞)`-absorbing before the UCT is
   known.  What (i) needs is a KK-equivalence `C ~_KK C ⊗ M_(p^∞)`.  This claim
   supplies its KK-algebraic core: `p` is already a unit in `KK(C, C)`, with no
   UCT, outerness or classification input.  Passing from "`p` invertible" to the
   KK-equivalence with the inductive limit `C ⊗ M_(p^∞)` uses the Milnor `lim^1`
   sequence for KK of an inductive limit in the first variable.  That step is
   recorded separately and is not asserted here.
2. *The per-prime class is a cyclotomic class.*  Every witness at `p` in the
   sense of `nuclear-algebra-without-uct-exists` is `C = O_2 ⋊_α Z_p` with
   `KK(C, C)` a `Z[ζ_p, 1/p]`-algebra.  Conversely, Barlak--Li's realization
   `O_2 ⋊_(id ⊗ γ) Z_p ~_KK Ã^(p−1)` gives `M_(p−1)(KK(Ã, Ã))`, which contains
   `Z[ζ_p, 1/p]` through the companion matrix of `Φ_p`.
3. *No K-theoretic signature from these invariants.*  Any test built from
   `K_*(C)`, `K^*(C)` and the dual action sees `Z[ζ_p, 1/p]`-modules.  Every
   such module with countable underlying group already occurs for UCT algebras:
   take `Ã` with the right K-theory.  So they cannot certify a failure of the
   UCT by themselves.  The certificate must live in non-K-theoretic structure,
   such as the full `KK`-ring, Künneth failures or central sequences.  This
   sentence is a heuristic reading, not a theorem: the realization of the dual
   action on K-theory by a UCT example was not checked.

Proof: `o2-zp-crossed-products-invert-p-in-kk-proof`.

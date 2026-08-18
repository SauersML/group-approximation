---
rg: 2
id: universal-sandwich-ring-proof
kind: route
title: Factor the given sandwich through the universal one
target: universal-sandwich-ring-is-finitely-presented-and-injective
requires: []
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

**Injectivity.**  By the universal property of `U = R<p,q>/(prq-1)` there is
a unital homomorphism

    Phi : U -> B

extending `phi` and sending `p |-> P`, `q |-> Q`.  It is well defined because
the defining relation is respected:

    Phi(prq) = P phi(r) Q = 1_B .

Write `i : R -> U` for the canonical map.  Then `Phi ∘ i = phi`.  Since `phi`
is injective, so is `i`.

**Fullness.**  The relation `prq = 1` exhibits `1 in UrU`, hence `UrU = U`.

**Finite presentation.**  If

    R = Z<x_1,…,x_m>/(f_1,…,f_k)

and `r^` is a word in the `x_i` representing `r`, then

    U = Z<x_1,…,x_m,p,q>/(f_1,…,f_k, p r^ q - 1) ,

which is a presentation with `m + 2` generators and `k + 1` relations.

## The whole content is the direction of the factorization

The lemma is nearly trivial once stated, and it is worth being explicit about
why it was not already in hand.  The tempting reading of Remark 5 is "the
sandwich extension of a finitely presented ring need not be finitely
presented", and under that reading nothing can be done.  The correct reading
is "the *particular* extension we construct, namely a subring of `End(W)`,
carries relations we cannot enumerate".  Those extra relations are exactly
what `Phi` absorbs: they live in `ker(Phi)`, and `U` does not need them.

The one hypothesis that cannot be dropped is injectivity of `phi`.  Without a
target in which the sandwich actually holds, `U` is defined but nothing
prevents `prq = 1` from collapsing `R`; the map `Phi` is the only evidence
that `i` is injective, and there is no intrinsic argument in `U` for it.
This is why the node is stated as a conditional on the existence of `(B, P,
Q)`, and why Chatterji--Kassabov's Lemma 4 — which produces exactly that
data — is the thing being reused, not replaced.

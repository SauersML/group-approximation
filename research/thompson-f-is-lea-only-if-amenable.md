---
rg: 2
id: thompson-f-is-lea-only-if-amenable
kind: claim
title: Thompson's F is locally embeddable into amenable groups only if it is amenable
distinct_from:
  thompson-f-is-sofic: that is soficity of F, which is open; this shows that local embeddability into amenable groups, the easiest sufficient condition for soficity after amenability, collapses to amenability for F.
  thompson-f-is-amenable: that is amenability of F; this shows LEA is equivalent to it, so LEA gives no independent route to soficity.
  lodha-moore-group-is-bi-orderable-and-not-lea: that is the same collapse for the Lodha--Moore group G_0, which is known to be nonamenable and hence not LEA; this is F, whose amenability is open.
---

**ESTABLISHED (unreviewed).** Let `F = <a, b | [ab^-1, a^-1ba], [ab^-1, a^-2ba^2]>` be Thompson's
group. If `F` is locally embeddable into amenable groups (LEA: every finite subset admits a map into
some amenable group that is injective on it and multiplicative on its pairs), then `F` is amenable.
The converse is immediate. So `F` is LEA exactly when `F` is amenable.

**Why it matters.** LEA groups are sofic, so LEA would have been a soficity route for `F` that does
not need amenability. It is not: for `F`, LEA is amenability.

**Scope.** The argument uses only finite presentability and the fact that every proper quotient of `F`
is abelian. It applies verbatim to any finitely presented nonabelian group whose proper quotients are
all abelian.

Derivation: `thompson-f-is-lea-only-if-amenable-proof`.

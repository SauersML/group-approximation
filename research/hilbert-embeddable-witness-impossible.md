---
rg: 2
id: hilbert-embeddable-witness-impossible
kind: claim
title: The Kun--Thom wreath has no Hilbert embeddable weak-soficity witness
invalidates: [clifford-cover-hilbert-embeddable-route, hilbert-embeddable-witness-route]
distinct_from:
  hilbert-embeddable-witness-for-kun-thom-wreath: that asked whether the witness exists; this is its negation, established, and per kernel doctrine exactly one of the pair can ever be established — the question is now decided, negatively.
  two-point-approximation-fails: that is the set-level statement about the coset action; this is its consequence for the weak-soficity witness question, via the recorded necessary-condition route.
  weakly-sofic-not-sofic: that separates weak soficity from soficity using the same wreath; this separates weak soficity from the Hilbert-embeddable class 𝒞_FU on the same wreath — W is weakly sofic but no witnessing lengths can be made conditionally negative definite.
  kun-thom-clifford-extension-not-weak-mf: that settles an operator-norm question about the Clifford cover in the negative; this settles a tracial, normalized-HS question about the wreath's weak-soficity witnesses, and the two metrics are independent — the same independence its own distinct_from records against the witness claim.
  kun-thom-wreath-weak-mf: that asks whether the wreath is MF in the operator-norm matrix-corona sense, still open; this decides the tracial 𝒞_FU-membership question negatively, and neither implies the other.
---

**Theorem.**  The Kun--Thom wreath `W = (⊕_{G/Γ} ℤ/2) ⋊ G` admits no
Hilbert embeddable weak-soficity witness: the claim
`hilbert-embeddable-witness-for-kun-thom-wreath` is **false**, and by
`hilbert-embeddable-is-representation-realized` this reads

```text
W ∉ 𝒞_FU
```

— `W` is not approximable by finite subgroups of unitary groups in
normalized Hilbert--Schmidt, even though it IS weakly sofic
(Glebsky permanence) and its witnesses exist in the general bi-invariant
class.

**Why.**  `witness-yields-two-point-approximation` (established route)
shows any Hilbert embeddable witness would yield a two-point approximation
of the coset action at the marked pair; `two-point-approximation-fails`
shows no such approximation exists.  Contrapositive.

**What this decides, and what it does not.**

1. The Hilbert-embeddable lane of the separation program **closes
   negatively**: the two routes into `hyperlinear-nonsofic-group` that
   required the witness (`clifford-cover-hilbert-embeddable-route`,
   `hilbert-embeddable-witness-route`) are invalidated by this claim.
2. It is the outcome the witness claim's own final paragraph named "a
   genuine obstruction of a new kind": the first explicit group whose weak
   soficity provably cannot be upgraded to `𝒞_FU` membership — weak
   soficity and `𝒞_FU` are separated on `W`.  Since
   `sofic ⊆ 𝒞_FU ⊆ hyperlinear`, this is evidence toward `W` not being
   hyperlinear, but it does NOT prove it: `𝒞_FU`-membership is a priori
   stronger than hyperlinearity, and the gap between them is untouched.
3. Consequently nothing here resolves Question 3.4 by itself.  The
   separation program's live routes are now the Clifford/CE lanes and the
   Leavitt--Steinberg fork; the goal's cheapest mapped plan is unchanged
   (`leavitt-steinberg-hs-unstable`).

**Trust surface.**  Inherited from Kun--Thom 2608.06222 Theorem 4.1
(unrefereed preprint, in-repo verified artifact) through
`normal-closure-fixes-gamma-fixed-algebra`; everything else in the chain
is proved in-repo.

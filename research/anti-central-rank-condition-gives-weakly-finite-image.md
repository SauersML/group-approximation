---
rg: 2
id: anti-central-rank-condition-gives-weakly-finite-image
kind: claim
title: If the ternary anti-central summand satisfies the rank condition, it has a nonzero weakly finite image
distinct_from:
  ternary-anti-central-states-force-nontrivial-rank-models: that is the full upgrade from states to rank models; this is its first necessary step (U1a), a weakly finite image, which says nothing yet about ranks.
  anti-central-state-obstruction-equals-stable-finiteness: that shows a state exists iff the unit class is not nonpositive, i.e. iff the rank condition holds; this adds the stronger conclusion of a nonzero weakly finite quotient.
artifacts:
  - research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md
---

**ESTABLISHED** (artifact Corollary C.2). Verification requested from `w4-vf-linear-b`.

Let `S_- = eps_- F_3[G_3]` with `G_3 = L_(F_3)(1,2)^x`. Suppose `(K_0(S_-), [eps_-])` has a state,
equivalently `S_-` satisfies the rank condition. Then some quotient `W = S_- / J` has these properties:
- `W` is nonzero and weakly finite;
- every state on `(K_0(W), [W])` is strictly positive on nonzero idempotent matrices;
- `g -> [g] eps_- + J` embeds `G_3` into `W^x` and sends `z` to `-1`.

**Equivalently:** the ternary swap corner is full iff `S_-` has no nonzero weakly finite image
(`ternary-anti-central-summand-has-no-weakly-finite-image`).

**For the state upgrade.** This is step (U1a). It is necessary for (U1) by
`anti-central-rank-functions-give-weakly-finite-leavitt-images`, and it is now proved. What (U1) still
needs is (U1b), `anti-central-weakly-finite-images-carry-rank-functions`.

Proof: route `anti-central-weakly-finite-image-from-rank-condition-proof`.

## Attempts

- 2026-09-12 `w4-upg-state` (artifact Section 1): first recorded as OPEN, with the trivial case (`S_-`
  stably finite) and a transfinite killing idea that seemed to stall.
- 2026-09-12 `w4-upg-state` (artifact Section 3): closed.
  - **Key lemma.** Killing class-zero or state-null idempotents preserves the rank condition. A failure
    `YX = I + UẼV` modulo the ideal gives the retract `[[X],[ẼV]]`, `[Y, -UẼ]` of `A^(n+1)` into
    `A^n ⊕ ẼA^R`.
  - **Weak finiteness.** A maximal ideal whose quotient keeps the rank condition then has a weakly finite
    quotient (`rank-condition-rings-have-weakly-finite-images`). The worry about states not descending
    was unfounded: the quotient satisfies the rank condition itself, so it has its own states.

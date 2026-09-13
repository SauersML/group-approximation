---
rg: 2
id: thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3
kind: claim
title: Thompson's V is the quotient of S4 amalgamated with S3 over C2 by four relators
distinct_from:
  bleak-quick-finite-presentations-of-thompson-v: that imports Bleak--Quick's relator lists as words; this reads their three-generator presentation as an amalgam of two finite cone-permutation groups plus four words.
  thompson-v-finitely-presented-infinite-simple: that records finite presentability and simplicity; this identifies one amalgam of finite groups of which V is a four-relator quotient.
---

**ESTABLISHED.** Let `a = (00 01)`, `b = (01 10 11)`, `c = (1 00)` be the Bleak--Quick generators,
acting on the right.
1. `<a, b>` is the group of rigid permutations of the cones `Q = {00, 01, 10, 11}`. It is `S4`,
   presented by `a^2, b^3, (ab)^4`.
2. `<a, c>` is the group of rigid permutations of the cones `P = {00, 01, 1}`. It is `S3`,
   presented by `a^2, c^2, (ac)^3`.
3. `<a, b> ∩ <a, c> = <a>`.
4. Put `G0 = <a, b, c | a^2, b^3, (ab)^4, c^2, (ac)^3>`, the amalgam `S4 *_<a> S3`. The natural map
   `G0 -> V` is onto, and its kernel is the normal closure of the four long words of (2.4):

```text
r5 = (cab^-1aba)^2 cb (cabab^-1a)^2
r6 = a(cb)^2 a(b^-1c)^2 bcabcb^-1cab^-1acb^-1(cb)^2 ab^-1
r7 = ab^-1cbc(ab^-1)^2 cbcb^-1a(b^-1c)^2 babcb^-1cab^-1
r8 = ca(b^-1c)^2 bacabacbc(b^-1ca)^2 b(cb^-1)^2(acb)^2 cb^-1cab^-1
```

So a finite action of `G0` is exactly an `S4`-set and an `S3`-set on one set that agree on `a`. The
soficity form is `thompson-v-sofic-iff-s4-s3-gluings-nearly-fix-long-words`.

Derivation: `thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3-proof`.

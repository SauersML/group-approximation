---
rg: 2
id: stw63-full-tracial-shadow-forbids-joint-z-bridge
kind: claim
title: A full tracial shadow forbids a joint central Jiang--Su bridge
distinct_from:
  stw63-counterexamples-invisible-in-all-vn-shadows: that says von Neumann shadows cannot separate the two embeddings up to approximate conjugacy; this uses a full shadow to rule out the strictly stronger joint-central-bridge mechanism.
  stw63-canonical-free-product-copies-are-aue: that remains the exact open universal-pair orbit problem; absence of a joint bridge does not imply failure of approximate unitary equivalence.
  stw63-zstable-hull-gives-pairwise-uniqueness: that is a positive theorem under pairwise Z-absorption; this proves that the universal full free-product host has no such absorption.
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

Let `B` be unital and let `phi,psi:Z->B` be unital embeddings.  Suppose that
for some free ultrafilter `omega` there are a finite von Neumann algebra `M`
with faithful normal tracial state and a unital homomorphism `theta:B->M`
such that

```text
W*(theta(phi(Z)) union theta(psi(Z)))=M,
M' intersect M^omega = C1.                              (FTS1)
```

Then there is no unital homomorphism

```text
Z -> B_infinity intersect phi(Z)' intersect psi(Z)'.    (FTS2)
```

In particular, if `F=Z*_(C)Z` and `i_0,i_1:Z->F` are the canonical copies,
then the pair `(i_0,i_1)` has no joint central-sequence Jiang--Su bridge.
Consequently the universal bridge claim
`stw63-every-z-pair-has-joint-central-bridge` is false.  This does not decide
whether `i_0` and `i_1` are approximately unitarily equivalent.  It also
shows that `F` is not `Z`-stable.

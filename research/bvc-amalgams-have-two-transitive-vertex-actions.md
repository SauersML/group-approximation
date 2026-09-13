---
rg: 2
id: bvc-amalgams-have-two-transitive-vertex-actions
kind: claim
title: "An amalgam A *_C B with C proper in both factors has BVC only if A and B act 2-transitively on the cosets of C"
---

Let `G = A *_C B` with `C != A` and `C != B`.  If `G` has BVC, then
`|C\A/C| = 2` and `|C\B/C| = 2`.  Equivalently, `A` acts 2-transitively on
`A/C` and `B` acts 2-transitively on `B/C`.

**Corollary.**  If moreover `C` is finite, then `A` and `B` are finite, so
`G` is virtually free.  It then has BVC only if it is virtually cyclic
(von Puttkamer--Wu, arXiv:1607.03790v2, Corollary 3.3(a), for hyperbolic
groups).  Reason: a finite `C` acting transitively on `A/C` minus the base
point forces `A/C` to be finite.

This extends von Puttkamer--Wu Lemma 1.10, the case `C = 1`, where the
double coset condition fails unless both factors have order 2.  With their
Lemma 2.4 (no non-ascending HNN extension has BVC), the splittings a BVC
group can carry are 2-transitive amalgams and ascending HNN extensions.

Proof: `bvc-amalgams-have-two-transitive-vertex-actions-proof`.

**Example.**  Higman's group `<a, b, c, d | a^b = a^2, b^c = b^2, c^d = c^2,
d^a = d^2>` splits as `A *_C B` with `A = <a, b, c>`, `B = <c, d, a>` and `C =
<a, c>` free of rank 2.  Killing `a` maps `A` onto `BS(1,2) = <b, c | c^{-1} b c
= b^2>` and `C` onto `<c>`.  The double cosets `<c> b^k <c>` meet `<b>` in
`{b^{2^i k}}`, so odd `k` give infinitely many of them.  Hence `C\A/C` is
infinite, and Higman's group does not have BVC (the splitting is the standard
one, used here as stated).

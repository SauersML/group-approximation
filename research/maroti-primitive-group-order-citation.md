---
rg: 2
id: maroti-primitive-group-order-citation
kind: route
title: Import Corollary 1.1(ii) of Maroti, On the orders of primitive groups (J. Algebra 2002)
target: primitive-groups-without-alt-have-order-below-50-n-sqrt-n
requires: []
---

Literature import, credited in full.

Attila Maroti, *On the orders of primitive groups*, Journal of Algebra 258
(2002). Author's preprint dated 21 February 2002,
<https://users.renyi.hu/~maroti/primitive.pdf>.

Verified from the text of the author's PDF on 2026-09-17:

* **Theorem 1.1.** "Let G be a primitive permutation group of degree n. Then
  one of the following holds. (i) G is a subgroup of Sm wr S r containing
  (Am)r, where the action of Sm is on k-element subsets of {1, ..., m} and
  the wreath product has the product action of degree n = (m choose k)^r;
  (ii) G = M11, M12, M23 or M24 with their 4-transitive action; (iii)
  |G| <= n * prod_{i=0}^{[log2 n]-1} (n - 2^i) < n^{1+[log2 n]}."
* **Corollary 1.1.** "Let G be a primitive subgroup of Sn. (i) If G is not
  3-transitive, then |G| < n^sqrt(n); (ii) If G does not contain An, then
  |G| < 50 * n^sqrt(n)."
* **Corollary 1.2.** "If G is a primitive subgroup of Sn not containing An,
  then |G| < 3^n. Moreover, if n > 24, then |G| < 2^n."

Corollary 1.1(ii) is the target verbatim. The target's second sentence is
arithmetic: `log(50 n^(sqrt n)) = log 50 + sqrt(n) log n`.

Either weaker classical bound would also serve the only downstream use,
`pair-swap-group-kill-proof`, which needs `log |G| = o(n)`: the paper's
introduction recalls Babai's bound `exp(4 sqrt(n) ln^2 n)` for uniprimitive
groups and Pyber's `n^(32 log2 n)` for doubly transitive groups (n > 400).
Corollary 1.2 (`|G| < 2^n` for `n > 24`) is **not** enough there when
`m = 2`, which is why the sharper Corollary 1.1(ii) is imported.

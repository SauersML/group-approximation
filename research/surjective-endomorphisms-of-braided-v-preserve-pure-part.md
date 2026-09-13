---
rg: 2
id: surjective-endomorphisms-of-braided-v-preserve-pure-part
kind: claim
title: Every surjective endomorphism of braided V maps the pure braided kernel onto itself and has kernel inside it
---

Let `phi: V_br -> V_br` be a surjective endomorphism of the Brin–Dehornoy braided
Thompson group, and let `P_br = ker(V_br -> V)`. Then:

- `phi^{-1}(P_br) = P_br`,
- `phi(P_br) = P_br`,
- `ker phi <= P_br`, and
- `phi` induces an automorphism of `V`.

So `phi` restricts to a surjective endomorphism of `P_br` with the same kernel, and
this restriction is twisted-equivariant: `phi(x p x^{-1}) = phi(x) phi(p) phi(x)^{-1}`.

---
rg: 2
id: fp-simple-nonexact-group-via-free-algebra-linear-groups
kind: route
title: A non-exact finitely generated linear group over F_2<x,y> makes the finitely presented simple Leavitt unit group non-exact
target: fp-simple-nonexact-group
requires: [binary-free-algebra-linear-group-nonexact, char-two-laurent-linear-groups-satisfy-boone-higman, fp-simple-nonsofic-group, exact-groups-are-closed-under-extensions]
---

Unlike `fp-simple-nonexact-group-via-boone-higman`, this route uses no conjecture. It replaces Osajda's group by a linear group over a free algebra, which already embeds in a finitely presented simple group.

1. Suppose `binary-free-algebra-linear-group-nonexact` holds. Then there is a
   finitely generated non-exact `Γ ≤ GL_n(F_2<x,y>)`.
2. By `char-two-laurent-linear-groups-satisfy-boone-higman`, with `q = 2` and
   `m = 2`, `Γ` embeds in `L^x = L_{F_2}(1,2)^x`.
3. By `fp-simple-nonsofic-group`, `L^x` is finitely presented and simple.
   This is its established witness, Khanh arXiv:2609.08428v1 Theorem 6.1,
   together with `binary-leavitt-unit-group-is-simple`.
4. By `exact-groups-are-closed-under-extensions` (Kirchberg--Wassermann),
   subgroups of exact groups are exact. So if `L^x` were exact, `Γ` would be
   exact, contradicting step 1.
5. So `L^x` is a finitely presented simple non-exact group. ∎

**The decomposition this adds.** The target used to have a single route,
through Boone--Higman. It now also has this one, whose only open input is a
question about one explicit residually finite Kazhdan-type family.

The inputs can fail independently. Step 1 is open. Steps 2 to 4 are
established. By `haagerup-hosts-carry-no-weak-expander`, `L^x` is the only
known finitely presented simple host in which an expander-type witness is not
already excluded.

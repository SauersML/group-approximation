---
rg: 2
id: simple-kazhdan-lef-group-of-non-uniform-exponential-growth
kind: claim
title: There is an infinite finitely generated simple Kazhdan LEF group of non-uniform exponential growth
---

**ESTABLISHED (unreviewed; sk-free-8).** Example: `G_X = EL_3(LC(X,F_2) ⋊ Z)` for the Thue–Morse subshift `X` (`substitution-subshift-elementary-groups-non-uniform-growth`).

**Context.**
- Gromov (1981) asked whether exponential growth forces uniform exponential growth. Wilson (2004) gave the first counterexamples; they are residually finite and not simple.
- Kourovka Notebook 21.117(a) asked for a finitely generated simple example. Sauer–Schesler (arXiv:2605.30163) answered it with Thompson's `V`, which is finitely presented and simple but neither Kazhdan nor LEF.
- de la Harpe (2002, §7) asked for a Kazhdan example. Sauer–Schesler (arXiv:2606.15945) answered it with an acylindrically hyperbolic group, which is not simple.

**Novelty (bounded; artifact part 2 §6).** This combines simple, Kazhdan and LEF.
- **Caution.** Hull (Small cancellation in acylindrically hyperbolic groups, arXiv:1308.4345, Theorem 8.6, as quoted by a web search, not opened) gives every countable acylindrically hyperbolic group an infinite finitely generated quotient in which two elements are conjugate iff they have the same order.
- If such a quotient of Sauer–Schesler's group is simple, it is a simple Kazhdan group of non-uniform exponential growth, because quotients do not increase ball sizes.
- So claim "simple Kazhdan" only as a new instance. The distinctive combination here is simple + Kazhdan + **LEF** (V is not LEF, Wilson's groups are not simple, and Hull-type quotients are not known to be sofic).

Route: `simple-kazhdan-lef-non-uniform-growth-from-thue-morse`.

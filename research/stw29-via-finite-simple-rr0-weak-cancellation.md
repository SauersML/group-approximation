---
rg: 2
id: stw29-via-finite-simple-rr0-weak-cancellation
kind: route
title: Weak cancellation for finite simple real rank zero algebras settles Rordam's dichotomy
target: stw99-problem-xxix-rr0-dichotomy
requires: [finite-simple-rr0-algebras-have-weak-cancellation, stw29-counterexample-level-two-fingerprint]
---

Suppose XXIX fails.  By `stw29-counterexample-level-two-fingerprint`
((1) implies (2)) there is a unital simple real-rank-zero `C` with `C` finite and
`M_2(C)` infinite.  By part (c) of the same claim, `C` fails weak
cancellation, with full classes `x = [1_C]` and `y = [1_C] + r` satisfying
`x + [1_C] = y + [1_C]` and `x != y`.  This contradicts the premise
`finite-simple-rr0-algebras-have-weak-cancellation`.

The premise is implied by LX(1) (`finite-simple-rr0-weak-cancellation-via-lx`),
so this route refines `stw99-lx-implies-xxix`.  It uses weak cancellation only
for finite simple unital algebras, and only for the single pair `[1_C]`,
`[1_C] + r` with `[1_C]` as the cancelled summand.

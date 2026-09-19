---
rg: 2
id: kourovka-19-45-yes-implies-the-collatz-conjecture-proof
kind: route
title: "Kohl's semiconjugacy r puts 0..42 in the orbit of 1, which forces the mod-12 mixing hypothesis; Kohl's Prop. 2.2(b) equates transitivity with Collatz"
target: kourovka-19-45-yes-implies-the-collatz-conjecture
requires:
  - ct-z-orbit-transversal-dichotomy-is-collatz-hard
---

Lane proof (bh-free-58, 2026-09-19), not reviewed. The argument is in the body of
`kourovka-19-45-yes-implies-the-collatz-conjecture`. It uses:
- Step 1 of `ct-z-orbit-transversal-dichotomy-is-collatz-hard`: `r(n)` and `r(T(n))` lie in one
  orbit, and `Z = r(Z) ⊔ a(r(Z))`;
- the finite check that 3x+1 trajectories of `1, …, 22` reach `1`;
- Kohl's Prop. 2.2(b), read at source.

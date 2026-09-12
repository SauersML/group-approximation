---
rg: 2
id: hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class
kind: claim
title: A hyperlinear flexibly HS-stable Kazhdan hyperbolic group with b_2 >= 1 carries a persistent degree-two class
distinct_from:
  kazhdan-hyperbolic-hs-stability-kills-hyperlinearity: that produces a non-hyperlinear hyperbolic finite central extension from stability alone; this adds hyperlinearity of the base and extracts the profinite consequence, a prime class surviving every finite-index subgroup
  persistent-degree-two-class-on-hyperbolic-group: that is the open cohomological counterexample target; this proves that the unitary stability premise, for a hyperlinear base, already supplies it
  finite-quotient-caps-cocycle-cheeger-constant: that shows the permutation route of Chapman--Peled is a finite-quotient statement; this shows the unitary route is one too
---

**ESTABLISHED.** Let `Γ` be word-hyperbolic, Kazhdan, hyperlinear, with
`b_2(Γ;Q) >= 1`, and flexibly Hilbert--Schmidt stable. Then `Γ` is residually
finite, and there are a finite-index subgroup `H_0 <= Γ`, a prime `p`, and a class

```text
0 != α in H^2(H_0; C_p),   res(α) != 0 on every finite-index subgroup of H_0.
```

So `H_0` witnesses `persistent-degree-two-class-on-hyperbolic-group`. In
particular `Γ` is not good in Serre's sense.

**Calibration.** Proving flexible HS-stability for a hyperlinear candidate is no
way around the profinite core of Gromov's question. It must prove that a
degree-two class persists in every finite cover. The only escape is a
non-hyperlinear stable `Γ`, which would already be the answer.

DERIVATION
hs-stable-hyperlinear-kazhdan-hyperbolic-persistent-class-proof

---
rg: 2
id: cyclic-energy-excess-recognizer-proof
kind: route
title: Apply the exact Tarski search to the fixed point and exhibit the C2/trivial r.e. family
target: cyclic-energy-excess-recognizer-is-essential
requires: []
---

For finite presentations the proof is immediate from the search in
`cyclic-energy-reverse-kleene-ceiling-proof`: if `(EER1)` held, the program
which halts on the first exact representation with energy above `b_e` would
halt exactly on NONHALT indices. At its Kleene fixed point, halting invokes
the HALT ceiling and contradicts the witness, while nonhalting invokes
`(EER1)` and makes the same exact search halt.

For sharpness of the r.e. boundary, uniformly present

```text
Gamma_e=<x | x^2=1; enumerate x=1 if and only if e halts>,
E(U)=||U-I||_2^2,
a_e=2, b_e=1.
```

If `e` halts, `Gamma_e` is trivial and `beta_e=0<=1`. If `e` does not halt,
`Gamma_e=C2`; its regular energy is `2`, while the exact one-dimensional sign
representation has energy `4`, so `beta_e=4>1`. Every group in the family is
finite and hyperlinear, and every canonical sequence has energy tending to
the regular value, hence at most `beta_e`. Thus the semantic energy clauses
hold, but

```text
beta_e>1 if and only if e does not halt.
```

No uniform semidecision of exact excess exists. Searching representations of
finite relator prefixes gives false positives, and no effective Higman
wrapper can preserve both this HALT collapse and the NONHALT exact excess:
otherwise finite-presentation Tarski search would enumerate `coHALT`.

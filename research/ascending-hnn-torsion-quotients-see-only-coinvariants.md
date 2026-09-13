---
rg: 2
id: ascending-hnn-torsion-quotients-see-only-coinvariants
kind: claim
title: A torsion quotient of an ascending HNN extension is a finite extension of a quotient of a coinvariant group of the base
distinct_from:
  ascending-hnn-action-iff-iterated-cosets: that characterizes actions of an ascending HNN extension through iterated cosets; this describes every torsion quotient of it through the coinvariant groups of powers of the endomorphism.
---

**ESTABLISHED** (proof in `ascending-hnn-torsion-quotients-see-only-coinvariants-proof`).

Let `B` be a group, `phi: B -> B` an injective endomorphism, and
`Gamma = B*_phi = < B, t | t^-1 b t = phi(b), b in B >` the ascending HNN
extension. For `m >= 1` put

```text
M_m = << b^-1 phi^m(b) : b in B >>^B      (normal closure in B)
B_{phi^m} = B / M_m                        (the phi^m-coinvariant group)
```

1. If `pi: Gamma -> Q` is onto a torsion group and `pi(t)` has order `m`, then
   `pi(B)` is a normal subgroup of `Q` of index dividing `m`, and
   `pi|_B` factors through `B_{phi^m}`.
2. `phi` induces an automorphism `phibar` of `B_{phi^m}` with `phibar^m = id`, and
   `Gamma / <<t^m>> ≅ B_{phi^m} x|_{phibar} Z/m`.
3. If `B` is torsion, then `Gamma` has an infinite torsion quotient if and only
   if `B_{phi^m}` is infinite for some `m >= 1`. In that case `Gamma/<<t^m>>`
   is an infinite torsion quotient, and when `Gamma` is finitely presented both
   `Gamma/<<t^m>>` and its finite-index subgroup `B_{phi^m}` are finitely
   presented infinite torsion groups.

**Why it matters for Zaremsky Problem 1.11.** The two standard finitely
presented torsion-by-cyclic groups are such `Gamma`: Grigorchuk's extension of
the first Grigorchuk group, and the Ol'shanskii–Sapir extension of a group of
exponent `n` (arXiv:math/0208237, Theorem 1.1). Killing the stable letter gives a finitely presented torsion group
at once. Item 3 says its size is exactly the size of a coinvariant group of the
base. For `m = 1` this is the construction that Ol'shanskii and Sapir attribute
to E. Rips (arXiv:math/0208237, footnote 5, p. 6): impose `c_i = u_i` with long
words `u_i`. Item 3 shows that no other torsion quotient of `Gamma` can do
better.

Item 3 is an equivalence for the base alone, not a reduction of Problem 1.11: a
finitely presented infinite torsion group `Q` gives `B = Q`, `phi = id`, and
`B_{phi} = Q`. Its value is that it names the one quantity to compute for each
concrete candidate `(B, phi)`.

Novelty: elementary. Not searched beyond the Ol'shanskii–Sapir footnote.

---
rg: 2
id: basilica-group-is-torsion-free-and-contains-every-z-n
kind: claim
title: The Basilica group is torsion-free, contains Z^n for every n, and its substitution endomorphism is injective of infinite index
---

**Statement.** Let `B = ⟨a, b⟩ ≤ Aut(T_2)` be the Basilica group. It is defined by the recursion
`a = (1, b)`, `b = (1, a)ε`. Automorphisms act on the right, `(g, h)` acts as `g` on the subtree
`0T` and as `h` on the subtree `1T`, and `ε` swaps the two subtrees. This is the convention of
Bartholdi–Virág, arXiv:math/0305262v1, Section 1. Then:

1. `a` and `b` have infinite order. The exponent sums `ε_a, ε_b` are well-defined homomorphisms
   `B → Z`, and `B^ab ≅ Z^2`.
2. `B` is torsion-free.
3. For all `x, y ∈ B'`, the automorphism `(x, y)` lies in `B'`. Hence `B` contains `Z^(2^k)` for
   every `k`, and `cd B = ∞`.
4. The map `σ(g) = (a^(ε_a(g)), g)` is an injective endomorphism of `B` with `σ(a) = b^2` and
   `σ(b) = a`. So it is the substitution endomorphism `b ↦ a, a ↦ b^2` of Bartholdi–Virág,
   Lemma 11, and `[B : σ(B)] = ∞`.
5. Let `B~ = ⟨B, t | t^(−1) g t = σ(g)⟩` be the ascending HNN extension along `σ`. It is
   torsion-free and contains `Z^n` for every `n`, so `cd B~ = ∞`. Its Bass–Serre tree has infinite
   valence.

Proof route: `basilica-group-is-torsion-free-and-contains-every-z-n-proof`. The proof uses only the
recursion. Torsion-freeness is classical (Grigorchuk–Żuk, IJAC 12 (2002), 223–246, whose title
asserts it; that paper was not fetched by this lane). Benli–Grigorchuk–de la Harpe
(arXiv:1206.2072, TeX source, lines 423–425) also record that `B` is torsion-free. The route does
not depend on either source.

Uses downstream: `torsion-free-f-infinity-amenable-non-ea-via-basilica-hnn`.

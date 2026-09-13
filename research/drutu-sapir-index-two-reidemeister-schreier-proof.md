---
rg: 2
id: drutu-sapir-index-two-reidemeister-schreier-proof
kind: route
title: Tietze moves, Reidemeister--Schreier and colimits of free products give the structure of the Druţu--Sapir group
target: drutu-sapir-group-index-two-squaring-mapping-torus
requires: []
---

**(DS0).** Adjoin `x = a b a^-1` and `y = a^2 b a^-2`. Then `y = a x a^-1` and
`b = a^-1 x a`. Also `a^2 b^2 a^-2 = (a^2 b a^-2)^2 = y^2`, so the relator reads
`y^2 = b = a^-1 x a`. Eliminate `b`:
`DS = <a, x, y | a^-1 x a = y^2, a^-1 y a = x>`, where the second relation is
`y = a x a^-1`. Conjugation by `a^-1` sends `x ↦ y^2` and `y ↦ x`, and this
extends to the endomorphism `ψ` of `F(x,y)`. The image `<y^2, x>` is free of
rank two, so `ψ` is injective and the presentation is the ascending HNN extension
along `ψ`. By Britton's lemma `F(x,y)` embeds.

**(K1).** Reidemeister--Schreier for the kernel of `a ↦ 1`, `b ↦ 0`, with
transversal `{1, a}`.
- **Nontrivial Schreier generators:** `s(a, a) = a^2 = c`, `s(1, b) = b = b_0`,
  `s(a, b) = a b a^-1 = b_1`. The generator `s(1, a)` is trivial.
- **Rewrite `r = a a b b a^-1 a^-1 b^-1` from coset `1`.** The letters are
  `a` (trivial), `a` (`c`), `b` (`b_0`), `b` (`b_0`), `a^-1` (`s(1,a^-1) = c^-1`),
  `a^-1` (trivial), `b^-1` (`b_0^-1`). This gives `c b_0^2 c^-1 b_0^-1`.
- **From coset `a`.** The letters are `a` (`c`), `a` (trivial), `b` (`b_1`),
  `b` (`b_1`), `a^-1` (trivial), `a^-1` (`c^-1`), `b^-1` (`b_1^-1`). This gives
  `c b_1^2 c^-1 b_1^-1`.

**(K2).** The presentation of `K` is the pushout of two copies of
`<b, c | c b^2 c^-1 = b> ≅ BS(2,1) ≅ BS(1,2)` along `<c>`. `c` has infinite order
in `BS(1,2)`, so `<c> ≅ Z` embeds in both factors. `K` is therefore the amalgamated
free product, and each factor embeds by the normal form theorem.

**(K3).** `c b_i^2 c^-1 = b_i` is equivalent to `c^-1 b_i c = b_i^2`. So `K` is the
HNN extension of `F(b_0, b_1)` along `φ(b_i) = b_i^2`, which is injective since
`b_0^2, b_1^2` generate a free subgroup of rank two. Checking on `x, y`:
`ψ^2(x) = ψ(y^2) = x^2` and `ψ^2(y) = ψ(x) = y^2`.

**(K4).** In an ascending HNN extension `<F, t | t^-1 w t = θ(w)>`:
- we have `t^-1 F t <= F`, so the conjugates `t^k F t^-k` increase with `k`;
- their union `N` is normal and meets `<t>` trivially;
- the quotient by `N` is `Z` (send `F ↦ 0`, `t ↦ 1`);
- `N` is the colimit `colim(F -θ-> F -θ-> ...)`.

For `DS` take `θ = ψ`, and for `K` take `θ = φ`. `φ = ψ^2`, so both colimits
agree. `φ` is the free product of two copies of `×2 : Z -> Z`. Free products are
coproducts and commute with colimits, so
`N ≅ colim(Z -2-> Z -> ...) * colim(Z -2-> Z -> ...) = Z[1/2] * Z[1/2]`.
The action of `a^-1` is the colimit of `ψ`: `x ↦ y^2` on the first factor and
`y ↦ x` on the second. `∎`

**(DS1).** The relator `a a b b a^-1 a^-1 b^-1` is cyclically reduced of length 7.
A proper power `u^k` with `k >= 2` has length divisible by `k`, so `u` would be a
single letter, which is false. Apply Linton--Nyberg-Brodda, Theorem 1.5.1
(Karrass--Magnus--Solitar). `∎`

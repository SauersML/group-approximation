---
rg: 2
id: bleak-quick-finite-presentations-of-thompson-v
kind: claim
title: Bleak and Quick's three-generator and two-generator presentations of Thompson's group V
distinct_from:
  thompson-v-finitely-presented-infinite-simple: that records that V is finitely presented, infinite and simple, through Cannon-Floyd-Parry; this pins three specific relator lists, with their generators as explicit prefix maps, so that a route can use them as words.
---

**ESTABLISHED (literature import).** Maps are written on the right (`w . (gh) = (w . g) . h`),
`(alpha beta)` swaps the cones `alpha C` and `beta C`, conjugation is `t^s = s^-1 t s`.

1. **Theorem 2.1** (the words of Theorem 1.2). `V` is presented by generators
   `a = (00 01)`, `b = (01 10 11)`, `c = (1 00)` and the eight relations (2.3):
   `a^2 = b^3 = (ab)^4 = 1`, `c^(ac) = a`,
   `c = a^(bcacaa^(ba)) a^(b^-1 cacaa^(b^-1 a))`, `[a^(b^-1 cac), a^(b^-1 caca^b a^(b^-1 a))] = 1`,
   `[a^(bcac), a^(b^-1 caca^b a^(b^-1 a))] = 1`, `[a^(bca^(bca)), a^(bcaca^b a^(b^-1 a))] = 1`.
2. **Equation (2.4).** The eight words `a^2, b^3, (ab)^4, c^-1(ac)^2 a`,
   `(cab^-1aba)^2 cb (cabab^-1a)^2`,
   `a(cb)^2 a(b^-1c)^2 bcabcb^-1cab^-1acb^-1(cb)^2 ab^-1`,
   `ab^-1cbc(ab^-1)^2 cbcb^-1a(b^-1c)^2 babcb^-1cab^-1`,
   `ca(b^-1c)^2 bacabacbc(b^-1ca)^2 b(cb^-1)^2(acb)^2 cb^-1cab^-1`
   have the same normal closure in the free group on `a, b, c` as (2.3). The paper reports this as
   the output of a KBMAG reduction.
3. **Theorem 1.3.** `V` is presented by `u = t_(00,01) t_(10,110) t_(10,111)`, `v = (01 10 11)` and
   seven relators `u^6, v^3, (u^3 v)^4` and four longer words (TeX source lines 646-655).

Source: `bleak-quick-finite-presentations-of-thompson-v-citation`.

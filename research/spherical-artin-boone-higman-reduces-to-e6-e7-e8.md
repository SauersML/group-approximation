---
rg: 2
id: spherical-artin-boone-higman-reduces-to-e6-e7-e8
kind: claim
title: Permutational Boone--Higman for every spherical-type Artin group reduces to the three types E6, E7, E8
---

**Statement.** Suppose the Artin groups `A(E_6)`, `A(E_7)` and `A(E_8)` satisfy
the permutational Boone--Higman property: each embeds in a finitely presented
simple twisted Brin--Thompson group. Then every Artin group of spherical type
has that property. In particular, every spherical-type Artin group embeds in a
finitely presented simple group.

**Derivation.**
1. **Crisp** (*Injective maps between Artin groups*, 1999), as quoted in Paris,
   arXiv:0711.2372, §6, p. 45: "any spherical type Artin group embeds in a
   direct product of Artin groups of type A_n (n ≥ 1), D_n (n ≥ 4), and E_k
   (k = 6,7,8)". Read from the PDF, extracted on MSI.
2. **Types A and D.** BFFHZ arXiv:2503.21882, Theorem A (permutational form for
   `Aut(F_n)`) and Corollary B (braid groups; Artin groups of types `B_n`, `D_n`,
   `I_2(m)`, `Ã_n`). Embedding in a twisted Brin--Thompson group passes to
   subgroups.
3. **Products.** Satisfying the permutational Boone--Higman conjecture is closed
   under direct products. This is recorded in
   `research/artifacts/boone-higman-frontier-2026-09-12.md` ("PBH closed under
   commensurability, direct products and free products", from BFFHZ and
   [Zarb]).

So a direct product of type A, D and E factors satisfies PBH once the three E
factors do, and every spherical-type Artin group embeds in such a product.

**Scope and trust.**
- Crisp's theorem is read through Paris's survey, not from the primary source.
  The closure of PBH under direct products is taken from the frontier
  artifact's reading of BFFHZ and was not re-read here.
- Nothing about `E_6`, `E_7`, `E_8` is proved. Two facts from the same survey
  bound the obvious attacks:
  - **Linearity.** The Digne and Cohen--Wales LKB representations are faithful
    over `K = Q(x,y)` (§6.1 and Corollary 6.5). That field is outside
    Zaremsky's `GL_n(Q)` theorem, and no rational specialization is proved
    faithful in the survey.
  - **Monodromy.** The Perron--Vannier geometric monodromy is faithful exactly
    for types `A_n` and `D_n` (§7.1, citing Perron--Vannier, Labruère and
    Wajnryb). So it does not put the E types inside a mapping class group with
    boundary.
- This is a special-class reduction. It gives no mechanism for the full
  conjecture.

DERIVATION
spherical-artin-bh-reduction-proof

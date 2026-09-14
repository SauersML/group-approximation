---
rg: 2
id: z-presentations-trivializing-relator-ac-equivalence-proof
kind: route
title: Proof that trivializing relators over a presentation of Z are AC-equivalent
target: z-presentations-with-a-trivializing-relator-are-ac-equivalent
requires: []
---

Write F = F(x_1, …, x_n), N = ⟨⟨r_1, …, r_{n−1}⟩⟩ and R = (r_1, …, r_{n−1}).

**Step 1: replacing w modulo N (AC composite).** For any u ∈ F, any j and ε = ±1,
the move w ↦ w · u r_j^ε u^{−1} is a composite of AC moves:
- apply (AC3) to r_j letter by letter to reach u r_j u^{−1};
- apply (AC2) if ε = −1;
- apply (AC1) to w;
- undo the changes to r_j.

Every element m ∈ N is a product of such conjugates. So w can be replaced by w·m
for any m ∈ N, i.e. by any w' ≡ w mod N.

**Step 2: reduce w to a power of x.** In F/N ≅ Z the element x is a generator, so
w ≡ x^p mod N for some p ∈ Z. By Step 1 the presentation (R, w) is AC-equivalent
to (R, x^p). The group ⟨x_1, …, x_n | R, w⟩ is trivial and equals Z/⟨p⟩, so p = ±1.
If p = −1, apply (AC2). This gives (R, x).

This follows the printed proof of Shehper et al. (`sec/stable.tex` l.209–213) and
adds only the explicit AC realization in Step 1. Elementary; no novelty claimed.

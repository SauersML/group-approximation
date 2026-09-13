---
rg: 2
id: artin-sigma1-conjecture-known-families
kind: claim
title: "The Sigma^1-conjecture holds for trees, circuit rank at most 2, the prime-p family, balanced and coherent Artin groups, and several further families"
---

The equality `Σ^1(A_Γ) = {[χ] : Liv^χ connected and dominant}` of
`artin-sigma1-is-connected-dominant-living-subgraph` holds whenever `Γ` is in one of
these families:

1. `Γ` has all labels 2 (right-angled; Meier–VanWyk, Proc. LMS 71 (1995) 263–280);
2. `Γ` is complete and all edges have the same label (Meier, Proc. LMS 74 (1997));
3. `Γ` is a tree (Meier–Meinert–VanWyk, Topology Appl. 110 (2001) 71–81);
4. `Γ` is connected and `π_1(Γ)` is free of rank 1 (Almeida–Kochloukova,
   Forum Math. 27 (2015) 2901–2925);
5. a certain family of complete graphs on 4 vertices (Almeida–Kochloukova,
   Comm. Algebra 43 (2015) 702–728);
6. a family of minimal graphs of arbitrary circuit rank (Almeida, J. Group Theory
   20 (2017) 793–806, arXiv:1605.00271);
7. `Γ` is connected and `π_1(Γ)` is free of rank 2 (Almeida, J. Group Theory 21
   (2018) 189–228);
8. `Γ` is even and every closed reduced path whose labels all exceed 2 has odd
   length (Kochloukova, Pacific J. Math. 312 (2021) 149–169, arXiv:2009.14269);
9. some prime `p` divides `l(e)/2` for every even `l(e) >= 4`
   (Escartín-Ferrer–Martínez-Pérez, arXiv:2309.03091v2, Theorem 1.3);
10. `A_Γ` is balanced (Escartín-Ferrer, arXiv:2501.08692v3, Definitions 2.2–2.4 and
    Theorem 1.2): collapse odd edges and delete label-2 edges; the resulting
    multigraph of even labels `>= 4` has a colouring by primes `p_i | l(e)/2`
    such that every closed path of even length contains exactly two or zero
    edges of each colour;
11. `A_Γ` is coherent (arXiv:2501.08692v3, Corollary 4.11), which covers family 8.

Families 9–10 come from finite abelian twisted homology of the kernel (Lemma 3.4,
Theorem 4.4 of arXiv:2501.08692v3). No family above contains, for example, a
complete graph on four vertices with two label-2 edges `u1u2`, `v1v2` and cross
labels `4, 4, 4, 6` on the 4-cycle `u1 v1 u2 v2` (circuit rank 3; the halves 2
and 3 are coprime; not balanced). Family 5 was not checked for that graph.

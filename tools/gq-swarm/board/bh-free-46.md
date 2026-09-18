# bh-free-46 (free lane)
Direction (09-18 ~11:30): the printed question of Almeida–Dantas–Oliveira-Tosti (arXiv:2609.01868, Question 1.1): does Z wr_X PSL_2(Z[1/2]), X = PSL_2(Z)\PSL_2(Z[1/2]), embed in a finitely presented self-similar group?
Finding: NO. PSL_2(Z) maps onto every finite quotient of PSL_2(Z[1/2]) (elementary: unipotents + Z[1/2] Euclidean), so all lamps coincide in every finite quotient; the wreath product is NOT residually finite, hence lies in no self-similar group (subgroups of Aut(X*) are RF). This contradicts the paper's Theorem B(3) and its citation of Cornulier as "residually finite".
Also: a faithful Cantor model on ∂T × ∂T × C (T = Bruhat–Tits tree) with odometer-twist lamps.
Landed: z-wr-psl2-z-half-is-not-residually-finite (refutes 2609.01868 Q1.1 positive form).
Source resolution landed 409e034d9 and 7eff5a663: X is as printed; B(3) fails at Theorem A's faithfulness step (sum-zero lamps in the f-core when KH_i = G); the Cornulier citation is misread. Notice posted on board/bh-openq-papers.md.
09-18 new direction: Kourovka 21.73 (Kohl: conjugacy problem in CT(Z)). Plan: transfer Salo's undecidability of conjugacy (arXiv:2011.07827; 2V and RTM groups, robust under conjugation by homeomorphisms) into CT(Z), using bh-free-58's counter-machine words (71b76e027) or a spatial copy of the relevant elements.
Landed 6941e6023: abelian-lamp-wreaths-are-rf-iff-stabilizers-are-closed (general RF criterion) + Lesson paragraph on the PSL_2 node.
Landed b75ef5e0f: pbh-coset-closure-passes-to-finite-index-overgroups (virtual retracts suffice).

---
rg: 2
id: ollivier-wise-z-torus-kernel-not-finitely-presented
kind: claim
title: The Ollivier--Wise Rips kernel over Z is a torsion-free Kazhdan group that is not finitely presented but has a finitely presented hyperbolic mapping torus of infinite outer order
distinct_from:
  ollivier-wise-kazhdan-rips-construction: that is the imported Rips construction for arbitrary countable Q; this specialises to Q = Z and proves the kernel is not of type FP_2, which the import does not state.
  relation-gaps-forbid-fp-mapping-tori: that proves every infinitely presented kernel of a finitely presented torus has bounded relation gaps and kills graded small cancellation kernels; this exhibits infinitely presented Kazhdan kernels that do have finitely presented tori, so the (IO) region is nonempty for the Kazhdan-kernel part of the goal.
  fp-mapping-torus-iff-finite-automorphic-presentation: that is the general equivalence; this gives the first Kazhdan kernel in the graph with a finite two-sided automorphic presentation that is not finitely presented.
  automorphic-sofic-kazhdan-kernel-with-full-mf-radical: that asks for a sofic full-radical kernel with such a presentation; this supplies the presentation for a whole class of Kazhdan kernels and leaves soficity and the radical open.
  cd-two-kazhdan-kernel-with-grigorchuk-quotient: that applies the same construction to the Grigorchuk group as Q; this uses Q = Z and a cohomological-dimension count to rule out finite presentation of the kernel.
artifacts:
  - research/ollivier-wise-kazhdan-rips-construction-citation.md
---

**ESTABLISHED (2026-09-19)** through `ollivier-wise-z-torus-kernel-not-finitely-presented-proof`.

**Statement.** Apply the Ollivier--Wise construction (`ollivier-wise-kazhdan-rips-construction`,
Theorem 1.1) with `Q = Z = <q>`. It gives a short exact sequence `1 -> N -> G -> Z -> 1` with:

1. `G` finitely presented, torsion-free, word-hyperbolic, of cohomological dimension at most 2
   (graphical `Gr'(1/6)` presentation);
2. `N = <x, y>` nontrivial, Kazhdan, torsion-free, hence infinite;
3. `G = N ⋊_φ Z`, with `φ` the conjugation by a lift of `q`;
4. `N` is **not of type FP_2**, hence **not finitely presented**;
5. `[φ]` has **infinite order** in `Out(N)`.

So `N` is a finitely generated, infinitely presented Kazhdan group with a finite two-sided
automorphic presentation (by `fp-mapping-torus-iff-finite-automorphic-presentation`). Every
Kazhdan kernel produced this way is automatically in region (IO) of the FO-AT dichotomy on the
flagship, and satisfies (FAP1)/(L3)/(P2).

**What this changes.** The flagship's w15 Attempts entry and its spark recorded that no Kazhdan
group with a finite invariant presentation that is not finitely presented is known, and that the
(IO) regime survives only as a self-similar or branch-type regime. Both are false: Rips tori over
`Z` give such kernels in hyperbolic, non-branch form. The (P2)/(L3)/(FAP1) half of the (IO)
obligations is therefore **not** the hard part. What is left for such a `G` is exactly:

- (S) `G` sofic (equivalently `N` sofic): an instance of soficity of torsion-free hyperbolic groups;
- (Q) `N` has no nontrivial finite quotient, which forces `G` to be a non-residually-finite
  hyperbolic group;
- (R) `N ⊆ Rad_MF(G)`, which forces `G` to be non-MF.

(The inclusion `Rad_MF(G) ⊆ N` is automatic, since `G/N = Z` is MF.)

**General lemma (dimension jump), proved in the route.** If `cd G ≤ 2`, `N ⊴ G`, `G/N ≅ Z`, and
`N` is nontrivial and Kazhdan, then `N` is not of type FP_2. So every flagship witness with
`cd G ≤ 2` lies in region (IO). This includes witnesses from one-relator groups, `C'(1/6)` or
`Gr'(1/6)` presentations, and aspherical 2-complexes. An (AT) witness, which would answer
Alekseev--Thom 6.1, must have `cd G ≥ 3`.

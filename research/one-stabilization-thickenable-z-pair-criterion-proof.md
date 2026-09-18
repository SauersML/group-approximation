---
rg: 2
id: one-stabilization-thickenable-z-pair-criterion-proof
kind: route
title: Proof that an orientably thickenable Z-pair in the move orbit certifies one-stabilization AC-triviality
target: one-stabilization-ac-trivial-from-thickenable-z-pair
requires:
  - z-presentations-with-a-trivializing-relator-are-ac-equivalent
  - one-stabilization-ac-trivial-from-primitive-relator
---

All manifolds and complexes are PL. F = F(a, b, c) and r = (r_1, r_2) is a Z-pair. K is the
presentation 2-complex of ⟨F | r_1, r_2⟩, with one vertex, three edges and two 2-cells. We
use Step 0 (property T), Steps 1–3 (T is invariant under (P1), (P2)) and Step 5
(projection) of `one-stabilization-primitive-relator-criterion-proof`.

**Lackenby's theorem.** Lackenby, arXiv:2606.06122, Theorem 1.3 (completing Guo): any
thickenable balanced presentation of the trivial group can be converted to a standard
presentation by Andrews–Curtis moves.
- His relators are words in the letters x_i^{±1}, not necessarily freely reduced. Free
  reduction and insertion of g g^{−1} are among his moves.
- So if the complex of a presentation with unreduced relator words embeds in a 3-manifold,
  the presentation with the reduced relators is AC-trivial in the sense of this repository.
  Free reduction does not change the element of F.

## Step 1: the handle structure

Suppose K embeds in an orientable 3-manifold M. Let N be a regular neighbourhood of K in M.
As in Lackenby, proof of Thm 7.3, N has a handle decomposition with:
- one 0-handle and three 1-handles, together a genus-3 handlebody H;
- two 2-handles h_1, h_2, attached along curves c_1, c_2 ⊂ ∂H.

Read in π_1(H) = F, each c_i is a conjugate of r_i^{±1}. Then:
- N collapses onto K, so N is homotopy equivalent to K and π_1(N) ≅ Z;
- N is compact, connected and orientable, with χ(N) = χ(K) = 1 − 3 + 2 = 0.

## Step 2: ∂N is a torus

**∂N ≠ ∅.** A closed orientable 3-manifold has H_3 ≅ Z, but H_3(N) = H_3(K) = 0.

**The components.** Let ∂N = F_1 ⊔ … ⊔ F_m with F_i of genus g_i.
- χ(∂N) = 2χ(N) = 0 gives Σ(2 − 2g_i) = 0, i.e. m = Σ g_i.
- Half lives, half dies: the image of H_1(∂N; Q) → H_1(N; Q) has dimension
  ½ dim H_1(∂N; Q) = Σ g_i. It is at most dim H_1(N; Q) = 1.
- So 1 ≤ m = Σ g_i ≤ 1, and ∂N is a single torus.

## Step 3: N is a solid torus

**A compressing disc.** π_1(∂N) = Z² → π_1(N) = Z is not injective. By the loop theorem
there is a properly embedded disc D ⊂ N whose boundary is essential in ∂N. An essential
simple closed curve on T² does not separate T², so D does not separate N.

**Cut along D.** Cutting N along D gives a compact connected N′ with ∂N′ ≅ S². Then
π_1(N) ≅ π_1(N′) ∗ Z. Since this is Z, Grushko gives π_1(N′) = 1. Gluing a ball to N′
gives a closed simply connected 3-manifold, which is S³ (Perelman). By Alexander's theorem
(Schoenflies in S³), N′ ≅ B³. So N is B³ with one orientable 1-handle, i.e. N ≅ S¹ × D²,
with meridian disc D.

## Step 4: a trivializing relator whose complex is thickenable

**A longitude.** Choose a simple closed curve λ ⊂ ∂N meeting ∂D transversely in one point.
There is a homeomorphism N ≅ S¹ × D² taking D to {pt} × D². It takes λ to a curve meeting
∂D once, i.e. to a longitude, up to Dehn twists along ∂D, which extend over N. So
N ∪_λ h ≅ B³, where h is a 2-handle attached along λ.

**Off the top discs.** ∂N consists of:
- ∂H minus the attaching annuli of h_1 and h_2;
- the four discs D² × {0}, D² × {1} of h_1 and h_2.

By a general-position isotopy, λ misses the four discs and so lies in ∂H. Then
B = H ∪ h_1 ∪ h_2 ∪ h is a handle decomposition of the 3-ball.

**The complex.** Let w be the word read by λ in the cocores of the 1-handles. B collapses
onto the 2-complex with one vertex, three edges and 2-cells attached along c_1, c_2, λ.
This is the presentation complex of ⟨F | c_1, c_2, w⟩, with unreduced words allowed. It
embeds in B ⊂ S³, so it is thickenable.

**AC-triviality.** π_1(B) = 1, so ⟨F | r_1, r_2, w⟩ presents the trivial group.
- By Lackenby's theorem, ⟨F | c_1, c_2, w⟩ is AC-trivial.
- c_i is a conjugate of r_i^{±1}, so it is (AC2)/(AC3)-equivalent to r_i.
- Hence ⟨F | r_1, r_2, w⟩ is AC-trivial, and **T(r) holds**.

This proves **Theorem 1**: every orientably thickenable Z-pair r satisfies T(r).

**Absent generators.** If a generator occurs in neither relator, then K = K′ ∨ S¹, where
K′ is the complex on the other generators. If K′ embeds in an orientable M′, then K embeds
in M′ with an orientable 1-handle added. So the thickenability test may ignore absent
generators. This is what `thzsearch.c` does: it passes only the letters that occur to
`thick2.c`.

## Step 5: assembly

- Suppose moves (P1), (P2) carry (s_1, s_2) to an orientably thickenable Z-pair r.
- By Theorem 1, T(r) holds.
- By Steps 2–3 of `one-stabilization-primitive-relator-criterion-proof`, T is invariant
  under both moves, so T(s_1, s_2) holds.
- By Step 1 of that route, S⁺ is AC-trivial. ∎

**Projection form.** Let r be reached from (s_1, s_2) with m_g = ±1, and suppose the
rank-2 projection P(r) is thickenable.
- P(r) presents the trivial group (Step 5(ii) of that route).
- Lackenby's theorem makes P(r) AC-trivial in rank 2, so P(r)⁺ is AC-trivial.
- By Step 5(iii) of that route, S⁺ is AC-trivial. ∎

## Remarks

**Orientability and the checker.** `thick2.c` decides whether the complex embeds in an
orientable 3-manifold. It uses Neuwirth's criterion on the Whitehead graph with orientable
1-handles.
- The convention is calibrated on ⟨x | x³⟩, whose complex lies in L(3,1). It is
  thickenable with the reversed rotation and not with the same one.
- The same file is used by `thickenable-balanced-presentations-have-meridional-relators`,
  where it was cross-checked against a brute-force embedding test on 2629 presentations.
- Non-orientable embeddings are not searched. The criterion is stated only for orientable
  ones.

**The Z hypothesis is used exactly in Steps 2–3.** For (x², y³), K is thickenable, but
π_1(N) = Z/2 ∗ Z/3 ∗ Z, so N is not a solid torus. No w as in Step 4 exists,
because ⟨F | x², y³, w⟩ is never trivial: Z/2 ∗ Z/3 ∗ Z has rank 3, by Grushko.
`thzsearch.c` flags (x², y³) as thickenable at the start state, so the search must, and
does, restrict to Z-pairs reached from (s_1, s_2).

**The goal is weaker than a primitive entry but not implied by it.** Thickenability is not
invariant under Aut(F). The primitive endpoint of the primitive-relator route is carried
by (P1)-composites and an automorphism to the thickenable pair (a, b). The search
therefore tests both targets.

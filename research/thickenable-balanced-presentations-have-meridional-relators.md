---
rg: 2
id: thickenable-balanced-presentations-have-meridional-relators
kind: claim
title: In a thickenable balanced presentation of the trivial group each relator is a knot meridian modulo the others, which rules out second-relator routes from AK(n) to a thickenable presentation
distinct_from:
  andrews-curtis-conjecture: that is the conjecture for all balanced presentations; this is a necessary condition for thickenability, which by Lackenby–Guo is sufficient for AC-triviality, plus an obstruction for one family of routes
artifacts:
  - experiments/ac-thickenable-orbit-2026-09-17/meridian_lemma_test.py
  - experiments/ac-thickenable-orbit-2026-09-17/meridian_lemma_test_out.txt
  - experiments/ac-thickenable-orbit-2026-09-17/meridian.py
---

**Proposed ESTABLISHED** through `thickenable-meridional-relators-proof`. Unreviewed.

**Why it matters.** Lackenby (arXiv:2606.06122, Thm 1.3, completing Guo) proves that a
thickenable balanced presentation of the trivial group is AC-trivial. The basis is
thickenable, so a balanced presentation P of the trivial group is AC-trivial iff its
AC-orbit contains a thickenable presentation. This node gives a necessary condition for
thickenability, and uses it to rule out one family of routes to such a presentation.

## Theorem A (meridian lemma)

Let P = ⟨x_1, …, x_n | r_1, …, r_n⟩ be a thickenable balanced presentation of the
trivial group. Fix j and put G_j = F(x_1, …, x_n)/⟨⟨r_i : i ≠ j⟩⟩. Then G_j is the group
of a knot K_j ⊂ S^3, by an isomorphism G_j ≅ π_1(S^3 − K_j) that sends the class of r_j
to a meridian of K_j, up to conjugacy and inversion.

For n = 2: F/⟨⟨r_1⟩⟩ is a knot group and r_2 is a meridian of that knot.

## Corollary B (torus relators)

Let p, q ≥ 2 be coprime. Let (r_1, r_2) be a balanced presentation of the trivial group on
x, y with F/⟨⟨r_1⟩⟩ ≅ T(p,q) = ⟨x, y | x^p = y^q⟩. Let Z be the centre, and fix any
isomorphism T(p,q)/Z ≅ Z/p ∗ Z/q. If (r_1, r_2) is thickenable, then the image of r_2 in
Z/p ∗ Z/q is conjugate to an element of cyclic syllable length 2.

**Exact form when r_1 = x^p y^{−q}.** The exponent sum of r_2 in H_1(T(p,q)) = Z is
±1, since the group is trivial. Among such elements, cyclic syllable length 2 means
exactly that r_2 is conjugate to (x^n y^m)^{±1}, where qn + pm = 1. `meridian.py`
(`torus_meridian_ok`) tests this exactly. Every such presentation is AC-trivial by an
elementary Euclidean argument (Step 5 of the route), with no appeal to Lackenby. So for a
torus relator we get the chain: thickenable ⇒ meridional ⇒ AC-trivial by elementary
moves.

## Corollary C (AK(n), second-relator routes)

For n ≥ 2 let AK(n) = ⟨x, y | x^n y^{−(n+1)}, xyxy^{−1}x^{−1}y^{−1}⟩. Let Ω_n be the set of
presentations (r_1', r_2') with the following properties:
- for some automorphism φ of F_2, r_1' is a word representing a conjugate of
  φ(x^n y^{−(n+1)})^{±1};
- r_2' represents, in F/⟨⟨r_1'⟩⟩, a conjugate of the image of xyxy^{−1}x^{−1}y^{−1} or its
  inverse under φ.

Ω_n is exactly what AC moves acting on the second relator alone reach, closed under
automorphisms of F_2. **No presentation in Ω_n is thickenable.** Along such routes
Lackenby–Guo can never be applied.

The reason: in Z/n ∗ Z/(n+1) the relator xyxy^{−1}x^{−1}y^{−1} maps to the cyclically
reduced word x·y·x·y^{−1}·x^{−1}·y^{−1}, of syllable length 6.

**Calibration.** AK(2) is AC-trivial, yet Ω_2 contains no thickenable presentation. So
the corollary is not an inequivalence statement. It says that every trivialization of
AK(n) must at some point leave Ω_n: it must replace the first relator by a word that is
not a conjugate of an automorphic image of x^n y^{−(n+1)} or its inverse. The known
trivializations of AK(2) do this.

**Test run.** `meridian_lemma_test.py 8 5` covers T(2,3), T(3,2), T(3,4), T(2,5) and
T(3,5), and every r_2 of length ≤ 8 with exponent sum ±1:
- every thickenable (x^p y^{−q}, r_2) whose r_2 is not meridional has a nontrivial group,
  shown by a representation to S_5;
- GAP gives order 120, the binary icosahedral group, for the three it was asked about.

No pair contradicts Theorem A.

**Novelty.** The topology is elementary: the Heegaard splitting from Lackenby's proof of
Thm 1.3, plus Burde–Zieschang. A literature search was not done beyond Lackenby's paper,
which does not state it.

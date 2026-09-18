---
rg: 2
id: thickenable-z-pair-split-quotient-meridian-proof
kind: route
title: Proof that in a thickenable Z-pair a relator with freely decomposable one-relator quotient has its partner as a knot meridian, why the hypothesis is needed, and the AK(n) one-relator-route corollary
target: thickenable-z-pairs-split-quotient-meridian-obstruction
requires:
  - one-stabilization-ac-trivial-from-thickenable-z-pair
  - thickenable-balanced-presentations-have-meridional-relators
---

All manifolds and complexes are PL. Put F = F(x, y, z).

## Setup

Let (r_1, r_2) be a thickenable Z-pair, and let N ⊂ M be a regular neighbourhood of its
complex in an orientable 3-manifold, with the handle decomposition H ∪ h_1 ∪ h_2 of
Step 1 of `one-stabilization-thickenable-z-pair-criterion-proof`. By Steps 2–3 of that
route, N ≅ S¹ × D², so N embeds in S³.

Fix {i, j} = {1, 2} and assume G_j = F/⟨⟨r_i⟩⟩ is freely decomposable. Let E = H ∪ h_i and μ = c_j ⊂ ∂E, so N = E ∪_μ h_j.
- By van Kampen, π_1(E) = F/⟨⟨r_i⟩⟩ = G_j, and μ represents a conjugate of r_j^{±1}.
- E ⊂ N ⊂ S³.
- χ(E) = 1 − 3 + 1 = −1.
- E is N with a regular neighbourhood of the cocore arc of h_j removed. That arc is
  properly embedded, so ∂E is connected, and ∂E is a closed orientable surface of genus 2.

**Facts about E.**
- **(E1)** *E is irreducible.* A 2-sphere in E bounds a ball in S³ on each side. The side
  not meeting the connected surface ∂E lies in E.
- **(E2)** *H_2(E) = 0.* By Alexander duality H_2(E) ≅ H̃^0(S³ − E) = 0, since S³ − E is
  connected (∂E is connected).
- **(E3)** *μ does not separate ∂E, and is essential in ∂E.* Adding a 2-handle along a
  separating curve disconnects the boundary. If μ separated ∂E, including the case where
  it bounds a disc there, then ∂N would be disconnected. But ∂N is a torus.

- **(E4)** *∂E is compressible in E.* Suppose not. E is compact and irreducible, with
  incompressible boundary, and π_1(E) = G_j = A ∗ B with A, B ≠ 1. By the Kneser
  conjecture for manifolds with incompressible boundary (Hempel, *3-Manifolds*, Thm 7.1),
  E = E_1 # E_2 with π_1(E_1) ≅ A and π_1(E_2) ≅ B. Neither E_k minus a ball is a ball,
  because both have nontrivial π_1. So the splitting sphere is essential, contradicting (E1).

This is the only place where the hypothesis on G_j is used, and it cannot be dropped: see
Step 3½.

## Step 1: a compressing disc disjoint from μ

We use Jaco's handle addition lemma (W. Jaco, *Adding a 2-handle to a 3-manifold: an
application to property R*, Proc. AMS 92 (1984) 288–292; see also Casson–Gordon). Let M be
a 3-manifold with ∂M compressible, and J ⊂ ∂M a simple closed curve with ∂M − J
incompressible in M. Then M[J] has incompressible boundary.

Here ∂E is compressible by (E4), and E[μ] = N is a solid torus with compressible boundary.
So ∂E − μ is compressible: there is a properly embedded disc
D′ ⊂ E with ∂D′ ⊂ ∂E − μ, and ∂D′ bounds no disc in ∂E − μ. Since μ is essential (E3),
∂D′ does not bound a disc in ∂E either.

**Separating in E and in ∂E agree.** If ∂D′ separates ∂E into F_1 and F_2, then D′ ∪ F_1
is a closed surface in E. By (E2) it separates E, so D′ separates E. Conversely, if ∂D′
does not separate ∂E, a loop in ∂E crossing ∂D′ once, pushed in, meets D′ once, so D′ does
not separate E.

## Step 2: case (a), D′ does not separate E

Cut E along D′ to get E″.
- ∂E″ is a torus, since ∂D′ is essential and nonseparating in the genus-2 surface.
- π_1(E) ≅ π_1(E″) ∗ Z.
- μ ⊂ ∂E″, and N cut along D′ is E″ ∪_μ h_j. Hence
  Z ≅ π_1(N) ≅ π_1(E″ ∪_μ h_j) ∗ Z, and π_1(E″ ∪_μ h_j) = 1 by Grushko.

**μ is essential on ∂E″.** Otherwise μ bounds a disc Δ ⊂ ∂E″, and there are three cases.
- Δ contains neither copy of D′ (the scars): then μ bounds a disc in ∂E, contradicting
  (E3).
- Δ contains both scars: then μ separates ∂E, contradicting (E3).
- Δ contains exactly one scar: then μ cobounds an annulus in ∂E with ∂D′. So μ bounds a
  push-off D″ of D′ in E. The sphere D″ ∪ (core of h_j) ⊂ N meets a loop crossing D′ once
  in one point. So it is a nonzero class in H_2(N), contradicting H_2(S¹ × D²) = 0.

**E″ is a knot exterior with meridian μ.** ∂(E″ ∪_μ h_j) is the torus surgered along an
essential curve, i.e. S². By Perelman and Alexander, E″ ∪_μ h_j ≅ B³. Put
S³ = B³ ∪ B³_out and V = B³_out ∪ h_j.
- h_j = D² × I meets ∂B³ in D² × ∂I, so V is a ball with an orientable 1-handle attached,
  i.e. a solid torus.
- D² × {½} is a meridian disc of V, with boundary μ.
- So E″ = S³ − int V is the exterior of the core K of V, and μ is a meridian of K.

Hence G_j = π_1(E) ≅ π_1(S³ − K) ∗ Z, and μ, which represents r_j^{±1} up to conjugacy,
is a meridian in the first factor.

## Step 3: case (b), D′ separates E

**The pieces.** ∂D′ is essential and separating in ∂E, so it cuts ∂E into two
once-punctured tori. So E = E_a ♮ E_b is a boundary connected sum along D′, where ∂E_a and
∂E_b are tori. We may assume μ ⊂ ∂E_a.

**μ is essential on ∂E_a.** Otherwise μ bounds a disc in ∂E_a. If that disc misses the
scar, μ is inessential in ∂E. If it contains the scar, μ is parallel to ∂D′ and separates
∂E. Both contradict (E3).

**The fundamental group.** ∂(E_a ∪_μ h_j) ≅ S². Then N = (E_a ∪_μ h_j) ♮ E_b, and
Z ≅ π_1(N) = π_1(E_a ∪ h_j) ∗ π_1(E_b). Since Z is freely indecomposable, one factor is
trivial.
- It is not π_1(E_b): a compact orientable 3-manifold with torus boundary has
  H_1(·; Q) ≠ 0 (half lives, half dies).
- So π_1(E_a ∪_μ h_j) = 1, and π_1(E_b) ≅ Z.

**Conclusion.** As in Step 2, E_a ∪_μ h_j ≅ B³, E_a is the exterior of a knot K with
meridian μ, and G_j ≅ π_1(E_a) ∗ π_1(E_b) ≅ π_1(S³ − K) ∗ Z. This proves (1) ⇒ (2).

**(2) ⇒ (1).** π_1(S³ − K) ≠ 1, since H_1 = Z. So π_1(S³ − K) ∗ Z is a nontrivial free
product.

**Separable relators.** If β(r_i) ∈ ⟨x, y⟩ for some β ∈ Aut(F), then
G_j ≅ ⟨x, y | β(r_i)⟩ ∗ ⟨z⟩. The first factor has abelianization Z²/⟨one vector⟩, which is
infinite, so it is nontrivial and (1) holds. This proves Theorem A′. ∎

## Step 3½: the hypothesis is needed

Take (r_1, r_2) = (x^{−1}y^{−1}, x^{−4}y^{−3}z^{−3}).
- **Z-pair.** Killing r_1 sets y = x^{−1}, and then r_2 = x^{−1}z^{−3}. So F/⟨⟨r_1, r_2⟩⟩ =
  ⟨x, z | x = z^{−3}⟩ ≅ Z.
- **Thickenable.** `thick2.c`, called through `thzsearch.c` in check mode, finds a
  rotation system with Σ_faces (len − 2) = 2V − 4c. `neuwirth_bruteforce.py` confirms
  this by trying every rotation system (`split-quotient-counterexamples.log`).
- **r_2 is not separable.** Its Whitehead graph, with vertices x^{±1}, y^{±1}, z^{±1} and
  one edge a — b^{−1} for each cyclic subword ab, is the 6-cycle
  X — x — Z — z — Y — y — X. It is connected without a cut vertex. By Stallings
  (*Whitehead graphs on handlebodies*, 1999), a separable word has a disconnected Whitehead
  graph or one with a cut vertex. `whitehead_minimal_set.py` independently finds that the
  Aut-minimal set (9 cyclic words of length 10) contains no word missing a generator.
- **Conclusion.** By Shenitzer (Proc. AMS 6 (1955) 273–279), G_1 = F/⟨⟨r_2⟩⟩ is freely
  indecomposable. So it is not π_1(S³ − K) ∗ Z, and conclusion (2) fails for i = 2.

In the thickening, E = H ∪ h_2 is irreducible by (E1). Steps 1–3 used only that ∂E is
compressible, and their conclusion fails, so ∂E is incompressible. Yet E[μ] = N is a solid
torus. So Jaco's lemma really needs ∂M to be compressible.

The pair (x^{−1}, x^{−4}y^{−1}x^{−1}z^{−1}x^{−1}zy^{−1}z^{−1}) is a second example. It is a
Z-pair, since x = 1 leaves y^{−2}z^{−1}. It is thickenable by both checkers. Its second
relator has Aut-minimal length 7 and a minimal set of 160 cyclic words, none missing a
generator. This relator also shows that a non-minimal word need not have a cut vertex: it
is shortened by y ↦ yx^{−1}, z ↦ zx^{−1}.

## Step 4: Corollary B′

Let G_j = F/⟨⟨r_i⟩⟩ ≅ T ∗ ⟨z⟩, with T ≅ T(p,q), p, q ≥ 2 coprime. This is freely
decomposable, so by Theorem A′
G_j = A ∗ C with A ≅ π_1(S³ − K), C ≅ Z, and r_j conjugate to a meridian of A.

**K is a nontrivial knot.** If K were trivial, G_j would be free of rank 2. But T ∗ Z
maps onto Z/p ∗ Z/q, and T(p,q) is not free because it has nontrivial centre.

**A is conjugate to T.**
- A is freely indecomposable: the exterior of a nontrivial knot is irreducible with
  incompressible boundary, and by the Kneser conjecture a free splitting would give an
  essential sphere or disc.
- A is not cyclic.
- By the Kurosh subgroup theorem, a freely indecomposable, non-cyclic subgroup of T ∗ ⟨z⟩
  is conjugate into T. So gAg^{−1} ⊂ T for some g.
- gAg^{−1} is a free factor of G_j contained in T, so it is a free factor of T. By
  Kurosh again, T ∩ (free factor) is a free factor of T.
- T is freely indecomposable (centre ≠ 1) and gAg^{−1} ≠ 1, so gAg^{−1} = T.

**The syllable length.** So r_j is conjugate in G_j to g·m·g^{−1} ∈ T, where m is a
meridian of K and T ≅ π_1(S³ − K).
- Burde–Zieschang: K is a torus knot, T(p,q) up to mirror image.
- Step 3 of `thickenable-meridional-relators-proof` applies to T with this isomorphism.
  The image of the meridian in T/Z(T) ≅ Z/p ∗ Z/q has cyclic syllable length 2.
- That length does not depend on the chosen isomorphism, by Fouxe-Rabinovitch and the
  conjugacy theorem for free products (p ≠ q).

Now pass to Q = G_j/⟨⟨Z(T)⟩⟩ = Z/p ∗ Z/q ∗ Z. The image of r_j is conjugate to an element of
Z/p ∗ Z/q of cyclic syllable length 2. It is still cyclically reduced of length 2 as an
element of the three-factor free product Q. ∎

## Step 5: Corollary C′

**Moving the automorphisms to the end.** Let α ∈ Aut(F) and let M be a (P1) move.
- M after α is α after a composite of (P1) moves.
- Products and inversions commute with α.
- Conjugating α(r_i) by a letter g equals α applied to the conjugation of r_i by the word
  α^{−1}(g), which is a composite of letter conjugations.

So every route equals a sequence of (P1)-composites followed by a single automorphism α.
The composites keep the fixed relator a conjugate of its start value, up to inversion.
Both s_1 and s_2 lie in ⟨x, y⟩, so α(fixed relator) is separable. Its one-relator quotient
is T(n, n+1) ∗ Z or B_3 ∗ Z, and Corollary B′ applies to it.

**The endpoint.** Suppose the fixed relator is s_1. By Step 4 of
`thickenable-meridional-relators-proof` (the rank does not matter there), the endpoint is
α(r_1*, r_2*), where:
- r_1* is a conjugate of s_1^{±1};
- r_2* represents in F/⟨⟨s_1⟩⟩ a conjugate of s_2^{±1}.

**Transport by α.** If α(r_1*, r_2*) is thickenable, apply Corollary B′ to it with
i = 1. Then α^{−1} induces an isomorphism F/⟨⟨α(r_1*)⟩⟩ → F/⟨⟨s_1⟩⟩ = T(n, n+1) ∗ ⟨z⟩.
- It sends the meridian free factor to a freely indecomposable, non-cyclic free factor,
  which by Step 4 is conjugate to T(n, n+1).
- It carries centre to centre.
- By Fouxe-Rabinovitch, the cyclic syllable length of the image of a meridian in
  Z/n ∗ Z/(n+1) is preserved.

So the image of s_2 in Q = Z/n ∗ Z/(n+1) ∗ Z must be conjugate to an element of syllable
length 2.

**Second-relator routes.** The image of xyxy^{−1}x^{−1}y^{−1} in Z/n ∗ Z/(n+1) ⊂ Q is
x·y·x·y^{−1}·x^{−1}·y^{−1}.
- x has order n ≥ 2 and y has order n + 1 ≥ 3, so every syllable is nontrivial.
- The syllables alternate between the factors, starting with x and ending with y.
- So it is cyclically reduced of length 6. By the conjugacy theorem it is not conjugate
  to a length-2 element.

**First-relator routes (fixed relator s_2).** Here F/⟨⟨s_2⟩⟩ = ⟨x, y | xyx = yxy⟩ ∗ ⟨z⟩.
Put u = xy and v = xyx. Then v² = xyx·yxy = xyxyxy = u³, and B_3 = ⟨u, v | u³ = v²⟩ =
T(2,3). Also:
- x = u^{−1}v, since y^{−1}x^{−1}·xyx = x;
- y = v^{−1}u², since x^{−1}y^{−1}x^{−1}·xyxy = y.

The centre is ⟨u³⟩. In Q = ⟨ū | ū³⟩ ∗ ⟨v̄ | v̄²⟩ ∗ Z:
- x̄ = ū²v̄;
- ȳ^{−1} = ū^{−2}v̄ = ūv̄.

So the image of s_1 = x^n y^{−(n+1)} is (ū²v̄)^n (ūv̄)^{n+1}.
- It alternates between the factors, starting with ū^{±1} and ending with v̄.
- Every syllable is nontrivial.
- So it is cyclically reduced of syllable length 2n + 2(n+1) = 4n + 2 ≥ 10.

It is not conjugate to a length-2 element. ∎

**Rank 2.** For a balanced presentation of the trivial group on x, y, apply Theorem A and
Corollary B of `thickenable-balanced-presentations-have-meridional-relators` with the
roles of r_1 and r_2 exchanged. The same syllable computation shows that no presentation
reached from AK(n) by moves on the first relator alone, up to Aut(F_2), is thickenable.

**Consistency check on a known thickenable pair.** From AK(2), `thzsearch.c` reaches the
thickenable Z-pair (xyx, x^{−2}y^{−1}x^{−1}y^{−1}) in F_3 (`calibration.log`).
- F/⟨⟨xyx⟩⟩ = F(x, z), with y = x^{−2}. The second relator becomes
  x^{−2}·x²·x^{−1}·x² = x, a meridian of the unknot.
- F/⟨⟨x^{−2}y^{−1}x^{−1}y^{−1}⟩⟩ is free on u = xy and z, with x = u^{−2}. The first
  relator is xyx = u·x = u^{−1}, again a meridian of the unknot.

Both agree with Theorem A′, whose hypothesis holds here because xyx and
x^{−2}y^{−1}x^{−1}y^{−1} both lie in ⟨x, y⟩.

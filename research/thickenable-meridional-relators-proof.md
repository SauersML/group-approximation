---
rg: 2
id: thickenable-meridional-relators-proof
kind: route
title: Proof that relators of thickenable balanced trivial presentations are meridians, with the AK(n) corollary
target: thickenable-balanced-presentations-have-meridional-relators
requires: []
artifacts:
  - experiments/ac-thickenable-orbit-2026-09-17/meridian.py
  - experiments/ac-thickenable-orbit-2026-09-17/meridian_lemma_test.py
---

All manifolds and complexes are PL. F = F(x_1, …, x_n). K is the presentation 2-complex
of P. "Thickenable" means that K embeds in some 3-manifold M (Lackenby,
arXiv:2606.06122, §1).

## Step 1: the Heegaard splitting (as in Lackenby, proof of Thm 7.3)

Let N be a regular neighbourhood of K in M. It has a handle decomposition with:
- one 0-handle, the neighbourhood of the vertex;
- n 1-handles, one per generator;
- n 2-handles, one per relator.

The j-th 2-handle is attached along a curve c_j ⊂ ∂H_1, where H_1 = 0-handle ∪ 1-handles.
Read in π_1(H_1) = F, the curve c_j is a conjugate of r_j^{±1}.

**N is a 3-ball.** N collapses onto K, so N is contractible, and in particular orientable.
- ∂N is connected. Lefschetz duality gives H_1(N, ∂N) ≅ H^2(N) = 0, and the exact
  sequence H_1(N, ∂N) → H̃_0(∂N) → H̃_0(N) = 0 then gives H̃_0(∂N) = 0.
- χ(∂N) = 2χ(N) = 2, so ∂N ≅ S^2.
- Σ = N ∪_{∂N} B^3 is a closed simply connected 3-manifold, hence S^3 (Perelman).

**H_1 and H_2.** H_1 is a genus-n handlebody. Put H_2 = cl(S^3 − H_1), the union of B^3
and the 2-handles. Seen from B^3, the 2-handles are 1-handles attached to a ball, so H_2 is
a genus-n handlebody. Let D_j be the core of the j-th 2-handle. Then:
- the D_j are disjoint properly embedded discs in H_2 with ∂D_j = c_j;
- cutting H_2 along D_1, …, D_n leaves a ball.

## Step 2: Theorem A

Fix j. Put W_j = H_1 ∪ (2-handles i ≠ j) and V_j = cl(S^3 − W_j) = B^3 ∪ (2-handle j).

**π_1(W_j) = G_j.** By van Kampen, attaching the i-th 2-handle kills the normal closure of
c_i, so π_1(W_j) = F/⟨⟨r_i : i ≠ j⟩⟩ = G_j. The inclusion H_1 ⊂ W_j induces the quotient
map F → G_j.

**V_j is a solid torus.** V_j is a ball with one 1-handle attached, so it is a solid torus.
D_j ⊂ V_j is a properly embedded disc that cuts V_j into a ball, so it is a meridian disc
of V_j.

**Conclusion.** Let K_j be the core of V_j. Then V_j is a tubular neighbourhood of K_j, and
W_j = S^3 − int V_j is the exterior E(K_j). So π_1(S^3 − K_j) ≅ π_1(W_j) = G_j.

The meridian of K_j is by definition the boundary of a meridian disc of V_j, namely
c_j = ∂D_j ⊂ ∂V_j = ∂W_j. As an element of π_1(W_j) = G_j, the curve c_j is the image of a
conjugate of r_j^{±1} (Step 1). This proves Theorem A. ∎

## Step 3: Corollary B

Let n = 2, and let G_1 = F/⟨⟨r_1⟩⟩ ≅ T(p,q) with p, q ≥ 2 coprime.

**K_1 is the (p,q) torus knot.** By Theorem A, G_1 ≅ π_1 E(K_1). The centre of T(p,q) is
nontrivial (it contains x^p). A knot whose group has nontrivial centre is a torus knot
T(p', q') (Burde–Zieschang, Math. Ann. 167 (1966) 169–176).

The quotient by the centre is Z/p' ∗ Z/q' ≅ Z/p ∗ Z/q. By Kurosh, every finite subgroup of
a free product is conjugate into a factor, so the maximal finite subgroups have orders
{p', q'} = {p, q}.

**The Seifert fibration.** E = E(K_1) is Seifert fibred, with base orbifold O a disc with
two cone points of orders p and q. The fibre class f generates the centre of π_1 E, and
π_1 E/⟨f⟩ = π_1^orb(O) = ⟨a, b | a^p, b^q⟩. The boundary loop of O is ab, with suitable
basing and orientations.

**The image of c_2.** On ∂E, a regular fibre is a parallel copy of K_1, so it meets the
meridian c_2 exactly once. So c_2 projects homeomorphically onto ∂O. Its class in
π_1^orb(O) is therefore conjugate to (ab)^{±1}. That element is cyclically reduced of
syllable length 2, since a ≠ 1 and b ≠ 1 lie in different factors.

**Independence of the isomorphism.** Any isomorphism T(p,q) → π_1 E maps centre to centre,
so it induces an isomorphism of the quotients. Hence the image of r_2 under any fixed
isomorphism T(p,q)/Z ≅ Z/p ∗ Z/q differs from the class of c_2^{±1} by an automorphism θ
of Z/p ∗ Z/q.

Since p ≠ q and both factors are finite cyclic, θ is an inner automorphism composed with
a factor automorphism x ↦ x^s, y ↦ y^t (Fouxe-Rabinovitch). With two factors, every
partial conjugation is inner. Both kinds of automorphism preserve the cyclic syllable
length of a conjugacy class: by the conjugacy theorem for free products (Lyndon–Schupp
IV.1.4), conjugate cyclically reduced elements are cyclic permutations of each other. ∎

**Exact form.** Let r_1 = x^p y^{−q}. The exponent map of T(p,q) is x ↦ q, y ↦ p. The group
⟨x, y | r_1, r_2⟩ has H_1 = Z/(e), where e = q·e_x(r_2) + p·e_y(r_2). The group is trivial,
so e = ±1.

**Conjugacy in T(p,q) is decided by the exponent and the image.** The centre Z = ⟨x^p⟩ maps
injectively under the exponent map (x^p ↦ pq). So g, g' ∈ T(p,q) are conjugate iff they
have the same exponent and conjugate images in Z/p ∗ Z/q.

**The length-2 classes with exponent ±1.** A length-2 class with exponent e = ±1 has a
representative x^a y^b with qa + pb ≡ e (mod pq). This forces a ≡ e·n (mod p) and
b ≡ e·m (mod q), where qn + pm = 1. So the class is that of (x^n y^m)^e, because
x^{−n} y^{−m} is conjugate to (x^n y^m)^{−1} in the free product.

This is the test `torus_meridian_ok` in `meridian.py`. It compares exponent sums and
cyclic syllable tuples in Z/p ∗ Z/q.

## Step 4: second-relator moves reach exactly a congruence class

For u ∈ F and ε = ±1, the move r_2 ↦ r_2 · u r_1^ε u^{−1} is a composite of AC moves:
conjugate r_1 letter by letter to u r_1 u^{−1}, invert if ε = −1, apply (AC1), then undo
the changes to r_1. Every m ∈ ⟨⟨r_1⟩⟩ is a product of such conjugates, and (AC2) and (AC3)
act on r_2 directly.

So the moves on r_2 alone reach exactly the words representing, in F/⟨⟨r_1⟩⟩, a conjugate
of r_2^{±1}. This is the same argument as Step 1 of `z-presentations-trivializing-relator-ac-equivalence-proof`.

## Step 5: Euclid (meridional ⇒ AC-trivial)

Let r_i = x^{a_i} y^{b_i} for i = 1, 2, with det [[a_1, b_1], [a_2, b_2]] = ±1.

**One row operation.** For i ≠ j:

x^{a_i} y^{b_i} = (x^{a_i − a_j} r_j x^{−(a_i − a_j)}) · x^{a_i − a_j} y^{b_i − b_j}.

By Step 4 (with the roles of the relators swapped), r_i can be replaced by
x^{a_i − a_j} y^{b_i − b_j}. The same identity with r_j^{−1} gives the sum x^{a_i + a_j} y^{b_i + b_j}.

**Reduction.** These are the elementary row operations on the 2×2 integer matrix. Euclid
reduces a matrix of determinant ±1 to a signed permutation matrix, i.e. relators
(x^{±1}, y^{±1}) or (y^{±1}, x^{±1}). (AC2) finishes.

**Application.** For r_1 = x^p y^{−q} and r_2 = x^n y^m, the determinant is pm + qn = 1. So
(x^p y^{−q}, r_2) is AC-trivial whenever r_2 passes the exact test of Step 3. First replace
r_2 by (x^n y^m)^{±1} using Step 4, then run Euclid.

## Step 6: Corollary C

**The image of the second relator.** The presentation AK(n) has r_1 = x^n y^{−(n+1)} and
r_2 = xyxy^{−1}x^{−1}y^{−1}, with T(n, n+1) = F/⟨⟨r_1⟩⟩. In Z/n ∗ Z/(n+1) the image of
r_2 is x^1 y^1 x^1 y^{−1} x^{−1} y^{−1}:
- the exponents are nonzero, since n ≥ 2 and n + 1 ≥ 3;
- the syllables alternate between the factors;
- the first letter is x and the last is y^{−1}.

So the image is cyclically reduced of syllable length 6. Inverting keeps the length at 6.

**Presentations in Ω_n.** Let (r_1', r_2') ∈ Ω_n with automorphism φ. Then φ^{−1} induces
an isomorphism F/⟨⟨r_1'⟩⟩ → T(n, n+1), and it sends r_2' to a conjugate of r_2^{±1}. By
Step 3 the syllable length does not depend on the isomorphism. Length 6 ≠ 2, so
Corollary B says (r_1', r_2') is not thickenable.

**Ω_n is the second-relator family.** By Step 4, Ω_n with φ = id is exactly the set of
presentations reached from AK(n) by moves on r_2 alone, and applying automorphisms gives
the rest. ∎

## Checks

`meridian_lemma_test.py 8 5` (output in the claim's artifacts) runs the torus relators
x^2y^{−3}, x^3y^{−2}, x^3y^{−4}, x^2y^{−5} and x^3y^{−5} against every r_2 of length ≤ 8
with exponent sum ±1:
- the prediction "thickenable and trivial ⇒ meridional" is never contradicted;
- the 36 thickenable non-meridional pairs all have a nontrivial representation to S_5;
- for three of them, GAP returns order 120.

The Neuwirth checker `thick2.c` was cross-checked against the brute-force
`verify_thick.py` on 2629 random two-relator presentations of total length ≤ 11, with no
mismatch. The 1-handle convention is calibrated on ⟨x | x^3⟩, whose complex lies in
L(3,1): it comes out thickenable with the reversed rotation, and not with the same one.

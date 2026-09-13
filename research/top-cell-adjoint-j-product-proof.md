---
rg: 2
id: top-cell-adjoint-j-product-proof
kind: route
title: The collapse at the identity is Ad-equivariant, and pointwise products of maps from a suspension are sums, so each bracket multiplies the top-cell class by J(Ad g) − 1
target: top-cell-commutator-class-is-product-of-adjoint-j-invariants
requires: []
---

**1. The collapse.** Fix a bi-invariant metric on H. Its restriction to G is
Ad(H)-invariant, and exp maps a small ball B_0 ⊂ g onto an Ad(H)-invariant
ball B ⊂ G, equivariantly. Let q: G -> G/(G − B) ≅ B_0^+ = S^n. Then
q(a x a^{-1}) = Ad_a q(x) for all a in H. The map q is the Pontryagin–Thom
collapse at the framed point 1, of degree one on H_n, so Sigma^∞ q is a
stable retraction onto the top-cell summand of the closed parallelizable
manifold G. The top cell splits off because the bottom cell of the Atiyah
dual Sigma^{-n} Sigma^∞ G_+ splits off through G_+ -> S^0.

**2. Sums.** Let Z = Sigma Z' and let a, b: X_+ ∧ Z -> G be based. The domain
is a suspension, so the pointwise product a·b is homotopic to the co-H sum
a + b, and b^{-1} = inv o b is homotopic to −b (Eckmann–Hilton). Any map,
in particular q, induces a homomorphism for co-H sums. Hence

    q o (a·b^{-1}) ≃ (q o a) − (q o b)   in [X_+ ∧ Z, S^n].

**3. One bracket.** Let k: X'_+ ∧ Z -> G be based with k = 1 on the
basepoint, and g: X -> H based. The bracket [g, k](x, z) =
g(x) k(z) g(x)^{-1} k(z)^{-1} is defined on X_+ ∧ X'_+ ∧ Z, a suspension,
and equals 1 when x or z is the base point. By Steps 1 and 2,

    q o [g, k] ≃ (Ad_{g(x)} o (q o k)) − (q o k).

The map (x, v) -> Ad_{g(x)} v on X_+ ∧ S^n stabilizes to u_g, and
precomposing the pointwise action with q o k stabilizes to the product
u_g·Sigma^∞(q o k) in the pi^0_s(X_+)-module pi^*_s(X_+ ∧ X'_+ ∧ Z). So
Sigma^∞ q o [g, k] = (u_g − 1)·Sigma^∞(q o k) = J_g·Sigma^∞(q o k).
Restricted to X ∧ X' ∧ Z it is the exterior product J_g ∧ Sigma^∞(q o k),
since u_g restricts to 1 at the base point of X.

**4. Induction** over c gives (a): each stage lives on a smash product with
the suspension Z as a factor, so Step 3 applies again.

**5. Seeds.** Put Z = S^j ∧ Y = Sigma^j Y, a suspension since j >= 1, and
k = [g_1, h]. Since [g_1, h] = 1 on S^j ∨ Y, k factors through Z. The iterated commutator f is 1 on the
fat wedge of M, so f factors through X_{c−1} ∧ ... ∧ X_2 ∧ S^j ∧ Y, and the
reduced part of [M]_E maps to [X_{c−1}] ∧ ... ∧ [X_2] ∧ [S^j x Y]_red.
Apply (a) and evaluate. The Kronecker pairing of E-homology with stable
cohomotopy is multiplicative for exterior products, so the top-cell
component is ± prod_i (J_{g_i})_*[X_i]_E · beta, where beta is
(Sigma^∞ q o [g_1, h])_* of the reduced class of S^j x Y. This is (b).

**6. The ideal.** J_g = J_Ad o Sigma^∞ g by naturality of stable adjoints and
of the translation u -> u − 1 in Omega^∞ S^0. So x_i = (J_Ad)_*(g_{i*}[X_i]_E)
lies in the image of the E_*-module map (J_Ad)_*: E~_*(H) -> E_*, an ideal.
Rationally pi~^0_s(H) ⊗ Q = H~^0(H; Q) = 0, so J_Ad is torsion. The reduced
class of [g_1, h] vanishes rationally because H_*(G; Q) is graded
commutative, so beta is torsion. This is (c).

**7. The rank-two checks.** For H = U(2), G = SU(2), n = 3 and q = id.
Ad(diag(z, 1)) rotates the complex line spanned by the off-diagonal
matrices in su(2) with weight one, so J of the circle class is J on the
generator of pi_1 SO, which is eta. Ad: SU(2) -> SO(3) clutches a bundle over
S^4 with p_1 = ±4 c_2 of the Hopf bundle, so lambda = ±2 and J_Ad on the
3-cell is ±2 nu. With Y = S^3, h = id and j = 3, beta = J_{omega}·1 = 2 nu.
With j = 1 and three circle letters, beta = eta and the fourfold
commutator gives eta^3. Every x_i lies in (eta, 2 nu)·E_*. Products of four
generators vanish in pi_*^s: eta^4 = 0, eta·nu = 0 and 16 nu^4 = 0. This is
(d). □

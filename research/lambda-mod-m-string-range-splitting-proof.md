---
rg: 2
id: lambda-mod-m-string-range-splitting-proof
kind: route
title: BSpin_m is the pullback of BSpin along multiplication by m on K(Z,4), the MString-line bundle is pulled back, and multiplication by m kills its classifying map on a skeleton
target: lambda-mod-m-bordism-splits-as-string-bordism-in-a-range
requires: []
---

**1. A pullback.** The class lambda: BSpin -> K is an infinite loop map with
fibre BString. The lift lambda/m: BSpin_m -> K exists because lambda
restricted to BSpin_m is null mod m. The square

    BSpin_m --> BSpin
      |           | lambda
      v           v
      K  --(x m)-->  K

commutes, and both vertical maps have fibre BString, so it is a homotopy
pullback. The maps to BO factor through BSpin.

**2. MString-line bundles.** Let E -> K be an infinite loop map with fibre
BString = E_0, over BO. Each fibre E_b is a torsor for E_0 under the
infinite loop sum, and the map to BO is additive. So the fibrewise Thom
spectra Th(E_b) are free MString-modules of rank one, and together they form
an MString-line bundle over K. It is classified by a map
xi_E: K -> BGL_1 MString, natural under pullback, and its global sections
pushed to a point give Th(E). If xi_E restricted to a subcomplex Y is null,
then Th(E|_Y) ≃ MString ∧ Sigma^∞_+ Y. Under this equivalence the fibre
inclusion Th(E_0) -> Th(E|_Y) is MString ∧ S^0 -> MString ∧ Sigma^∞_+ Y,
which the collapse Y_+ -> S^0 splits. By Step 1,
xi_m := xi_{BSpin_m} = xi_1 o (x m).

**3. The skeleton.** Th(E|_{K^(k)}) -> Th(E) has a cofibre built from
MString-cells indexed by the cells of K of dimension > k. Since MString is
connective, the cofibre is k-connected. So for connective X the map is an
isomorphism on pi_n(− ∧ X) for n < k.

**4. The obstruction group is finite.** BGL_1 MString is an infinite loop
space, so G_Y = [Y, BGL_1 MString] is an abelian group, and precomposition
with any map is a homomorphism. For Y = K^(k+1), the Atiyah–Hirzebruch
filtration F^j of G_Y has subquotients that are subquotients of
H^j(Y; pi_{j−1} MString) for 4 <= j <= k + 1, since K is 3-connected and
pi_j BGL_1 R = pi_{j−1} R for j >= 2. For j <= k these groups equal
H^j(K; A_j) with A_j = pi_{j−1} MString, and they are finite:
- if j ≡ 0 mod 4, then A_j is finite, because MString is rationally
  concentrated in degrees ≡ 0 mod 4;
- if j is not ≡ 0 mod 4, then H_j(K; Z) is finite, because
  H^*(K; Q) = Q[iota], and the universal coefficient theorem makes
  H^j(K; A_j) finite.

**5. Multiplication by a prime is nilpotent on each layer.** Fix a prime q.
H^*(K; F_q) is generated as an algebra by Steenrod operations on iota, and
(x q)^* iota = q·iota = 0 mod q. So (x q)^* = 0 on H^{>0}(K; F_q). A short
induction over a composition series of a finite q-group A, using the long
exact sequences in cohomology, shows that (x q)^* is nilpotent on H^j(K; A).
The q-primary part of H^j(K; Z) for j not ≡ 0 mod 4 is the image of a
Bockstein from H^{j−1}(K; Z/q^b), so (x q)^* is nilpotent there too.
Precomposition with a cellular approximation c: Y -> Y of x q preserves the
filtration F^j and acts on the subquotients for j <= k through these maps.
So for large a, (c^a)^* carries the q-primary part of G_Y into F^{k+1}G_Y.
The self-maps x q' with q' prime to q and x u with u a unit preserve
q-primary parts.

**6. Choice of m_k.** Let P be the finite set of primes dividing
|G_Y / F^{k+1} G_Y|. Choose a_q for q in P as in Step 5 and put
m_k = prod_{q in P} q^{a_q}. For m a multiple of m_k, Step 5 gives
xi_m restricted to Y = xi_1 o (x m) restricted to Y in F^{k+1} G_Y. Classes
in F^{k+1} vanish on K^(k). So xi_m is null on K^(k), and Steps 2–3 give (a).

*Check at k = 4.* K^(4) = S^4, G = pi_3 MString = Z/24, and xi_1 is a
generator, since pi_3 MSpin = 0. Then xi_m = m·xi_1 is null iff 24 | m.

**(b)** is (a) with Step 3, for n < k.

**(c)** A string structure on M induces a Spin_m structure for every m, and
Omega^String_* -> Omega^{Spin_m}_* is induced by the ring map. Put
k = dim M + 1. The splitting of (b) is natural in X, so it respects the
decomposition MString_n(U(N)) = MString_n(pt) (+) MString~_n(U(N)) given by
the base point. Hence the image of the nonzero reduced class in
MSpin_m~_{dim M}(U(N)) is nonzero, and it is [M, f]_red for the induced
Spin_m structure.
Theorem 7.3 of
`research/artifacts/class-four-lambda-mod-eight-trapping-part3-2026-09-13.md`
then applies with this m.

**(d)** The first half is spin-m-trapping-factors-through-string-bordism (d).
The second half is (c). □

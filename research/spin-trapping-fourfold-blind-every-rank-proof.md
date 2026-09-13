---
rg: 2
id: spin-trapping-fourfold-blind-every-rank-proof
kind: route
title: Commutators vanish on free ku-modules, Wood's cofibre sequence adds one eta per bracket, and MSpin splits 2-locally into ko-modules
target: spin-trapping-blind-to-fourfold-commutators-in-every-rank
requires: []
---

Write G = U(N), X^{∧j} = G^{∧j}, and cbar_j for the j-fold nested commutator,
with cbar_{j+1} = cbar_2 o (1 ∧ cbar_j). All spectra are suspension spectra
or module spectra, and smash products are over S unless marked.

**Step 1: ku kills the commutator.** H_*(G^{∧j}; Z) is torsion free. The
Atiyah–Hirzebruch spectral sequence for ku_* has torsion-free E^2 page, and
every differential vanishes rationally, so it collapses. So ku_*(G^{∧j}) is
a free ku_*-module, and ku ∧ G^{∧j} is a wedge of suspensions of ku. The
Pontryagin ring ku_*(G) embeds in H_*(G; Q)[v], so it is graded
commutative. By Künneth, the commutator map
c(x, y) = x y x^{-1} y^{-1} acts on ku_*(G) (x) ku_*(G) by
x (x) y -> sum ± x' y' chi(x'') chi(y''), with the diagonal
Delta x = sum x' (x) x''. Graded commutativity and
sum x' chi(x'') = epsilon(x) give epsilon(x)·epsilon(y). This vanishes on
reduced classes. So ku ∧ cbar_2: ku ∧ G^{∧2} -> ku ∧ G is a map of free
ku-modules that is zero on homotopy, and hence null as a ku-module map. The
same argument with ku replaced by BP, MU or HQ, and with HZ/2 (mod-2
homology of U(N) is also graded commutative), shows that these kill cbar_2.

**Step 2: one eta per bracket.** Let E be a ko-module spectrum, for instance
a connective cover of Sigma^{8k} ko, or HZ/2 through the ring map ko -> HZ/2.
Wood's equivalence ko ∧ C(eta) ≃ ku gives E ∧ C(eta) ≃ E ∧_ko ku, a ku-module.
So

    E ∧ C(eta) ∧ cbar_2 ≃ E ∧_ko (ku ∧ cbar_2) ≃ 0.

The cofibre sequence Sigma E ∧ G -eta-> E ∧ G -> E ∧ C(eta) ∧ G is exact for
maps out of E ∧ G^{∧2}. So E ∧ cbar_2 = eta·L_2 for some map
L_2: E ∧ G^{∧2} -> Sigma E ∧ G. Here eta· denotes multiplication by
eta in pi_1 S. This operation is natural for all maps of spectra.

**Step 3: induction.** Suppose E ∧ cbar_j = eta^{j-1}·L_j. Then

    E ∧ cbar_{j+1} = (E ∧ cbar_2) o (1_G ∧ (E ∧ cbar_j))
                   = (eta·L_2) o (eta^{j-1}·(1_G ∧ L_j)) = eta^j·(L_2 o (1_G ∧ L_j)),

up to the permutation of smash factors, using naturality of multiplication
by elements of pi_* S. This proves the formula of (a).

**Step 4: eta^3 = 0.** Multiplication by eta^3 on a ko-module E factors
through the image of eta^3 under the unit S -> ko. That image lies in
pi_3 ko = 0. So E ∧ cbar_4 = eta^3·L_4 is null. This is (a).

**Step 5: MSpin.** At p = 2, Anderson–Brown–Peterson split MSpin_(2) as a
wedge of connective covers ko<n_J> of suspensions of ko and suspensions of
HZ/2. Each summand is a ko-module. Smashing with cbar_4 distributes over the
wedge, so MSpin_(2) ∧ cbar_4 is a wedge of null maps, hence null. At an odd
prime p, MSpin_(p) ≃ MSO_(p) is a wedge of suspensions of BP, and Step 1
gives BP ∧ cbar_2 ≃ 0. Rationally MSpin ∧ HQ is an HQ-module, and Step 1
applies again. So the homomorphism MSpin~_*(G^{∧4}) -> MSpin~_*(G) induced by
cbar_4 vanishes after localization at every prime, and so it vanishes. This
is (b)'s first sentence.

**Step 6: the seed.** Let g' = (g_3, g_2, g_1, h): M -> G^4, and let
q: G^4 -> G^{∧4} be the quotient. Then f = cbar_4 o q o g'. The reduced part
of f_*[M] in MSpin_*(G) is (cbar_4)_* of the reduced part of
(q o g')_*[M], hence 0. That is [M, f]_red = 0. The transfer theorem's
detector evaluates nu((f o pr_M) (+) 1_Q) = ±<c_r(Q)^N, [X]>·[M, f]_red,
so it vanishes. This is (c). □

*Consistency.* For j = 3, Step 3 leaves eta^2·L_3. That is not zero, and the
class-three tower sees eta^2 as the Arf-invariant-one torus. For N = 2 this
recovers rank-two-spin-trapping-blind-to-depth-three-brackets without
Künneth for KO^*(G ∧ G) and without detection by characteristic numbers.

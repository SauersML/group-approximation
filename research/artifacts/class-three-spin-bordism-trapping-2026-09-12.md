# A simple AH algebra whose unitary component group has class at least three

Date: 12 September 2026, lane `ex-unitary-class-three` (EX swarm). This is a
complete argument. It has not been independently reviewed. Part 1 (this file)
sets up the detector. Part 2
(`class-three-spin-bordism-trapping-part2-2026-09-12.md`) builds the tower and
proves the theorem.

**Credit.** The detector and the tower are A. S. Toms's, from "A simple
C*-algebra which is not K1-injective", arXiv:2609.09535v1 (8 Sep 2026,
unrefereed). The lane read pages 1--24 of the PDF on 2026-09-12. What is new here: the seed
factor S^4 is replaced by T^2 x S^3. The suspended Hopf map is replaced by the
eta-squared triple Samelson product from `u2-triple-samelson-class-three-stage`
(lix-sweep lane, 11 Sep 2026). We check that spin bordism still detects the
seed after these changes.

## 0. Statement

**Theorem.** There are a simple, separable, unital, nuclear, stably finite,
infinite-dimensional AH algebra A and unitaries u_1, u_2, v in A such that the
triple commutator

    w = [u_2, [u_1, v]],   [x, y] = x y x* y*,

is not in U_0(A). So the lower central series of U(A)/U_0(A) has
gamma_3 != 1, and U(A)/U_0(A) is not nilpotent of class at most two.
Moreover w has order exactly two in U(A)/U_0(A), its K_1 class is zero, and
diag(w, 1) lies in U_0(M_2(A)).

We do not claim that U(A)/U_0(A) is nilpotent.

## 1. Toms's statements used verbatim

All numbering below is from arXiv:2609.09535v1.

- Section 3 setting (p. 9): "Fix r >= 1. Let X be a closed, connected,
  simply connected smooth spin manifold of real dimension 4r, and let Q -> X
  be a Hermitian complex vector bundle of rank r. Put B = S^4 x X ... Let
  E = C^2 (+) Q." Also W = Hom(Q, C^2) ≅ Q* (+) Q* (12), and W_R is spin by
  (13).
- Definition 3.2 (p. 11): for a smooth unitary section v transverse to the
  block-diagonal subbundle D(E), the locus is Z(v) = v^{-1}(D(E)). The map is
  f_v = rho o a_v, where a_v is the upper-left block and
  rho(A) = diag(det(A)^{-1}, 1) A. The invariant is
  nu_{X,Q}(v) := [Z(v), sigma_v, f_v] - [Z(v), sigma_v, c_v], an element of
  the reduced group Omega-tilde^Spin_4(SU(2)).
- Theorem 3.3 (p. 11): "The class nu_{X,Q}(v) is independent of the chosen
  transverse representative and depends only on the path component of v in
  U(Gamma(End E))."
- Lemma 4.1 (p. 13): the rotation R_z of a bundle map z: Q -> C^2 with
  ||z|| < 1 is homotopic to the identity. It is block diagonal exactly on
  Z(z), and it is transverse to D(E) when z is transverse to the zero
  section. For block-diagonal g, the upper-right block of g R_z is g_0 z.
- Proposition 4.2 (p. 14): "Let X, Q, B, E be as in section 3, let
  u: S^4 -> SU(2) represent the nonzero element of pi_4(SU(2)), and put
  w = (u o pr_{S^4}) (+) 1_Q. Then nu_{X,Q}(1_E) = 0,
  nu_{X,Q}(w) = <e(W_R), [X]> eta_Spin = <c_r(Q)^2, [X]> eta_Spin."
- Lemma 5.1 (p. 16): G(d) = Gr_2(C^{2d+2}) is closed, simply connected,
  spin, of complex dimension 4d, and "<c_2(zeta_d)^{2d}, [G(d)]> = 1."
- Proposition 5.2 (p. 17): with X_{i+1} = X_i x G(d_i) and
  Q_{i+1} = pr* Q_i (+) (+)_l (V_{i,l} (x) pr* zeta_{d_i}), where d_i = m_i N_i
  and N_i = r_i + 2, one has dim_R X_{i+1} = 4 r_{i+1} and
  <c_{r_{i+1}}(Q_{i+1})^2, [X_{i+1}]> = 1, the stated properties persist.
- Lemma 6.3 (p. 20): "Let (B_i, psi_i) be an inductive system of unital
  C*-algebras with injective connecting maps. Suppose that for every i and
  every nonzero positive a in B_i, there is j > i such that psi_{i,j}(a) is
  full in B_j. Then lim (B_i, psi_i) is simple."
- Lemma 7.1 (p. 21): "Let B = lim (B_i, psi_i) be an inductive limit of unital
  C*-algebras with injective connecting maps. Let v in U(B_i). If the image
  of v in B belongs to U_0(B), then there is j >= i such that
  psi_{i,j}(v) in U_0(B_j)."

## 2. The detector over an arbitrary closed spin seed factor

Fix a closed smooth manifold M of dimension m. Fix one spin structure
sigma_M on M. Keep X, Q, W as in Section 3 of Toms. Put B = M x X and
E = C^2 (+) Q, and give B the product spin structure. Give W_R its unique spin
structure pulled back from X.

**Proposition 2.1.** Definition 3.2 with S^4 replaced by M gives a function

    nu^M_{X,Q}: U(Gamma(End E))/U_0(Gamma(End E)) -> Omega-tilde^Spin_m(SU(2)).

It satisfies nu^M(1_E) = 0. For every smooth f: M -> SU(2),

    nu^M((f o pr_M) (+) 1_Q) = <c_r(Q)^2, [X]> · [M, f]_red.

*Proof.* We go through Toms's arguments and list every use of S^4 or of
dimension four.

(a) *Spin structures.* Toms uses simple connectivity of B at two points
(p. 9, and after (13), p. 10). There it gives uniqueness of the spin
structures on TB and W_R. We fix these structures instead: sigma_M x (the
unique one on X) on TB, and the pullback from X on W_R. Lemma 2.3 (two out
of three) and everything after (13) use only that the ambient and normal
structures are fixed. Uniqueness is never used. Toms himself remarks that
Z(v) need not be simply connected and carries the particular induced
structure sigma_v (p. 10).

(b) *Dimension.* Z(v) has codimension rank_R W = 4r = dim X, so
dim Z(v) = m. The bordism Z in the proof of Theorem 3.3 has dimension m + 1.
Proposition 2.8 (relative transversality), Lemma 3.1 (normal bundle of
D(E)), Lemma 2.3 and Definition 2.4 hold in every dimension. So the proof of
Theorem 3.3 goes through verbatim and gives well-definedness on components.

(c) *The values.* Toms's proof of Proposition 4.2 perturbs 1_E and w by
R = R_{eps s}, where s in Gamma(X, W) is transverse. The loci of R and of
(f o pr_M)R are both M x Z(s). On each copy the protected block is 1_2 or f.
The normal identifications agree, because left translation removes the
factor f(y) (p. 14). So both loci carry the same spin structure, and it is
sigma_M on each copy M x {xi}, up to orientation. The derivative
eps D_xi s is constant along M x {xi}, so no twist enters. Each zero xi
contributes sign_xi(s)·[M, f]_red. The signed count is <c_r(Q)^2, [X]>, by
(10) and (19). Nothing used that M = S^4, nor that f represents the Hopf
class. □

**Remark 2.2.** When m = 5 we have Omega^Spin_5(pt) = 0, so the constant-map
subtraction contributes nothing. By the suspension isomorphism (Toms (6)),
Omega-tilde^Spin_5(S^3) ≅ Omega^Spin_2(pt) ≅ Z/2. As in Toms (8), the
isomorphism takes a regular inverse image with its induced spin structure.

## 3. The seed: eta squared in spin bordism

Let alpha: S^1 -> U(2) be z -> diag(z, 1) and omega: S^3 = SU(2) -> U(2) the
inclusion. On M = T^2 x S^3 = S^1 x S^1 x S^3 with coordinates (s_1, s_2, z),
the pointwise triple commutator is

    c(s_1, s_2, z) = [alpha(s_2), [alpha(s_1), omega(z)]]  in SU(2).

**Proposition 3.1.** For any spin structure on T^2 x S^3, the class
[T^2 x S^3, c]_red in Omega-tilde^Spin_5(SU(2)) ≅ Z/2 is nonzero.

*Proof.* Commutators with 1 vanish. So c ≡ 1 on the fat wedge
F = {s_1 = 1} ∪ {s_2 = 1} ∪ {z = 1}, and c descends to
cbar: S^5 = (T^2 x S^3)/F -> SU(2). By `u2-triple-samelson-class-three-stage`,
[cbar] = <alpha, <alpha, omega>> = omega o eta_3 o eta_4, which generates
pi_5(S^3) ≅ Z/2.

Choose a regular value y != 1 of c. Then L = c^{-1}(y) is a closed surface
inside U = (T^2 x S^3) \ F ≅ R^1 x R^1 x R^3. It carries the normal framing
c^*(basis of T_y S^3). The spin structure of T^2 x S^3 restricted to the
contractible open set U is the unique one. So the induced spin structure on L
is the structure induced by the framing alone. It does not depend on the
spin structure chosen on T^2 x S^3.

By Pontryagin--Thom, (L, framing) represents the stabilization of [cbar] in
pi_2^s. That is eta^2, the nonzero element (Freudenthal: pi_5(S^3) ->
pi_2^s is onto, and both groups are Z/2). Under the Pontryagin--Thom ring
isomorphism, eta^2 is the product of two Lie-framed circles. The spin
structure induced by a framed product is the product structure. Each
Lie-framed circle carries the nonbounding structure (Toms, Lemma 2.6 and its
proof). The product of two nonbounding circles is the spin torus whose
quadratic form is 1 on all three nonzero classes. Its Arf invariant is 1, so
it is nonzero in Omega^Spin_2 ≅ Z/2. By Remark 2.2 the class of c is
nonzero. □

Standard facts used above without a re-verified theorem number:
Omega^Spin_2 ≅ Z/2 detected by the Arf invariant (Milnor 1963; Kirby--Taylor
1990, both cited by Toms); pi_2^s ≅ Z/2 generated by eta^2, and the
Pontryagin--Thom ring isomorphism (Stong, Notes on cobordism theory). An
independent check is that the unit S -> KO is an isomorphism on pi_2, and it
factors through the Atiyah--Bott--Shapiro orientation MSpin -> KO (Toms
Section 8.3 records the degree-one analogue).

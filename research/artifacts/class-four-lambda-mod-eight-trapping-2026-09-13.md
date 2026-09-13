# Class four in a simple AH algebra, part 1: the lambda-mod-8 trapped class

Date: 13 September 2026, lane `ex-unitary-string-trapping` (EX swarm). This is
a complete argument. It has not been independently reviewed. Part 2
(`class-four-lambda-mod-eight-trapping-part2-2026-09-13.md`) computes the
quaternionic Grassmannians, builds the tower and proves the theorem. It
continues `class-three-spin-bordism-trapping-2026-09-12.md` (cited as CT3)
and `class-four-stage-and-blind-spin-trapping-2026-09-12.md` (cited as CF4).
Toms numbering refers to arXiv:2609.09535v1.

**Credit.** The detector, the recursion and the limit lemmas are Toms's. The
class-four stage, with its eta-cubed Samelson product, is from lane
`ex-unitary-class-three`. Three steps are new here.

1. The tangential structure is put on the virtual bundle TX − W_R. It is not
   put on X and on W separately.
2. The structure is spin together with a trivialization of lambda mod 8. This
   is weaker than a string structure, and its bordism still sees eta cubed.
3. The quaternionic Grassmannians Gr_8(H^{8+2d}) replace Toms's
   Gr_2(C^{2d+2}). Their defect lambda(TG) − lambda(W) is 8·q_1, which
   vanishes mod 8. The complex Grassmannians have defect 2·c_2.

## 0. Statement

**Theorem.** There are a simple, separable, unital, nuclear, stably finite,
infinite-dimensional AH algebra A and unitaries u_1, u_2, u_3, v in A such
that

    c = [u_3, [u_2, [u_1, v]]]   is not in U_0(A),   [x, y] = x y x* y*.

So gamma_4(U(A)/U_0(A)) != 1, and U(A)/U_0(A) is not nilpotent of class at
most three. The class of c has order exactly two. Its K_1 class is zero, and
diag(c, 1) lies in U_0(M_2(A)).

We do not claim that U(A)/U_0(A) is nilpotent.

## 1. The structure Spin_8, and why its bordism sees eta cubed

Let lambda in H^4(BSpin; Z) be the spin characteristic class, with
2·lambda = p_1. It is primitive: lambda(V (+) V') = lambda(V) + lambda(V')
for spin bundles. Let BSpin_8 -> BSpin be the homotopy fibre of the map
BSpin -> K(Z/8, 4) that represents lambda mod 8.

A *Spin_8-structure* on a stable, possibly virtual, vector bundle V over a
space Y is a spin structure on V together with a nullhomotopy of
lambda(V) mod 8. One exists if and only if w_1(V) = 0, w_2(V) = 0 and
lambda(V) = 0 in H^4(Y; Z/8). The class lambda mod 8 is primitive, so
BSpin_8 is an H-space over BO. Structures on V and V' therefore give one on
V (+) V', and a structure on V gives one on −V. Write Omega^8_* for the
bordism of closed manifolds with a Spin_8-structure on the stable tangent
bundle.

The fibre F of BSpin_8 -> BO is built from Z/2 (orientations), K(Z/2, 1)
(spin structures) and K(Z/8, 3) (nullhomotopies of lambda mod 8), so
pi_0(F) = Z/2. On a trivial bundle over a contractible space, structures up
to homotopy are pi_0(F), that is, orientations. A framing therefore induces
a Spin_8-structure, and there is a homomorphism pi_n^s = Omega^fr_n ->
Omega^8_n.

**Proposition 1.1.** The image of eta^3 = 12 nu in Omega^8_3 is nonzero.

*Proof.* Let L be a closed framed 3-manifold. Choose a compact spin
4-manifold W with ∂W = L, inducing on L the spin structure of the framing.
The framing trivializes lambda(TW) on ∂W. So it defines a relative class
lambda(W, ∂W) in H^4(W, ∂W; Z) ≅ Z. Put

    e(L) = <lambda(W, ∂W), [W, ∂W]>  mod 24.

Two choices W, W' glue along L to a closed spin 4-manifold V. The two
relative numbers differ by <lambda(V), [V]> = p_1[V]/2 = 3·sigma(V)/2. By
Rokhlin's theorem 16 divides sigma(V), so 24 divides this number. So e(L) is
well defined. It is a framed bordism invariant, since a framed bordism glued
to W is another choice. It is additive.

The Lie-framed S^3 = SU(2) represents nu. It bounds D^4. Its framing differs
from the bounding framing by the unit-quaternion map S^3 -> SO(4). So
lambda(D^4, ∂D^4) is lambda of the quaternionic line bundle over S^4, which
is ±1. Thus e(nu) = ±1, e is an isomorphism pi_3^s ≅ Z/24 -> Z/24, and
e(eta^3) = e(12 nu) = 12.

Now suppose a framed L with e(L) = 12 bounds a Spin_8-manifold W, with the
structure on ∂W induced by the framing. Then W is spin with the correct
boundary spin structure, so W computes e(L). On ∂W the Spin_8-structure is
the mod-8 reduction of the integral trivialization given by the framing. It
extends over W. The obstruction to extending a nullhomotopy of lambda mod 8
rel ∂W is the reduction of lambda(W, ∂W) in H^4(W, ∂W; Z/8). So
lambda(W, ∂W) is divisible by 8, and e(L) ≡ 0 mod 8. But 12 is not
divisible by 8. □

The same argument shows that the kernel of pi_3^s -> Omega^8_3 lies in
{0, 8 nu, 16 nu}. Reducing lambda only mod 2 or mod 4 loses eta cubed in
this argument, and Omega^Spin_3 = 0 loses it altogether (CF4, Section 2).

## 2. The trapped Spin_8 class over M x X

Fix a closed smooth m-manifold M with a Spin_8-structure sigma_M on TM. Let
X be a closed connected smooth manifold of dimension 4r, Q -> X a Hermitian
bundle of rank r, and W = Hom(Q, C^2) ≅ Q* (+) Q*. Suppose tau is a
Spin_8-structure on the virtual bundle TX − W_R. Put B = M x X and
E = C^2 (+) Q. Then TB − W_R = pr_M^* TM (+) pr_X^*(TX − W_R) carries
sigma_M (+) tau.

**Proposition 2.1.** Toms's Definition 3.2, with S^4 replaced by M and the
spin structure sigma_v replaced by the Spin_8-structure described below,
gives a function

    nu^{M,8}_{X,Q}: U(Gamma(End E))/U_0(Gamma(End E)) -> Omega-tilde^8_m(SU(2)).

It satisfies nu^{M,8}(1_E) = 0. For every smooth f: M -> SU(2),

    nu^{M,8}((f o pr_M) (+) 1_Q) = <c_r(Q)^2, [X]> · [M, f]_red.

*Proof.* (a) *Normal identification.* Let U(E) -> B be the bundle of unitary
groups and D(E) ⊂ U(E) the block-diagonal subbundle. At g in D(E)_b we have
T_g U(E)_b = g·u(E_b) and T_g D(E)_b = g·(u(2) (+) u(Q_b)). The off-diagonal
skew-Hermitian matrices [[0, z], [−z*, 0]], with z in Hom(Q_b, C^2), form a
complement O_b ≅ W_{R,b}. Left translation by g^{-1} identifies the normal
space of D(E) at g with O_b, continuously in g. So the normal bundle of D(E)
in U(E) is canonically pi^* W_R (Toms Lemma 3.1). No twist enters.

If a section v is transverse to D(E), then Z(v) = v^{-1}(D(E)) has normal
bundle W_R|_{Z(v)}, and T Z(v) (+) W_R|_{Z(v)} ≅ TB|_{Z(v)}. Hence
T Z(v) ≅_s (TB − W_R)|_{Z(v)}. Restricting sigma_M (+) tau gives a
Spin_8-structure sigma_v on Z(v). A transverse homotopy has locus
Z ⊂ B x I with T Z ≅_s (TB (+) R − W_R)|_Z, and it gets its structure the
same way.

(b) *Invariance.* Toms's proof of Theorem 3.3 uses relative transversality
(Proposition 2.8), the normal bundle (Lemma 3.1) and two-out-of-three for
structures (Lemma 2.3). For Spin_8, two-out-of-three is the restriction in
(a). It applies to any submanifold whose normal bundle is identified with
W_R. Dimensions are as in CT3 Proposition 2.1(b). So

    nu^{M,8}(v) = [Z(v), sigma_v, f_v] − [Z(v), sigma_v, const]

depends only on the path component of v.

(c) *Values.* Follow Toms's proof of Proposition 4.2 and CT3 2.1(c). Perturb
by R = R_{eps s}, where s in Gamma(X, W) is transverse to zero. The loci of R
and of (f o pr_M) R are both M x Z(s). Along M x {xi}, the normal
identification is the constant derivative eps·D_xi s. There TB − W_R
restricts to TM (+) (TX − W_R)|_xi. The second summand is a virtual trivial
bundle over a point, and its Spin_8-structures are orientations. So
M x {xi} carries sigma_M up to orientation, and it contributes
sign_xi(s)·[M, f]_red. The signed count of zeros is
<e(W_R), [X]> = <c_{2r}(Q* (+) Q*), [X]> = <c_r(Q)^2, [X]>. The orientation
of X comes from tau, since W_R is complex. □

**Remark 2.2.** Omega-tilde^8_m(SU(2)) ≅ Omega^8_{m−3}. The isomorphism takes
a regular preimage of a point y != 1, with the structure induced by the
normal framing.

## 3. The seed on T^3 x S^3

Give M = T^3 x S^3 the Spin_8-structure of its Lie-group framing. Let c_4 be
the pointwise commutator of CF4 Section 1:

    c_4(s_1, s_2, s_3, z) = [alpha(s_3), [alpha(s_2), [alpha(s_1), omega(z)]]],

with alpha(s) = diag(s, 1) and omega the inclusion SU(2) ⊂ U(2).

**Proposition 3.1.** [T^3 x S^3, c_4]_red is nonzero in
Omega-tilde^8_6(SU(2)) ≅ Omega^8_3.

*Proof.* The map c_4 is 1 on the fat wedge F, so it descends to
cbar_4: S^6 -> SU(2). By `u2-quadruple-samelson-class-four-stage`,
[cbar_4] = omega o eta_3 o eta_4 o eta_5 = 6 nu'. Choose a regular value
y != 1. Its preimage L lies in U = (T^3 x S^3) \ F ≅ R^6 and carries the
normal framing c_4^*(basis of T_y S^3). On the contractible set U, a
Spin_8-structure on TU is an orientation. So the structure that L inherits
from M is the one induced by its framing, up to orientation. By
Pontryagin–Thom, (L, framing) represents the stabilization of [cbar_4]. That
is eta^3 = 12 nu, which is nonzero in pi_3^s. Proposition 1.1 makes its
image nonzero. Reversing orientation negates the class, and 12 nu has order
two. □

Standard facts used without a re-verified theorem number: eta^3 = 12 nu in
pi_3^s ≅ Z/24 (Toda, Composition Methods); Rokhlin's theorem; the
Lie-framed S^3 represents nu, and the e-invariant of Adams, J(X) IV, is an
isomorphism on pi_3^s.

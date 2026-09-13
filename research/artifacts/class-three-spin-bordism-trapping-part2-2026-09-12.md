# Class-three component groups, part 2: the tower and the theorem

Date: 12 September 2026, lane `ex-unitary-class-three`. This continues
`class-three-spin-bordism-trapping-2026-09-12.md` (cited as Part 1). The
argument is complete and has not been independently reviewed. Toms numbering
refers to arXiv:2609.09535v1.

## 4. The tower

Start as in Toms Construction 5.3: X_1 = Gr_2(C^4), Q_1 = zeta_1, r_1 = 2.
Put

    Y_i = T^2 x S^3 x X_i,   E_i = C^2 (+) Q_i,   A_i = Gamma(End E_i),
    N_i = r_i + 2.

Fix a spin structure on T^2 (any one). Give Y_i the product spin structure.

Choose the evaluation sets exactly as in Toms Section 6.1, with S^4 replaced
by T^2 x S^3. Take a finite set F_i = {z_{i,1}, ..., z_{i,m_i}} in Y_i such that
alpha_{j,i}(F_i) is 1/i-dense in Y_j for all j <= i. Here alpha_{j,i} is the
coordinate projection that keeps T^2 x S^3 and discards the later Grassmannian
factors. Put V_{i,l} = E_i|_{z_{i,l}}, d_i = m_i N_i, G_i = Gr_2(C^{2d_i+2})
and zeta_i its tautological bundle. Then

    X_{i+1} = X_i x G_i,
    Q_{i+1} = pr* Q_i (+) (+)_l (V_{i,l} (x) pr* zeta_i),
    phi_i(a) = alpha_i^* a (+) (+)_l ( a(z_{i,l}) (x) 1_{zeta_i} ).

By Toms Proposition 5.2, which concerns X_i and Q_i only,

    dim_R X_i = 4 r_i,   X_i simply connected and spin,
    <c_{r_i}(Q_i)^2, [X_i]> = 1   for every i.       (32')

Each phi_i is a unital injective *-homomorphism. The coordinate summand makes
it injective.

## 5. The unitaries

In A_1, with coordinates (s_1, s_2, z) on T^2 x S^3, put

    u_1 = (alpha o s_1) (+) 1_{Q_1},  u_2 = (alpha o s_2) (+) 1_{Q_1},
    v = (omega o z) (+) 1_{Q_1}.

The operations are pointwise and block diagonal. So their triple commutator is

    w_1 = [u_2, [u_1, v]] = (c o pr_{T^2 x S^3}) (+) 1_{Q_1},

where c is the map of Part 1, Section 3. More generally, put
w_i = (c o pr_{T^2 x S^3}) (+) 1_{Q_i} in U(A_i).

**Lemma 5.1** (Toms Lemma 6.2, same proof). phi_i(w_i) is homotopic to
w_{i+1} in U(A_i+1). Hence phi_{1,j}(w_1) is homotopic to w_j.

*Proof.* On the coordinate summand, phi_i(w_i) is (c o pr) (+) 1_{alpha* Q_i}.
On the l-th evaluation summand it is w_i(z_{i,l}) (x) 1_{zeta_i}. The group
U(V_{i,l}) is connected, so a path from w_i(z_{i,l}) to 1, tensored with 1,
joins that summand to the identity. □

**Lemma 5.2.** w_i is not in U_0(A_i), for every i.

*Proof.* Part 1, Proposition 2.1 with M = T^2 x S^3, X = X_i, Q = Q_i gives
nu^M(w_i) = <c_{r_i}(Q_i)^2, [X_i]>·[T^2 x S^3, c]_red and nu^M(1) = 0. The
first factor is 1 by (32'). The second is nonzero by Part 1,
Proposition 3.1. Since nu^M is constant on path components, w_i and 1 lie in
different components. □

## 6. Simplicity

**Proposition 6.1** (Toms Proposition 6.4, same proof). A = lim (A_i, phi_i)
is simple.

*Proof.* Let 0 != a in (A_i)_+. Then U = {y : a(y) != 0} is a nonempty open
subset of Y_i. By density, some j >= i and z in F_j satisfy alpha_{i,j}(z) in
U. The coordinate block of phi_{i,j}(a) at z is a(alpha_{i,j}(z)), which is
nonzero. So the evaluation block phi_{i,j}(a)(z) (x) 1 of phi_{i,j+1}(a) is
nonzero in every fibre, and phi_{i,j+1}(a) is full. Toms Lemma 6.3 applies.
Only density of the evaluation sets was used, never the factor S^4. □

## 7. Proof of the Theorem (Part 1, Section 0)

Each A_i is a unital homogeneous algebra over a compact finite CW complex.
The connecting maps are unital and injective. So A is separable, unital,
nuclear, AH and infinite-dimensional. It is simple by Proposition 6.1.

*Stably finite.* Each M_n(A_i) has a tracial state. Tracial states of M_n(A)
form the inverse limit of the nonempty compact sets T(M_n(A_i)), so the set
is nonempty. A simple algebra's tracial state is faithful, and a faithful
tracial state forces finiteness. So every M_n(A) is finite.

*The triple commutator.* The images of u_1, u_2, v in A have triple commutator
w = phi_{1,infinity}(w_1). Suppose w were in U_0(A). By Toms Lemma 7.1, some
j >= 1 would give phi_{1,j}(w_1) in U_0(A_j). By Lemma 5.1 this means w_j is
in U_0(A_j), which contradicts Lemma 5.2. So w is not in U_0(A), and
gamma_3(U(A)/U_0(A)) != 1.

*Order two.* The class [cbar] has order two in pi_5(S^3), so cbar^2 is
null-homotopic through based maps. Precomposing with the collapse, c^2 is
homotopic to 1, hence w_1^2 is too. So w^2 is in U_0(A), and w has order
exactly two.

*K_1 and M_2.* K_1(A) is abelian and w is a commutator, so [w]_1 = 0. In
U(M_2(A)), diag(x, x*) is in U_0 by rotation. So diag(x, 1) and diag(1, x)
agree modulo U_0, and diag(x, 1) commutes with diag(y, 1) modulo U_0. All
commutators of elements diag(x, 1) are therefore trivial there. In particular
diag(w, 1) is in U_0(M_2(A)). □

## 8. Remarks and open directions

- *Why the excess-one CP tower is different.* Trapping needs
  dim X_i = 4 rank Q_i, so the base dimension is about four times the rank,
  well above the excess-one regime dim = 2·rank + 1 of
  `eta-squared-survives-twisted-excess-tower`. That claim is still open. The
  existence problem no longer depends on it.
- *Class-two bound.* This is consistent with
  `equal-dimension-ah-component-groups-class-two`. The blocks here have
  dim Y_i = 5 + 4 r_i > 2 rank E_i = 2 r_i + 4.
- *Class four and beyond.* Nesting more alpha's gives
  <alpha,<alpha,<alpha,omega>>> = omega o eta^3. Stably eta^3 = 12 nu is
  nonzero in pi_3^s = Z/24, but Omega^Spin_3 = 0, so spin trapping cannot see
  it. Stably eta^4 = 0. With a rank-two protected block, spin trapping sees
  only KO-visible stems (eta, eta^2, and the mu_{8k+1} family). Two routes are
  open. One is a trapping theory that detects nu, such as string bordism;
  that needs string structures on Y_i and W_R. The other is seeds in
  larger protected blocks.
- *Matrix amplification.* The witness dies in M_2(A). Whether some simple A
  has gamma_3 != 1 in U(M_n(A))/U_0 for every n is open. That would need a
  triple Samelson product in U(k) for k >= 3 that survives into rank k + 1
  after trapping.
- *Nilpotency.* Whether U(A)/U_0(A) is nilpotent at all is open. The
  finite-stage groups are nilpotent, but their dimensions are unbounded.

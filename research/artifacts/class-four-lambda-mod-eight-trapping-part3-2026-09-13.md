# Unitary component groups, part 3: a transfer principle for any protected rank, and where rank two stops

Date: 13 September 2026, lane `ex-unitary-string-trapping`. This continues
Part 1 (`class-four-lambda-mod-eight-trapping-2026-09-13.md`) and Part 2
(`class-four-lambda-mod-eight-trapping-part2-2026-09-13.md`). The arguments
are complete and have not been independently reviewed. Toms numbering refers
to arXiv:2609.09535v1.

For m >= 1, BSpin_m -> BSpin is the homotopy fibre of lambda mod m. So
Spin_1 is spin, and Spin_8 is the structure of Part 1. Omega^m_* is the
corresponding bordism. On a trivial bundle over a contractible space, a
Spin_m-structure is an orientation (Part 1, Section 1, with 8 replaced by m).

## 7. Rank-p trapping and the transfer principle

**Proposition 7.1.** Fix p, m >= 1 and a closed manifold M with a
Spin_m-structure. Let X be a closed connected 2pr-manifold, Q -> X Hermitian
of rank r, and W = Hom(Q, C^p) ≅ p·Q*. Suppose TX − W_R carries a
Spin_m-structure. Put E = C^p (+) Q over B = M x X. Then the trapped class
(Toms Definition 3.2), with f_v the upper-left p x p block, gives

    nu: U(Gamma(End E))/U_0 -> Omega-tilde^m_{dim M}(U(p)),

with nu(1_E) = 0 and, for smooth f: M -> U(p),

    nu((f o pr_M) (+) 1_Q) = ±<c_r(Q)^p, [X]>·[M, f]_red.

*Proof.* Part 1, Proposition 2.1, with C^2 replaced by C^p. The normal
identification uses the off-diagonal block Hom(Q, C^p), of real rank
2pr = dim X. The structure argument uses only that lambda mod m is
primitive. The count is <e(W_R), [X]> = <c_{pr}(p·Q*), [X]> =
±<c_r(Q)^p, [X]>. No normalization rho is needed: f_v lands in U(p), and
reduced bordism subtracts the constant map. □

**Lemma 7.2 (steps).** Let k, d >= 1, G = Gr_k(H^{k+pd}), zeta the
tautological bundle (complex rank 2k), q_1 = c_2(zeta), Q_G = d·zeta and
W_G = Hom(Q_G, C^p) ≅ pd·zeta*. Then dim_R G = 4kpd = rank_R W_G,
<c_{2k}(zeta)^{pd}, [G]> = ±1, TG − W_{G,R} is spin, and
lambda(TG) − lambda(W_{G,R}) = k·q_1. So for m | k, TG − W_{G,R} carries a
Spin_m-structure.

*Proof.* Part 2, Lemmas 4.1 and 4.2, with 2d replaced by pd. Here n = k + pd.
Pieri gives sigma_{1^k}^{pd} = [pt] on Gr_k(C^{k+pd}). We have
lambda(TG) = −(n − 2k)·q_1 = −(pd − k)·q_1. Since W_{G,R} (x) C ≅
pd·zeta* (+) pd·zeta, p_1(W_{G,R}) = −2pd·q_1 and lambda(W_{G,R}) = −pd·q_1.
The difference is k·q_1. □

**Theorem 7.3 (transfer).** Let M be a closed manifold with a
Spin_m-structure, and u_1, ..., u_s smooth unitaries in C(M, M_p). Let w be a
group word, and put f = w(u_1, ..., u_s): M -> U(p). Suppose
[M, f]_red != 0 in Omega-tilde^m_{dim M}(U(p)). Then there are a simple,
separable, unital, nuclear, stably finite AH algebra A and a unital injective
*-homomorphism iota: C(M, M_p) -> A such that w(iota(u_1), ..., iota(u_s)) is
not in U_0(A).

*Proof.* Run the tower of Part 2, Section 5, with seed factor M, protected
block C^p and X_1 = point. Then A_1 = C(M, M_p). The steps are
G_i = Gr_m(H^{m + p·d_i}) with Q_{i+1} = Q_i (+) d_i·zeta_i and
d_i = m_i·rank E_i. By Lemma 7.2 and induction as in Part 2, Lemma 5.1:
dim X_i = 2p·r_i, TX_i − W_{i,R} carries a Spin_m-structure, and
<c_{r_i}(Q_i)^p, [X_i]> = ±1. Words are computed pointwise and
block-diagonally, so w(phi_{1,i}(u)) is homotopic to
w_i = (f o pr_M) (+) 1_{Q_i}, as in Part 2, Lemma 5.2. Proposition 7.1 gives
nu(w_i) = ±[M, f]_red != 0 = nu(1). Simplicity, stable finiteness and the
passage to the limit (Toms Lemmas 6.3 and 7.1) are as in Part 2. Take
iota = phi_{1,infinity}. □

*Special cases.* With p = 2, m = 1 and w = [u_2, [u_1, v]] on T^2 x S^3, this
recovers the class-three algebra, using spin steps Gr_1(H^{1+2d}) = HP^{2d}
in place of Toms's complex Grassmannians. With m = 8 and the fourfold
commutator on T^3 x S^3, it recovers Part 2. The theorem turns "class at
least c in a simple algebra" into a finite-stage question: find a depth-c
word in unitaries over a closed Spin_m-manifold whose reduced Spin_m-bordism
class in U(p) is nonzero.

## 8. Rank two stops at fivefold commutators (depth four)

Depth counts brackets: [u_3, [u_2, [u_1, v]]] has depth three. Compare
`rank-two-spin-trapping-blind-to-depth-three-brackets` (peer landing
97882e595). There KO-theory shows that *spin* trapping is blind at depth
three on every seed manifold. Below, *every* bordism detector is shown to be
blind at depth four, for sphere-product seeds.

**Proposition 8.1.** Let M = S^{n_1} x ... x S^{n_5}, and let u_j be pulled
back from the j-th factor through maps S^{n_j} -> U(2). Let
f = [u_5, [u_4, [u_3, [u_2, u_1]]]]. Then for every tangential structure G
under which M is framed on its open top cell, [M, f]_red = 0 in
Omega-tilde^G_{dim M}(U(2)). So Theorem 7.3 and every trapping detector with
protected rank two are silent on such fivefold commutators.

*Proof.* The map f is 1 on the fat wedge. So f = fbar o q, with q: M -> S^N
the degree-one collapse, N = sum n_j, and fbar the iterated Samelson product
of the leaves. A regular preimage of y != 1 lies in the open top cell, so
[M, f]_red is the image of the stable class of fbar under the unit map. Every
element of pi_n U(2) with n >= 2 has the form omega o h. Samelson products are
natural for precomposition: <a o g, b o h> = <a, b> o (g ∧ h). Also
<alpha, alpha> = 0, <alpha, omega> = omega o eta_3, and <omega, omega> is the
generator of pi_6(S^3) ≅ Z/12. Its stable image y lies in pi_3^s. So each
bracket contributes one factor eta (when one entry is a multiple of alpha) or
one factor y (when both entries have the form omega o h). The stable image of
fbar is therefore

    eta^a · y^b · (stable images of the leaves),   a + b = 4.

Each such product vanishes. eta^4 = 0. eta^3·y = 12 nu·y is a multiple of
12 nu^2 = 0, since nu^2 has order two. eta^2·y^2 and eta·y^3 vanish because eta·nu = 0 and eta kills the
3-primary part of y. y^4 lies in pi_12^s = 0. □

For fourfold commutators (a + b = 3) the product eta^3 survives, and
Parts 1–2 detect it. So for sphere-product seeds, rank-two trapping is sharp
at class four. Class five needs protected rank p >= 3, non-spherical seeds,
or detection that is not a bordism class.

**First data at rank p >= 3.** Bott's brackets are
<a_i, a_j> = (i−1)!(j−1)!·g in pi_{2p} U(p) ≅ Z/p! for i + j = p + 1. The
coefficient is odd only when i, j <= 2, so only for p <= 3
(`samelson-odd-sphere-products-in-u-n-orders`). Take the evaluation map
q: U(p) -> S^{2p−1}. In the exact sequence
pi_{2p} U(p) -> pi_{2p} S^{2p−1} ≅ Z/2 -> pi_{2p−1} U(p−1) -> pi_{2p−1} U(p) ≅ Z,
the group pi_{2p−1} U(p−1) is Z/2 for odd p and 0 for even p (Kervaire). It
is torsion, so it maps to zero in Z. For odd p, Z/2 -> pi_{2p−1} U(p−1) is
therefore an isomorphism, and q_*: pi_{2p} U(p) -> Z/2 is zero. For even p,
q_* is onto. So stem-one detection through q dies at the first
bracket for p >= 3. Deeper stems (nu^2 in pi_6^s, eta·mu_9 in pi_10^s) are
the next candidates. They are not computed here.

## 9. Gluing towers: non-nilpotency reduces to seeds of every depth

**Proposition 9.1.** Suppose that for every c >= 2 there are m_c >= 1 and an
unbounded set S_c of integers such that, for each N in S_c, some closed
Spin_{m_c}-manifold M and some unitaries u_1, ..., u_{c−1}, v in C(M, M_N)
have c-fold nested commutator f = [u_{c−1}, [..., [u_1, v]...]] with [M, f]_red != 0 in Omega-tilde^{m_c}(U(N)). Then some simple
unital AH algebra has a non-nilpotent unitary component group.

*Proof.* Stage n is a finite direct sum. It has one summand T_c for each
2 <= c <= n, plus two auxiliary summands M_{a_n}(C) and M_{a_n+1}(C).
Stage 1 is C (+) M_2(C).

Suppose the stage-n ranks have gcd one. Then every large integer is a sum of
them with multiplicities, and each stage-(n+1) summand can take any large
rank. So the two auxiliary ranks a_{n+1} and a_{n+1} + 1 can be realized, and
they keep the gcd equal to one.

Tower T_c enters at stage c as C(M_c, M_{N_c}), with X = point and protected
block C^{N_c}. Its entry rank N_c is chosen in S_c, large enough to be such a
sum. The map into the new summand is a sum of evaluations at
points, over constant functions. At later stages T_c evolves by Theorem 7.3's
steps Gr_{m_c}(H^{m_c + N_c d}).

Every summand at stage n + 1 receives evaluation blocks a(z) (x) 1_{zeta} from
every stage-n summand, at dense point sets. Here zeta is that summand's own
step bundle, or trivial for the auxiliary summand. Each T_c also receives its
own coordinate pullback. So the connecting maps are unital and injective, and
the limit is simple (Toms Lemma 6.3, density as in Part 2). Evaluation blocks
add multiples of zeta to Q, and only change d in the step count. So the
Euler count ±1 and the structure on TX − W_R persist in each T_c.

The depth-c witness in T_c persists as (f o pr) (+) 1 in T_c. Its images in
the other summands are evaluation blocks, which contract. The trapped class
of T_c is nonzero at every stage, so Toms Lemma 7.1 keeps the witness out of
U_0 of the limit. Hence gamma_c != 1 for every c. □

Caution: the hypothesis needs seeds of every depth in growing ranks N. By
Proposition 8.1 rank two is blind beyond depth four. The heuristics in
`simple-cstar-unitary-component-group-not-nilpotent` suggest that
image-of-J products may cap metastable depth. The hypothesis is open, and it
may be false.

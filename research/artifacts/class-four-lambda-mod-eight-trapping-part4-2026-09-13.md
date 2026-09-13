# Unitary component groups, part 4: one eta per bracket in every U(N), and the class-five target

Date: 13 September 2026, lane `ex-unitary-string-trapping`. This continues
Parts 1–3 (`class-four-lambda-mod-eight-trapping{,-part2,-part3}-2026-09-13.md`).
The argument is complete and has not been independently reviewed. It extends
Steps 1–4 of `rank-two-spin-trapping-depth-three-blind-proof` (peer landing
97882e595) from U(2) to every U(N). The peer proof uses a Künneth
decomposition of KO^*(G ∧ G). That decomposition needs Sigma^∞ U(2) to be a
wedge of spheres, and it fails for N >= 3, where the 5-cell of SU(N) is
attached to the 3-cell by eta. Below, an induction over all smash factors X
replaces it.

## 10. The KO-pullback of a j-fold commutator is divisible by eta^{j−1}

Let G = U(N) with N >= 1, and let c: G ∧ G -> G be the commutator map
(g, h) -> g h g^{-1} h^{-1}. It is well defined on the smash product because
c(g, 1) = c(1, h) = 1. Put c_1 = id and c_j = c o (1 ∧ c_{j−1}): G^{∧j} -> G.
So the nested commutator [g_{j−1}, [..., [g_1, h]...]] of maps M -> G equals
c_j o (g_{j−1} ∧ ... ∧ g_1 ∧ h) o (diagonal).

**Lemma 10.1.** c^*: KU~^*(G) -> KU~^*(G ∧ G) is zero.

*Proof.* By Hodgkin, K^*(U(N)) is the exterior algebra on the classes
beta_i = beta(lambda^i), and each generator is primitive. Take a primitive
class p. Represent it in K^{−1}(Y) = [Y, U], where the group law is pointwise
multiplication, and let inv be the group inverse. Then mu^* p = p (x) 1 + 1 (x) p
and inv^* p = −p. So c^* p = p_1 + p_2 − p_1 − p_2 = 0 on G x G, and hence on
G ∧ G. The map c^* is multiplicative, so it kills the reduced ring those
primitives generate. □

**Proposition 10.2.** Let X be a finite based CW complex and
z in KO^*(X ∧ G). Then (1_X ∧ c_j)^* z lies in
eta^{j−1}·KO^*(X ∧ G^{∧j}).

*Proof.* Induction on j. The case j = 1 is trivial. For j >= 2, write
(1_X ∧ c_j)^* = (1_X ∧ 1_G ∧ c_{j−1})^* o (1_X ∧ c)^*.

*First factor.* K^*(G) is free, so Künneth gives
KU^*(X ∧ G ∧ G) ≅ KU^*(X) (x) KU~^*(G ∧ G) and
KU^*(X ∧ G) ≅ KU^*(X) (x) KU~^*(G). Under these, the complexification of
(1_X ∧ c)^* z is (1 (x) c^*)(z_C) = 0 by Lemma 10.1. Wood's cofibre sequence
Sigma KO -eta-> KO -> KU gives exactness of KO^{*+1} -eta-> KO^* -> KU^* on
every space. So (1_X ∧ c)^* z = eta·z' for some z' in
KO^{*+1}(X ∧ G ∧ G).

*Second factor.* Apply the induction hypothesis with X' = X ∧ G to z'. It
gives (1_{X'} ∧ c_{j−1})^* z' in eta^{j−2}·KO^*(X' ∧ G^{∧(j−1)}). Multiplying
by eta finishes the step. □

**Corollary 10.3.** Let M be a closed manifold, let g_1, ..., g_{j−1}, h: M -> U(N)
be maps, and put f = [g_{j−1}, [..., [g_1, h]...]]. Then
f^* z in eta^{j−1}·KO^*(M) for every z in KO~^*(U(N)). For j >= 4 this gives
f^* z = 0, since eta^3 = 0 in KO_*. The same Hodgkin-type argument applies to
H^*(U(N); Z/2), which is exterior on primitive classes. So f^* x = 0 for
every reduced mod-2 class x once j >= 2.

*Consequence for trapping.* Let m = 1, so the structure is spin. For every
rank N, every KO-characteristic number
<pi^J(M)·f^* z, [M]_KO> of (M, f) with reduced coefficients vanishes at depth
three (j = 4). So does every Stiefel–Whitney number with reduced coefficients,
from depth one (j = 2). For N = 2, the peer's Anderson–Brown–Peterson step
turns this into [M, f]_red = 0. For N >= 3, KO^*(U(N)) is not free over KO_*.
This lane has not verified that these numbers detect Omega-tilde^Spin_*(U(N)),
so for N >= 3 bordism blindness is *not* claimed.

## 11. The class-five target

By the transfer theorem (Part 3, Theorem 7.3), a simple unital C*-algebra
with a nonzero fivefold commutator follows from one finite-stage input. That
input is a closed Spin_m-manifold M and unitaries u_1, ..., u_4, v in C(M, M_p)
whose fivefold commutator has nonzero reduced Spin_m-bordism class in U(p).
The known constraints on such an input:

- p = 2 with sphere-product seeds is impossible for every structure
  (Part 3, Proposition 8.1).
- In every rank, m = 1 detection through KO- and Stiefel–Whitney numbers
  dies from depth three on (Corollary 10.3).
- So an input needs invariants beyond KO- and Stiefel–Whitney numbers. One
  source is relative lambda-type e-invariants of null-bordisms, as in Part 1,
  Proposition 1.1. That argument exhausts eta^3 at depth three. A depth-four
  input would need a length-four product of torsion classes visible in
  Omega^{Spin_m}_*, or information carried by higher cells of U(p).
- tmf-type detection (for example nu^2, or products involving kappa-bar)
  would need a string structure on TX − W_R. The quaternionic steps never
  give one, because their defect is k·q_1 with k >= 1. No step family with
  defect zero and odd count is known to this lane.

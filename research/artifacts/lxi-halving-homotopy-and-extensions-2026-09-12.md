# K1-injectivity over properly infinite quotients, and the halving homotopy

Lane `ex-k1-properly-infinite`, 2026-09-12. Both results are proved completely below. They have not
been externally reviewed and do not decide STW Problem LXI.

Notation: for a unital A with Cuntz isometries `s_1, s_2` (`s_1s_1^* + s_2s_2^* = 1`), put
`Theta([x_ij]) = sum s_i x_ij s_j^*`, a unital \*-isomorphism `M_2(A) -> A`. The halving of a unitary w is
`C(w) = s_1 w s_1^* + s_2 s_2^* = Theta(diag(w,1))`.

## 1. Extension lemma

**Lemma 1.** Let A be unital and `I` a closed ideal, with `I~ = I + C1 subset A`. If `A/I` is properly
infinite and K1-injective and `I~` is K1-injective, then A is K1-injective.

*Proof.* Let `u in U(A)` with `[u] = 0` in `K_1(A)`. Then `[pi(u)] = 0`, so `pi(u) in U_0(A/I)`, and it
lifts to some `w in U_0(A)` (products of exponentials lift). The unitary `y = u w^*` has `pi(y) = 1`, so
`y in U(I~)`, and `[y] = 0` in `K_1(A)`. By exactness of `K_0(A/I) -> K_1(I) -> K_1(A)`,
`[y]_{K_1(I)} = delta_0(g)` for some g in `K_0(A/I)`, where `delta_0` is the exponential map.

Every element of `K_0` of a unital properly infinite algebra is the class of a projection in the algebra
itself (Cuntz, Ann. of Math. 113 (1981)). So `g = [e]` with `e in A/I`. Lift e to a self-adjoint `h in A`.
Then `exp(2 pi i h)` lies in `U(I~)` and in `U_0(A)` (path `t -> exp(2 pi i t h)`), and its class in
`K_1(I)` is `delta_0([e])` (Rordam--Larsen--Laustsen, Proposition 12.2.2). Replace h by `-h` if the sign
convention requires it, and call the result `y'`. Now `y y'^*` lies in `U(I~)` with trivial class in
`K_1(I)`, so by hypothesis it is in `U_0(I~)`, which is contained in `U_0(A)`. Hence
`u = (y y'^*) y' w` is in `U_0(A)`. Square.

Special cases in which the unitization is K1-injective, so that Lemma 1 applies:
- I stable. A unitary of `I~` is homotopic to one in `M_n(J)~` for `I ~= J (x) K`, and a null-homotopy
  in a larger matrix algebra transports back through a corner embedding.
- `I~` of stable rank one (Rieffel, Proc. London Math. Soc. 46 (1983), Theorem 10.12).
- I of real rank zero, conditionally on Lin's theorem that unital real rank zero algebras are
  K1-injective. It is quoted as [Lin01, Corollary 4.2.10] in Blanchard arXiv:0804.4624v13, proof of
  Proposition 3.2, and the real rank of I is by definition that of `I~`. The citation was not checked
  against Lin's book.
- Z-stable ideals are not claimed. Jiang's theorem (arXiv:math/9707228) is for unital algebras, and
  the unitization of a non-unital Z-stable algebra is not Z-stable.
(Correction of 2026-09-13 after review `ex-review-analysis-2026-09-12-part3` section 1.6.)
The quotient can be any Kirchberg algebra. Consider a unital Toeplitz--Pimsner
algebra `T(E)` of a correspondence E over B, with Fock module isomorphic to `H_B` and properly infinite
Cuntz--Pimsner quotient. Its compact ideal `K(F(E)) ~= B (x) K` is stable, so `T(E)` is K1-injective as
soon as the quotient is.

## 2. The halving homotopy

**Theorem 2.** Let `U = O_2 *_C C(T)` be the full unital free product, with Cuntz generators `s_1, s_2`
and free unitary z. The following are equivalent.
(a) U is K1-injective.
(b) For every unital C\*-algebra A, every Cuntz pair `s_1, s_2` in A and every `w in U(A)`, one has
    `w ~_h C(w)` in `U(A)`.
(c) Every unital properly infinite C\*-algebra A with `[1_A] = 0` in `K_0(A)` is K1-injective.

*Proof.* (c) => (a): U contains O_2 unitally, so it is properly infinite and `[1_U] = 0`, because
`K_0(O_2) = 0`.

(a) => (b): `[C(z)] = [Theta(diag(z,1))] = [diag(z,1)] = [z]` in `K_1(U)`, since Theta is implemented
by the unitary row `(s_1, s_2)`. So `y = z^* C(z)` is K1-trivial, and by (a) it lies in `U_0(U)`. The
unital homomorphism `U -> A` with `s_i -> s_i` and `z -> w` maps y to `w^* C(w)`. So `w ~_h C(w)`.

(b) => (c): since `[1_A] = 0` and 1 is properly infinite, `1 (+) 1 ~ 1` (properly infinite full
projections with equal K_0 classes are equivalent, Cuntz 1981). This gives a Cuntz pair in A. Let
`[u] = 0`. BRR Lemma 2.4(ii), applied in `M_2(A)` to `diag(u,1)` and `p = diag(1,0)`, gives
`diag(u,1) in U_0(M_2(A))`. Applying Theta, `C(u) in U_0(A)`. By (b), `u ~_h C(u)`, so u is in `U_0(A)`.
Square.

**Remark 3.** Blanchard's argument for arXiv:0804.4624, Proposition 4.6(i), with O_2 in place of O_3,
gives `O_2 *_C O_2 ~= O_2 *_C C(T)`. Use `iota_1(s_k) -> s_k`, `iota_2(s_k) -> z s_k`, with inverse
`z -> sum_l iota_2(s_l) iota_1(s_l)^*` and `s_k -> iota_1(s_k)`. So (a) is K1-injectivity of `O_2 * O_2`.

**Remark 4 (relation to LXI).** LXI implies (c). The converse would need a witness u in an arbitrary
properly infinite A to survive in `A *_C O_2`, which has trivial unit class because both units
are identified. That is the same survival problem as the free envelope `A_LIX * T_2` recorded in
the LXI Attempts. BRR's universal algebra `O_infty * O_infty` has nonzero unit class, so (c) is possibly
weaker than LXI.

**Remark 5 (Eckmann--Hilton picture).** On `pi_0(U(A))`, Theta-sum `(w_1, w_2) -> Theta(diag(w_1,w_2))`
and multiplication satisfy the interchange law. Theta-sums over orthogonal supports commute, and
`C_{s_1}(w) ~ C_{s_2}(w)` by rotation inside `M_2(C)`. Condition (b) is exactly the statement that `[1]` is
a unit for the Theta-sum. Given that unit, Eckmann--Hilton would identify the two operations. The naive
path from the isometry 1 to `s_1` through isometries does not exist: `1 - tt^*` cannot move continuously
from 0 to a nonzero projection. So the unit axiom is where the problem lives.

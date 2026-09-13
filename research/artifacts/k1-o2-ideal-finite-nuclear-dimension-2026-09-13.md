# O_2-multiplier ideals of finite nuclear dimension

Lane `ex-k1-halving-homotopy`, 2026-09-13. Section 1 checks a literature pointer against its source.
Sections 2 and 3 are proved in full. Nothing here has been externally reviewed.

Setting (as in `o2-multiplier-extension-k1-injective-iff-unitization`): `I` is a non-unital C\*-algebra
with isometries `S_1, S_2 in M(I)`, `S_1S_1^* + S_2S_2^* = 1`. `A = C*(I, S_1, S_2)`, and `I~ = I + C1`.

## 1. The pointer, corrected

The predecessor lane recalled, without a source: "σ-unital algebras of finite nuclear dimension with no
bounded traces are stable". **As stated this is false.** `C_0([0,1)) ⊗ O_2` is σ-unital, has nuclear
dimension 1 and no bounded traces, and is not stable: it has the unital quotient `O_2`, evaluation at 0.
The correct statement needs one more hypothesis.

L. Robert, *Nuclear dimension and n-comparison*, arXiv:1002.2180v2 (Münster J. Math. 4 (2011)). Read
from the PDF, pages 5--6:
- Theorem 1: "If A has nuclear dimension n then Cu(A) has the n-comparison property."
- Corollary 1: "Let A be a C\*-algebra of nuclear dimension at most ω and let `B ⊆ A ⊗ K` be hereditary
  and σ-unital. Then B is stable if and only if it has no non-zero unital quotients and no non-zero
  bounded traces."

The proof combines Theorem 4 (ω-comparison) with Ortega--Perera--Rordam, Proposition 4.8. Taking
`B = A ⊗ e_11` gives the abstract's form: a σ-unital C\*-algebra of finite nuclear dimension is stable
iff it has no nonzero unital quotients and no nonzero bounded traces.

## 2. O_2-multiplier ideals carry no bounded traces

**Lemma 1.** I has no nonzero bounded trace.

*Proof.* Let τ be a bounded trace on I and `(e_λ)` an approximate unit. For `x in I_+`, put
`y = S_i x^{1/2}`, which lies in I. Then `τ(S_i x S_i^*) = τ(y y^*) = τ(y^* y) = τ(x)`. Hence
`2 τ(e_λ) = τ(S_1 e_λ S_1^* + S_2 e_λ S_2^*) <= ||τ||`, because `S_1 e_λ S_1^* + S_2 e_λ S_2^*` is a positive
contraction in I. Letting λ grow gives `2||τ|| <= ||τ||`. Square.

## 3. Consequences for counterexample ideals

**Lemma 2 (stable ideals are harmless).** If I is stable, then `I~` is K1-injective.

*Proof.* Write `I = J ⊗ K`, with `e_n = 1 ⊗ (e_11 + ... + e_nn)` in `M(I)`. Let `u in U(I~)` with `[u] = 0` in
`K_1(I)`. After a small homotopy, `u = λ(v + (1 - e_n))` with `λ in T` and v a unitary of the unital corner
`e_n I~ e_n`, that is of `M_n(J)~`. Here `[v] = 0` in `K_1(J)`, so `v ⊕ 1_m` is null in `M_{n+m}(J)~` for
some m. Inside `1 - e_n` the projection `1 ⊗ (e_{n+1,n+1} + ... + e_{n+m,n+m})` is available. So
`v + (1 - e_n)` is null in `I~`. Square.

**Proposition 3.** Let I be σ-unital with nuclear dimension at most ω, for instance finite. If `I~` is not
K1-injective, then I has a nonzero unital quotient `Q = I/K`. Every such Q contains `O_2` unitally, and
`A/K ≅ Q ⊕ A/I = Q ⊕ O_2`.

*Proof.* By Lemma 1, Robert's Corollary 1 and Lemma 2, an I with no nonzero unital quotient is stable,
and then `I~` is K1-injective. If `Q = I/K` is unital, K is an ideal of A. The unit of Q is a central
projection in `A/K`, whose complementary summand is `(A/K)/(I/K) = A/I ≅ O_2`. Compressing `S_1, S_2` by
the unit of Q gives a Cuntz pair in Q. Square.

**Proposition 4 (dividing out the stable part).** Let I be separable with nuclear dimension at most ω, and
let `J_0` be the sum of all ideals of I that have no nonzero unital quotient. Then `J_0` has no nonzero
unital quotient and is stable. If `A/J_0` is K1-injective, then so is `A`. So if `I~` is not K1-injective,
then `I' = I/J_0` is again a counterexample ideal for the extension `0 -> I' -> A/J_0 -> O_2 -> 0`. It is
separable, has nuclear dimension at most that of I, and **every nonzero ideal of `I'` has a nonzero unital
quotient**.

*Proof.* Let `F` be the ideals without nonzero unital quotients. F is closed under closed increasing
unions: if `J = closure(union J_n)` and `J/L` has unit e, some `J_n` maps onto an ideal of `J/L` that contains
an element near e. That ideal is then everything, so `J_n/(J_n ∩ L) = J/L`, and `J/L` must be 0.
F is also closed under finite sums: if `(J_1 + J_2)/L = Q` is unital, the images `Q_1, Q_2` satisfy
`Q_1 + Q_2 = Q`. So `Q/Q_2` is a unital quotient of `J_1`, which forces `Q_2 = Q`. Then Q is a unital quotient
of `J_2`, and `Q = 0`. Hence `J_0 in F`, and `J_0` is separable, so σ-unital. Its nuclear dimension is at most
that of I (Winter--Zacharias). So `J_0` is stable, by Lemma 1 (with `A -> M(J_0)`), Robert's Corollary 1
and Lemma 2, and `J_0~` is K1-injective. `A/J_0` is properly infinite. By the established
`k1-injectivity-extends-over-properly-infinite-quotients`, A is K1-injective if `A/J_0` is. The algebra
`A/J_0` is unital, contains `I/J_0` as an ideal with quotient `O_2`, and the proof of
`o2-multiplier-extension-k1-injective-iff-unitization` uses only this extension. So `A/J_0` is K1-injective
iff `(I/J_0)~` is. Nuclear dimension does not increase under quotients (Winter--Zacharias). Only this
direction is claimed: K1-injectivity of A need not pass to `A/J_0`.

Minimality: let `K/J_0` be a nonzero ideal of `I/J_0` with no unital quotient, and `K/L` a unital quotient
of K. The image of `J_0` in `K/L` is an ideal, and the quotient by it is a unital quotient of `K/J_0`. So the
image is all of `K/L`, and `K/L` is a unital quotient of `J_0`, which is 0. Hence `K in F` and `K ⊆ J_0`. Square.

**Remark.** The commutative model `I = C_0(Y) ⊗ O_2` with Y locally compact and non-compact already has
unital quotients on every nonzero ideal. So Proposition 4 removes only genuinely stable parts, and it does
not reduce the problem to unital algebras. The predecessor's constraints stand: no finite-dimensional
representations, non-stable. What is new is the exact form of the finite-nuclear-dimension constraint.

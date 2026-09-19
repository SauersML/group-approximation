---
rg: 2
id: thompson-gap-witnesses-need-nonamenable-image-proof
kind: route
title: Relator images in the Frobenius ball of a virtually solvable unitary group commute, so their normal closure is abelian; simplicity makes it everything, and the abelianization character pays at least 2 sin(pi/12)
target: thompson-gap-witnesses-need-nonamenable-image
requires:
  - thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3
  - thompson-v-finitely-presented-infinite-simple
  - thompson-t-lochak-schneps-presentation
artifacts:
  - experiments/amenable-image-gap-witnesses-2026-09-17/abelian_and_monomial_check.py
  - experiments/amenable-image-gap-witnesses-2026-09-17/out_abelian_and_monomial_check.json
---

All matrices are in `U(n)` and all norms are operator norms. We write `[g,h] = g h g^-1 h^-1`.
Nothing depends on `n`.

## Lemma 1 (commutator contraction)

For unitaries `g, h`, `||[g,h] - 1|| <= 2 ||g - 1|| ||h - 1||`.

*Proof.* `[g,h] - 1 = (gh - hg) g^-1 h^-1`, and `gh - hg = (g-1)(h-1) - (h-1)(g-1)`. Unitaries have norm 1.

## Lemma 2 (back-tracking)

Let `A, B` be unitaries with `||B - 1|| < sqrt 2`. If `A` commutes with `B A B^-1`, then `AB = BA`.

*Proof.*
1. Let `V_1, ..., V_m` be the eigenspaces of `A`, with distinct eigenvalues `a_1, ..., a_m`. Then `B V_i` is the
   `a_i`-eigenspace of `B A B^-1`.
2. The normal operators `A` and `B A B^-1` commute, so they are simultaneously diagonalizable. Hence
   `B V_i = ⊕_j (B V_i ∩ V_j)`.
3. Suppose `j != i` and `u` is a unit vector in `B V_i ∩ V_j`. Then `B^-1 u` lies in `V_i`, which is
   orthogonal to `V_j`, so `||B^-1 u - u||^2 = 2`. But `||B^-1 - 1|| = ||B^-1 (1 - B)|| = ||B - 1|| < sqrt 2`,
   a contradiction.
4. So `B V_i = V_i` for every `i`, and `B` commutes with `A`.

The hypothesis holds in either of two cases:
- `A` commutes with `[A,B] = A (B A^-1 B^-1)`. Commuting with `B A^-1 B^-1` is the same as commuting with its
  inverse `B A B^-1`.
- `A` and `B A B^-1` lie in a common abelian group.

## Lemma 3 (tori are centralized by near-identity normalizers)

Let `S <= U(n)` be an abelian subgroup and `g` a unitary with `g S g^-1 = S` and `||g - 1|| < sqrt 2`.
Then `g` centralizes `S`.

*Proof.* For `s` in `S`, both `s` and `g s g^-1` lie in the abelian group `S`. Apply Lemma 2 with `A = s` and
`B = g`.

## Lemma 4 (Frobenius ball in a virtually solvable unitary group)

Let `L <= U(n)` be virtually solvable, and let `g, h` in `L` satisfy `||g - 1|| < 1/2` and `||h - 1|| < sqrt 2`.
Then `gh = hg`.

*Proof.*
1. **Structure of the closure.** Let `K` be the closure of `L` in `U(n)`. It is a compact Lie group
   (Cartan's closed-subgroup theorem), so its identity component `K^0` is open in `K` and normal.
   - Let `L_1 <= L` be solvable of finite index, with `L = ⋃_(t=1..p) x_t L_1`. The closure `K_1` of `L_1` is
     solvable, since the closure of each derived subgroup contains the derived subgroup of the closure.
   - `K = ⋃ x_t K_1`, so `K_1` has finite index in `K` and `K^0 = K_1^0`.
   - `K^0` is a compact connected solvable Lie group. Its Lie algebra is compact, hence the sum of its centre
     and a semisimple ideal, and solvability kills the semisimple ideal. So `K^0` is abelian, a torus.
2. **Descent.** Put `h_0 = h` and `h_(k+1) = [g, h_k]`, all in `L`.
   - With `q = 2 ||g - 1|| < 1`, Lemma 1 gives `||h_k - 1|| <= q^k ||h - 1||`. So `h_k -> 1`, and
     `||h_k - 1|| < sqrt 2` for all `k`.
   - Since `K^0` is an open neighbourhood of `1` in `K`, some `h_N` lies in `K^0`.
3. **The bottom step.** `g` is in `K`, so it normalizes the abelian group `K^0`. Since `||g - 1|| < 1/2 < sqrt 2`,
   Lemma 3 shows that `g` centralizes `K^0`. In particular `g` commutes with `h_N`.
4. **Back-tracking.** Suppose `g` commutes with `h_(k+1) = [g, h_k]` for some `k < N`. Lemma 2, with `A = g` and
   `B = h_k` (`||h_k - 1|| < sqrt 2`), shows that `g` commutes with `h_k`. By downward induction `g` commutes
   with `h_0 = h`.

*Remark.* For finite `L`, `K^0 = 1` and Step 3 reads `h_N = 1`. This is the classical Frobenius lemma from the
proof of Jordan's theorem, as in `mod-s2-finite-image-near-scalar-torelli-abelian-proof`, Lemma 3.

## Lemma 5 (simple groups have no virtually solvable quotients)

An infinite simple group `Gamma` has no nontrivial virtually solvable quotient.

*Proof.*
1. A nontrivial quotient of `Gamma` is `Gamma` itself. Suppose `Gamma` has a solvable subgroup `E` of finite
   index.
2. The normal core of `E` is normal of finite index. It is not `1`, because `Gamma` is infinite, so it is
   `Gamma`. Hence `Gamma = E` is solvable.
3. A nontrivial solvable group has a proper derived subgroup. So `[Gamma, Gamma] = 1`, and `Gamma` is an
   abelian simple group, hence finite cyclic. This is a contradiction.

## Proof of (A)

Let `Q`, `R`, `Gamma = Q/<<R>>` and `sigma` be as in (A), with `L = sigma(Q)` virtually solvable and
`||sigma(r) - 1|| < 1/2` for `r` in `R`.
1. Let `X = { x sigma(r) x^-1 : x in L, r in R }`. Conjugation by a unitary preserves `||. - 1||`, so every element
   of `X` is within `1/2` of `1`.
2. By Lemma 4 (with `1/2 < sqrt 2`), any two elements of `X` commute. Hence `N = <X>` is abelian. It is normal
   in `L`, because `X` is conjugation invariant.
3. The composite `Q -> L -> L/N` kills `R`, so it factors through `Gamma`, and `L/N` is a quotient of `Gamma`.
   `L/N` is also a quotient of the virtually solvable group `L`, so it is virtually solvable. By hypothesis
   `L/N = 1`.
4. So `L = N` is abelian. In an abelian group conjugation is trivial, so `X = sigma(R)` and `L = <sigma(R)>`.

## Proof of (B): Thompson's V

1. **Hypothesis of (A).** `G0 -> V` is onto with kernel `<<r5, ..., r8>>`
   (`thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`, item 4). `V` is infinite and simple
   (`thompson-v-finitely-presented-infinite-simple`). By Lemma 5, `V` has no nontrivial virtually solvable
   quotient.
2. **Abelianization of G0.** Write `G0^ab` additively.
   - The relations give `2a = 0`, `3b = 0`, `4a + 4b = 0`, `2c = 0` and `3a + 3c = 0`.
   - Hence `4b = 0`, so `b = 4b - 3b = 0`, and then `a + c = 3a + 3c = 0`, so `c = a`.
   - So `G0^ab = Z/2`, generated by the image of `a`. Its nontrivial character is
     `eta : a, c -> -1, b -> 1`. It is well defined because every defining relator has even `{a,c}`-letter count:
     `a^2`, `b^3`, `(ab)^4`, `c^2`, `(ac)^3`, with counts 2, 0, 4, 2 and 6.
3. **Values on the long relators.** `eta(r)` is `(-1)` to the number of letters `a^(+-1)` or `c^(+-1)` in `r`.
   - For `r5 = (cab^-1aba)^2 cb (cabab^-1a)^2` the counts are `2*4 + 1 + 2*4 = 17`, which is odd. So
     `eta(r5) = -1`.
   - The same count gives `eta(r8) = -1` and `eta(r6) = eta(r7) = 1` (checked in `abelian_and_monomial_check.py`,
     Part 1). Only `eta(r5) = -1` is needed below.
4. **Conclusion.** Let `rho : G0 -> U(n)` have virtually solvable image and `D(rho) < 1/2`.
   - By (A), `rho(G0)` is abelian, so `rho` factors through `G0^ab = Z/2`. Hence `C^n = E_1 ⊕ E_eta`, where `G0`
     acts trivially on `E_1` and by `eta` on `E_eta`.
   - If `E_eta != 0`, then `rho(r5)` acts by `-1` on it, so `D(rho) >= ||rho(r5) - 1|| = 2`. This contradicts
     `D(rho) < 1/2`.
   - So `E_eta = 0` and `rho` is trivial.

Equivalently, every nontrivial `rho` with virtually solvable image has `D(rho) >= 1/2`. For an irreducible
`rho != 1` this is the uniform gap of criterion (3) of `thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes`,
with `epsilon_0 = 1/2`, on the virtually solvable-image locus.

## Proof of (C): Thompson's T

1. **Hypothesis of (A).** `thompson-t-lochak-schneps-presentation` gives
   `T = (Z/4 * Z/3) / <<r_1, r_2, r_P>>`. `T` is infinite and simple (Cannon--Floyd--Parry, *Introductory
   notes on Richard Thompson's groups*, Enseign. Math. 42 (1996), Theorem 5.8, as already cited in
   `thompson-t-has-full-mf-radical` and `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-proof`). By Lemma 5, `T` has
   no nontrivial virtually solvable quotient.
2. **Characters.** `(Z/4 * Z/3)^ab = Z/4 x Z/3 = Z/12`. A character `chi` is given by `chi(alpha) = i^j` and
   `chi(beta) = omega^k`, with `omega = e^(2 pi i/3)`.
   - `chi(r_1) = chi(r_2) = 1`, since both are commutators.
   - `chi(r_P) = chi(beta alpha)^5`, which is the image of `5(j,k) = (j, 2k)` in `Z/4 x Z/3`. It is `1` only
     for `(j,k) = (0,0)`.
   - For `chi != 1`, `chi(r_P)` is therefore a nontrivial 12th root of unity, so
     `|chi(r_P) - 1| >= |e^(2 pi i/12) - 1| = 2 sin(pi/12) > 1/2`.
3. **Conclusion.** Suppose `A^4 = B^3 = 1`, `<A,B>` is virtually solvable and `D(A,B) < 1/2`.
   - By (A), `<A,B>` is abelian, so `C^n` splits into joint eigenlines on which the pair acts by characters
     `chi`.
   - On each line, `|chi(r_P) - 1| <= D(A,B) < 1/2`, so `chi = 1` by Step 2. Hence `(A,B) = (1,1)`.

## Proof of (D)

`rho(G0)` and `<A,B>` are finitely generated subgroups of `GL_n(C)`. By the Tits alternative (Tits 1972,
Theorem 1, quoted in the claim), each either contains a nonabelian free group or is virtually solvable.
- An amenable group contains no nonabelian free group, so an amenable image is virtually solvable.
- (B) and (C) then apply.

## Where the argument stops

For an image containing `F_2`, Lemma 4 fails at Step 2: the descent `h_k` tends to `1` but need not
enter a subgroup normalized and centralized by `g`. The closure's identity component can be non-abelian,
for example `SU(2)`, and near-identity elements of `SU(2)` do not commute. This is the only locus left open
in `thompson-v-is-not-mf` by this route. A natural next test is images whose closure has identity component
of bounded semisimple rank.

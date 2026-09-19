---
rg: 2
id: thompson-v-haar-regular-gluings-have-defect-two-proof
kind: route
title: Collins freeness plus vanishing diagonal blocks kills every cyclically alternating trace in a Haar-glued regular pair, and the four V relators are cyclically alternating
target: thompson-v-haar-regular-gluings-have-defect-two
requires:
  - collins-haar-constant-matrices-asymptotic-freeness
  - thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3
  - thompson-v-hyperlinear-iff-unitary-s4-s3-gluings-fix-long-words
---

Notation is as in the target. `A = <a>` is the amalgamated subgroup, of order 2. A *syllable* is a nonidentity element
of `S4 \ A` or of `S3 \ A`. A word is **cyclically alternating** if it has the form

```text
w = x_1 y_1 x_2 y_2 ... x_L y_L,     L >= 1,   x_j in S4 \ A,   y_j in S3 \ A.
```

## Step 0. A model whose constant blocks do not depend on k

1. Fix `pi4 = lambda_S4` on `C^24`. Fix `pi3 = lambda_S3 (x) 1_4` on `C^24 = C^6 (x) C^4`.
2. Conjugate both by fixed unitaries so that `pi4(a) = pi3(a) = diag(1_12, -1_12)`. This is possible because in each
   regular representation the eigenvalues `+-1` of `a` have multiplicity 12.
3. Put `rho4 = pi4 (x) 1_k` and `rho3 = pi3 (x) 1_k` on `C^24 (x) C^k`. Order the basis as
   `(E_+ (x) C^k) (+) (E_- (x) C^k)`, where `E_+-` are the `+-1` eigenspaces of `pi(a)`. Then
   `rho4(a) = rho3(a) = A`.

**Independence of choices.**
- Any other choices of `rho4`, `rho3` as in the target differ from these by conjugation by fixed unitaries `V4`, `V3`
  in the commutant `C(A) = U(m) x U(m)`.
- The law of `sigma_U` is unchanged, up to one fixed conjugation, because
  `(V4 rho4 V4^*, U V3 rho3 V3^* U^*) = V4 (rho4, (V4^* U V3) rho3 (V4^* U V3)^*) V4^*`.
- `V4^* U V3` is again Haar on `C(A)`, and conjugation does not change traces or norms.
- The same remark identifies the model with the parameterization `(A_0, B_0, W^* C_0 W)`, `W` Haar on `C(A_0)`, of
  `thompson-v-hyperlinear-iff-unitary-s4-s3-gluings-fix-long-words`. Haar measure is inversion invariant, so `W^*` is
  Haar as well.

**Blocks.**
- For `M` in `M_n(C)` write `M_(st)` in `M_m(C)`, `s, t in {1, 2}`, for its blocks with respect to
  `C^n = C^m (+) C^m`. These are the `+1` and `-1` eigenspaces of `A`.
- Then `rho4(x)_(st) = pi4(x)_(st) (x) 1_k` and `rho3(y)_(st) = pi3(y)_(st) (x) 1_k`, where the `pi(.)_(st)` are fixed
  `12 x 12` matrices.
- For every noncommutative monomial `q` in these blocks, `tr_m q = tr_12 q(pi-blocks)`, which is independent of `k`.

**Padding.** Collins' theorem is indexed by all `d`. For `d = 12k + r` with `0 <= r < 12`, put
`W^d = (pi-blocks (x) 1_k) (+) 0_r`.
- For monomials of degree at least 1, `tr_d q(W^d) = (12k/d) tr_12 q(pi-blocks)`, which converges to
  `tr_12 q(pi-blocks)`.
- For the empty monomial, `tr_d q(W^d) = 1`.
- So the family has a joint limit distribution, and along `d = 12k` it is our family.

**Diagonal blocks vanish (property P).** For `x` in `S4 \ A` and `s in {1, 2}`, let `P_1 = (1 + pi4(a))/2` and
`P_2 = (1 - pi4(a))/2`. Then

```text
tr_12 pi4(x)_(ss) = (1/12) Tr(P_s pi4(x)) = (1/24) (Tr pi4(x) +- Tr pi4(a x)) = 0,
```

because `x != e` and `a x != e`, and the regular character vanishes off the identity. The same computation applies
to `y` in `S3 \ A`, since `Tr pi3(y) = 4 Tr lambda_S3(y)`.

## Step 1. Cyclically alternating traces vanish

**Lemma 1.** Let `w` be cyclically alternating. Then `tr_n sigma_U(w) -> 0` in probability as `k -> infinity`, and
`P(|tr_n sigma_U(w)| >= epsilon) = O(k^(-2))` for every `epsilon > 0`.

*Proof.*

**Expansion into block words.** Since `U = diag(U_1, U_2)`, we have `(U M U^*)_(st) = U_s M_(st) U_t^*`. Write
`X^j = rho4(x_j)` and `Y^j = rho3(y_j)`. Then `sigma_U(w) = X^1 (U Y^1 U^*) X^2 (U Y^2 U^*) ... X^L (U Y^L U^*)` and

```text
tr_n sigma_U(w) = (1/2) sum over s_0, t_1, s_1, ..., t_L in {1,2}, with s_L := s_0, of tr_m T, where
T = X^1_(s_0 t_1) U_(t_1) Y^1_(t_1 s_1) U^*_(s_1) X^2_(s_1 t_2) U_(t_2) ... X^L_(s_(L-1) t_L) U_(t_L) Y^L_(t_L s_L) U^*_(s_L).
```

There are `4^L` terms. It suffices to show that each `tr_m T` tends to 0 at the stated rate. Write each term as a
linear word

```text
T = b_1 v_1 b_2 v_2 ... b_(2L) v_(2L),
```

where the `b_j` are constant blocks and the `v_j` are among `U_1, U_2, U_1^*, U_2^*`. Say that `b_j` is **flanked by
equal indices** if `j >= 2` and `v_(j-1)`, `v_j` involve the same unitary `U_s`.
- For `b_(2i) = Y^i_(t_i s_i)` the flanks are `U_(t_i)` and `U^*_(s_i)`.
- For `b_(2i-1) = X^i_(s_(i-1) t_i)` with `i >= 2` the flanks are `U^*_(s_(i-1))` and `U_(t_i)`.

In both cases the indices are equal exactly when `b_j` is a diagonal block. By property P of Step 0, such a block has
`tr_m b_j = 0` for every `k`. It follows that `phi(b_j) = 0`.

**Passage to the limit.** Apply the imported theorem (a), (b) with `d = m = 12k`, the independent Haar unitaries
`U_1, U_2`, and the padded constant family of Step 0.
- `tr_m T` converges in probability, at rate `O(m^(-2)) = O(k^(-2))`, to `phi(b_1 v_1 ... b_(2L) v_(2L))`.
- Here `phi` is a state on the free product of three subalgebras: `B` (the limits of the blocks), `alg(u_1, u_1^*)`
  and `alg(u_2, u_2^*)`.
- By the remark in the imported node, `phi(u_s) = phi(u_s^*) = 0`.

**The limit is 0.**
1. Write `b_j = phi(b_j) 1 + b_j°` with `phi(b_j°) = 0` for every `j`, and multiply out. This gives `2^(2L)` terms.
2. A term that uses the scalar `phi(b_j)` for some `b_j` flanked by equal indices is 0.
3. In every other term, the product is a scalar times a nonempty word in the letters `b_j°` and `v_j`. It contains all
   `2L >= 2` letters `v_j`, in their original order. Two cases:
   - If the scalar was taken for `b_j` with `j >= 2`, then `v_(j-1)` and `v_j` become adjacent. They then involve
     different unitaries `u_1 != u_2`, so they lie in different free subalgebras.
   - Otherwise every `b_j°` in `B` sits between letters from `alg(u_1, u_1^*)` or `alg(u_2, u_2^*)`.
4. So consecutive letters always come from different subalgebras among the three free ones, and every letter is
   centered.
5. By the definition of freeness, `phi` of such a word is 0.

Hence `phi(T) = 0`, and summing the `4^L` terms proves the lemma. `QED`

## Step 2. Part (i): every element of G0

**Lemma 2 (syntactic reduction).** Every `g` in `G0` is conjugate in `G0` to one of the following:
- `e`;
- a nonidentity element of `S4` or of `S3`;
- an element represented by a cyclically alternating word.

*Proof.*
1. Write `g` as a word in `a, b, c` and cut it into maximal runs of letters from one factor. The letter `a` belongs to
   both factors and may join either run.
2. Evaluate each run in its finite factor, giving a sequence of factor elements. Repeat the following while possible:
   - delete an identity entry;
   - merge two adjacent entries from the same factor;
   - if an entry lies in `A`, multiply it into a neighbour, which is possible since `A` lies in both factors.
   Each move shortens the sequence, so the process ends. It ends with the empty sequence (so `g = e`), with a single
   entry, or with an alternating sequence of length at least 2 whose entries all lie outside `A`.
3. In the last case, if the first and last entries lie in the same factor, conjugate by the first entry: move it to
   the end and merge it there. Then apply step 2 again. Again the length drops, so the process ends.
4. It ends with at most one entry, or with an alternating sequence whose first and last entries lie in different
   factors. Such a sequence has even length and, after a cyclic rotation (a further conjugation) if needed, is
   cyclically alternating. `QED`

**Proof of (i).** Traces are conjugation invariant, so apply Lemma 2 and treat the three cases.
- `g` conjugate to `e`: then `tr sigma_U(g) = 1` for every `U`.
- `g` conjugate to a nonidentity factor element `x`: then `tr sigma_U(g)` is `tr rho4(x)` or `tr rho3(x)`. This is the
  normalized regular character, so it is 0 for every `U`.
- `g` conjugate to a cyclically alternating word: then `tr sigma_U(g) -> 0` by Lemma 1.

In the third case `g != e`, since otherwise `tr sigma_U(g) = 1` identically. So `tr sigma_U(g) -> delta_(g,e)` for all
`g`. This is (i), and convergence in distribution to `lambda_G0` means exactly this. The argument reproves, in
passing, that a cyclically alternating word is nontrivial in `G0`.

## Step 3. Parts (ii) and (iii): spectra of relators

**Powers.** Let `w` be cyclically alternating. For `j >= 1`, the power `w^j` is the concatenation of `j` copies of
`w`. The last syllable of `w` lies in `S3` and the first in `S4`, so the concatenation is again cyclically alternating.
`w^(-1) = y_L^(-1) x_L^(-1) ... y_1^(-1) x_1^(-1)` is cyclically alternating after rotating it by one syllable. So, by
Lemma 1, `tr sigma_U(w)^j -> 0` in probability for every `j != 0`.

**Relators.** Part 1 of `experiments/thompson-v-random-gluing-defect-2026-09-17/random_gluing.py` applies the moves of
Lemma 2 exactly, by permutation arithmetic in the faithful actions of `S4` on the four cones `00, 01, 10, 11` and of
`S3` on the three cones `00, 01, 1`, which are the actions used in `thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`.

**Why the conventions do not matter.**
- These permutations satisfy the defining relations of the factors. The relations are also checked numerically in
  Part 2, with error `1e-15`.
- They generate groups of orders 24 and 6, so they are faithful copies of the abstract factors.
- Membership of a syllable in `A` does not depend on whether products are composed left to right or right to left.
  Indeed `p -> p^(-1)` identifies the opposite group with the group and fixes `A`.
Its output (`out_random_gluing.txt`) records that each `r_i` is conjugate in `G0` to a cyclically alternating word:

| relator | letters | cyclic syllable length |
|---|---|---|
| `r5` | 26 | 10 |
| `r6` | 28 | 20 |
| `r7` | 26 | 16 |
| `r8` | 37 | 28 |

Line `PART1 PASS` checks that every final syllable lies outside `A`. Conjugation changes neither spectra nor norms,
so the power statement applies to `sigma_U(r_i)`.

**Equidistribution.** Let `mu_k` be the normalized eigenvalue counting measure of the unitary `sigma_U(r_i)`. Then
`int z^j d mu_k = tr sigma_U(r_i)^j -> 0` in probability for every `j != 0`.
- So `int p d mu_k -> int p d Haar` in probability for every trigonometric polynomial `p`.
- The `mu_k` are probability measures and trigonometric polynomials are uniformly dense in `C(T)`, so the same holds
  for every continuous `f`. This is (ii).

**Norms.**
- **Operator norm.** For `epsilon > 0` choose continuous `f >= 0`, supported in the arc `{z : |z - 1| > 2 - epsilon}`,
  with `int f d Haar > 0`.
  - With probability tending to 1, `int f d mu_k > 0`, so some eigenvalue lies in that arc and
    `||sigma_U(r_i) - 1|| > 2 - epsilon`.
  - The bound `||sigma_U(r_i) - 1|| <= 2` always holds.
- **Hilbert--Schmidt norm.** `||sigma_U(r_i) - 1||_2^2 = 2 - 2 Re tr sigma_U(r_i) -> 2` in probability.

For (iii), take `w` of infinite order. By Lemma 2 it is conjugate to a cyclically alternating word, since factor
elements have finite order. Then the same argument applies.

## Step 4. Part (iv): rate and almost sure convergence

Each `tr sigma_U(g)` is a finite sum of terms `tr_m T`, each with deviation probability `O(k^(-2))` by (b). So
`sum_k P(|tr sigma_U(g) - delta_(g,e)| >= epsilon) < infinity`. By the first Borel--Cantelli lemma, which needs no
independence, `tr sigma_U(g) -> delta_(g,e)` almost surely, simultaneously for the countably many `g` and rational
`epsilon`. The argument of Step 3 then runs pointwise on this full-measure event. `QED`

## Consequences

1. Let `G_(k, epsilon)` be the set of gluings `W` in `U(12k) x U(12k)` with `max_i ||r_i - 1||_2 <= sqrt 2 - epsilon`.
   Its Haar measure is at most `P(||sigma_U(r_5) - 1||_2 <= sqrt 2 - epsilon)`, which tends to 0 by Step 3. The same
   holds for the operator norm with `2 - epsilon`. This covers the good sets of criterion 4 of
   `thompson-v-hyperlinear-iff-unitary-s4-s3-gluings-fix-long-words` for every `epsilon < sqrt 2`.
2. Only two inputs were used: the joint limit distribution of the blocks, and `phi(diagonal block of a non-A element)
   = 0`. So Steps 1--4 hold unchanged for any balanced sequence `(rho4, rho3)` with `rho4(a) = rho3(a) = A` whose
   characters are `o(n)` off the identity and whose blocks have a joint limit distribution.
   - Property P then holds in the limit.
   - The factor-element case of Step 2 gives `tr -> 0` instead of `= 0`.

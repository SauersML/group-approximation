---
rg: 2
id: root-splits-into-large-and-fixed-characteristic-witnesses-proof
kind: route
title: Amplify rank models by conjugation tensors, sort ultraproducts by characteristic, diagonalize over primes, and assemble witnesses by free products
target: root-splits-into-large-and-fixed-characteristic-witnesses
requires: [non-weakly-sofic-iff-non-finite-field-linear-sofic-group, countable-group-embeds-in-two-generator-simple-group]
---

Groups are countable.
- `rho(A, B) = rank(A - B)/n` on `M_n(F)`.
- A **`(W, eps)`-model** of `G` over a field `F` is a map `phi : W -> GL_n(F)`, where `W` is a finite subset of `G`
  containing `1`, such that:
  - `rho(phi(g)phi(h), phi(gh)) <= eps` whenever `g, h, gh` lie in `W`;
  - `rho(phi(g), 1) >= 1/4` for `g` in `W \ {1}`.

## 1. Uniform amplification

**Lemma 1.** Let `A` be in `GL_n(F)` with `rank(A - 1) = k`. Then the centralizer `C(A)` in `M_n(F)` has dimension at
most `(n - k)^2 + k^2`. Consequently `rho(A (x) A^(-T), 1) >= 2r(1 - r)`, where `r = k/n`.

*Proof.*
1. Centralizer dimensions do not change under field extension, so we may assume `F` algebraically closed.
2. `C(A)` is the direct sum of the centralizers of `A` on its generalized eigenspaces. On the generalized eigenspace
   of an eigenvalue `lambda`, with Jordan partition `mu`, the centralizer has dimension `sum_i (mu'_i)^2`, where
   `mu'` is the conjugate partition and `mu'_1` is the geometric multiplicity.
3. *Eigenvalue 1.* Here `mu'_1 = n - k`. Put `s = a_1 - (n - k)`, where `a_1` is the algebraic multiplicity. The
   remaining parts sum to `s`, so they contribute at most `s^2`.
4. *Other eigenvalues.* Their algebraic multiplicities sum to `n - a_1 = k - s`, so they contribute at most
   `(k - s)^2`.
5. Hence `dim C(A) <= (n - k)^2 + s^2 + (k - s)^2 <= (n - k)^2 + k^2`.
6. `A (x) A^(-T)` acts on `F^n (x) F^n = M_n(F)` as `X -> A X A^(-1)`. So its fixed space is `C(A)`, and
   `rho(A (x) A^(-T), 1) = 1 - dim C(A)/n^2 >= 1 - (1 - r)^2 - r^2 = 2r(1 - r)`. ∎

**Lemma 2 (amplifier).** For `phi : W -> GL_n(F)` put `T phi(g) = (phi(g) (x) 1_n) (+) (phi(g) (x) phi(g)^(-T))` in
`GL_(2n^2)(F)`.
- If `phi` has multiplicative defect at most `delta` on `W`, then `T phi` has defect at most `3 delta / 2`.
- If `rho(phi(g), 1) = r`, then `rho(T phi(g), 1) >= min(1/4, 5r/4)`.
- Iterating `m` times gives defect at most `(3/2)^m delta` and separation at least `min(1/4, (5/4)^m r)`, over the same
  field `F`.

*Proof.*
1. *Defect.* Let `A = phi(g)`, `B = phi(h)`, `C = phi(gh)`. Then
   `AB (x) (AB)^(-T) - C (x) C^(-T) = (AB - C) (x) (AB)^(-T) + C (x) ((AB)^(-1) - C^(-1))^T`.
   - `(AB)^(-1) - C^(-1) = (AB)^(-1)(C - AB)C^(-1)`, so it has the same rank as `AB - C`.
   - `rank(X (x) Y) = rank X * rank Y`, so the tensor block has rank at most `2n rank(AB - C)`.
   - The first block has rank `n rank(AB - C)`.
   - Dividing the total by `2n^2` gives at most `(3/2) rho(AB, C)`.
2. *Separation.* `rho(T phi(g), 1)` is the average of `r` and `rho(A (x) A^(-T), 1)`, so it is at least
   `g(r) = r(3 - 2r)/2` by Lemma 1.
   - For `r <= 1/4`: `g(r) >= 5r/4`.
   - On `[1/4, 1]`: `g` is concave, with `g(1/4) = 5/16` and `g(1) = 1/2`, so `g >= 1/4`.
3. *Iteration.* Induct using `min(1/4, 5r'/4) >= min(1/4, (5/4)^(j+1) r)` whenever `r' >= min(1/4, (5/4)^j r)`. ∎

**Restriction of scalars.** An `F_q`-linear map on `F_q^n`, with `q = p^e`, is an `F_p`-linear map on `F_p^(ne)`. Its
`F_p`-rank is `e` times its `F_q`-rank. So `rho` is unchanged, and a model over `F_q` is a model over `F_p`.

**Lemma 3 (models).** Let `G` be countable.
- (i) `G` is in `L_p` iff every `(W, eps)` has a model over `F_p`.
- (ii) `G` is in `L_inf` iff for every `(W, eps)` and every `N` there is a model over `F_l` for some prime `l >= N`.
- (iii) `G` embeds in some rank ultraproduct over finite fields iff every `(W, eps)` has a model over some finite field.
- The same argument over a fixed field `F` gives: `G` is `F`-linear sofic iff every `(W, eps)` has a model over `F`.

*Proof.*
1. *Models give embeddings.*
   - Exhaust `G` by finite sets `W_1 <= W_2 <= ...` and take a `(W_j, 1/j)`-model `phi_j` over `F_j`. In case (ii)
     choose `char F_j >= j`.
   - Put `Phi(g) = (phi_j(g))_j`, using `1` when `g` is not in `W_j`.
   - Along a nonprincipal ultrafilter `omega`, `Phi` is a homomorphism to `prod_omega GL_(n_j)(F_j) / N_omega`. It
     is injective because separation stays at least `1/4`.
   - In case (i) all `F_j` have characteristic `p`. In case (ii) the characteristic tends to infinity.
2. *Embeddings give models.*
   - Let `Psi` be an embedding into `prod_omega GL_(n_i)(F_(q_i)) / N_omega` with lifts `(phi_i(g))_i`.
   - Fix `(W, eps)`. Let `r_0` be the minimum over `g` in `W \ {1}` of the length of `Psi(g)`. It is positive. Choose
     `m` with `(5/4)^m r_0/2 >= 1/4`.
   - The set `I` of indices `i` for which `phi_i` has defect at most `(2/3)^m eps` on `W` and separation at least
     `r_0/2` lies in `omega`.
   - For `i` in `I`, Lemma 2 applied `m` times gives a `(W, eps)`-model over `F_(q_i)`. Restriction of scalars makes
     it a model over the prime field.
   - In case (i), `I` meets `{i : q_i` is a power of `p}`, since that set is also in `omega`. In case (ii), `I` meets
     `{i : char F_(q_i) >= N}`.
   - The constant `1/4` and the passage to the prime field do not depend on the characteristic. ∎

## 2. The spectrum

1. **`S(G)` is nonempty iff `G` is linear sofic over finite fields.**
   - Take an embedding in `prod_omega GL_(n_i)(F_(q_i))`, with `p_i = char F_(q_i)`.
   - Either some prime `p` has `{i : p_i = p}` in `omega`, or none does.
   - In the first case, change the factors off an `omega`-null set to `GL_1(F_p)`. The ultraproduct does not change,
     so `G` is in `L_p`.
   - In the second case, every `{i : p_i < N}` is a finite union of `omega`-null sets, hence null. So `p_i -> infinity`
     along `omega` and `G` is in `L_inf`.
   - The converse is immediate.
2. **Monotonicity.** Every class `L_p` and `L_inf` is closed under subgroups. So `S(G)` contains `S(G')` whenever
   `G <= G'`, and a free product has spectrum inside the intersection of the spectra of its factors.
3. **Sofic groups.**
   - For permutations `a` and `b` on `n` points, `rank(P_a - P_b)` is at most the number of points where `a` and
     `b` differ.
   - `rank(P_a - 1) = n - #cycles(a)`, which is at least half the number of moved points.
   - So sofic models give linear models over every field, with separation at least half the Hamming separation.
     Sofic separation can be taken close to `1`, so this is at least `1/4`. Hence `S(G)` is everything.
4. **Finiteness.**
   - Suppose `S(G)` contains infinitely many primes. Fix `(W, eps)` and `N`, and pick a prime `p >= N` in `S(G)`.
   - Lemma 3(i) gives a `(W, eps)`-model over `F_p`, with the same separation `1/4`.
   - By Lemma 3(ii), `G` is in `L_inf`.
   - This is the step where a characteristic-dependent separation constant would break the argument.

## 3. The reduction

1. **(root) implies (a) and (b).**
   - By `non-weakly-sofic-iff-non-finite-field-linear-sofic-group`, some countable `W` is not linear sofic over finite
     fields. So `S(W)` is empty by §2.1.
   - Take `H = G = W`.
2. **(a) and (b) imply (root).**
   - Take `H` not in `L_inf` and `G` in no `L_p`. Then `S(H * G)` is contained in `S(H) ∩ S(G)`.
   - `S(H)` lies in the primes and `S(G)` lies in `{inf}`, so the intersection is empty.
   - So `H * G` is not linear sofic over finite fields, and the root follows by the same equivalence.
3. **Economical form.**
   - Fix `H` not in `L_inf`. By §2.4, `S(H) = {p_1, ..., p_k}` is finite.
   - Given `G_(p_j)` not in `L_(p_j)`, the spectrum of `W = H * G_(p_1) * ... * G_(p_k)` lies in
     `S(H) \ {p_1, ..., p_k}`, which is empty.
   - The converse is part 1.
4. **Two-generator simple witnesses.**
   - Component (b) with one group is equivalent to "for every `p` some `G_p` is not in `L_p`". Take the free product of
     countably many `G_p`; its spectrum is empty on the primes.
   - Countable witnesses of (a), (b), or the root embed in two-generator simple groups
     (`countable-group-embeds-in-two-generator-simple-group`). Spectra only shrink under this embedding. ∎

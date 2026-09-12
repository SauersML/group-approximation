# F_9 coefficients and Hadamard spectral idempotents for the ternary Cohn family

Lane `w3-corner-cohn-b`, 2026-09-12. Supports `ternary-anti-central-cohn-family-over-f9`,
`f9-hadamard-spectral-idempotents-are-half-idempotents` and
`f9-hadamard-spectral-idempotent-is-full`. It tests the idea gk-l3-units recorded on
`ternary-anti-central-summand-has-quaternary-leavitt-family`: over F_9, depth-one Hadamard units
have non-monomial spectral idempotents.

## 0. Notation

- `R = L_(F_3)(1,2)`, `G = R^x`, `z = -1`, `S = F_3[G]`, `eps_- = 2(1 - [z])`, `S_- = eps_- S`,
  with unit `1_- = eps_-`. In `S_-`, `[z] = -1_-`.
- `S^(9) = F_9[G] = F_9 (x)_(F_3) S` and `S_-^(9) = eps_- S^(9) = F_9 (x) S_-`. The group is still
  `G = L_(F_3)(1,2)^x`; only the coefficients change.
- `i` in `F_9` with `i^2 = -1`; Frobenius `phi(i) = -i`.
- A depth-one constant unit is written by its matrix `(c_ab)` for `sum_ab c_ab s_a t_b`.
- `h = s0 t0 + s0 t1 + s1 t0 - s1 t1`, matrix `[[1,1],[1,-1]]` (the Hadamard unit).
- `u = s0 t0 + s1 t0 - s1 t1`, matrix `[[1,0],[1,-1]]`.
- `J : M_2(S_-) -> S_-`, the injective unital algebra homomorphism of
  `anti-central-ternary-summand-contains-its-matrix-ring`, part 3.
- A unital two-pair Cohn family in a ring `A` is `sigma_1, sigma_2, tau_1, tau_2` with
  `tau_i sigma_j = delta_ij 1_A`.

## 1. Coefficient extension neither helps nor hurts

**Theorem 1.1.** `S_-^(9)` has a unital two-pair Cohn family if and only if `S_-` has one. The same
holds for any finite system of unital ring identities, such as a quaternary Leavitt family.

*Proof.*
- *If.* `S_-` is a unital subalgebra of `S_-^(9)`.
- *Only if.* The regular representation `rho : F_9 -> M_2(F_3)`, `rho(a + b i) = [[a, -b], [b, a]]`,
  is a unital ring embedding, since `[[0,-1],[1,0]]^2 = -I`. So `rho (x) id : F_9 (x) S_- ->
  M_2(F_3) (x) S_- = M_2(S_-)` is a unital algebra homomorphism. Compose it with `J`. The composite
  `Phi = J o (rho (x) id) : S_-^(9) -> S_-` is a unital ring homomorphism. Unital ring homomorphisms
  carry unital identities to unital identities, so a Cohn family maps to a Cohn family. QED

**Remark 1.2.** Iterating part 4 of the matrix-ring claim (`M_(2^n)(S_-)` embeds unitally in `S_-`)
gives the same equivalence over every field `F_(3^(2^n))`. Fields `F_(3^k)` with `k` not a power of
two are not covered by this argument.

**Consequence.** F_9 designs are a legitimate search space for the exact target
`ternary-anti-central-summand-has-cohn-family`, not only for Gottschalk. Descent needs no Galois
averaging: `Phi` does it.

## 2. The depth-one Hadamard spectral idempotents

**Lemma 2.0.**
- `h^2 = z`: the matrix square is `[[2,0],[0,2]] = -I`.
- `u^2 = 1`: `[[1,0],[1,-1]]^2 = [[1,0],[0,1]]`.
- `u h u = -h = h z`: `u h = [[1,1],[0,2]]`, and `(u h) u = [[2,-1],[2,-2]] = [[-1,-1],[-1,1]] = -h`.

So in `S_-^(9)`: `[h]^2 = [z] = -1_-` and `[u][h][u] = [h][z] = -[h]`.

**Proposition 2.1.** Put `f_+ = 2(1_- + i[h])` and `f_- = 2(1_- - i[h])`.
1. `f_+` and `f_-` are orthogonal idempotents with `f_+ + f_- = 1_-`.
2. Frobenius swaps them: `phi(f_+) = f_-`.
3. `[u] f_+ [u] = f_-`, and so `f_+ [u] = [u] f_-`.
4. `E_11 = f_+`, `E_22 = f_-`, `E_12 = f_+ [u]`, `E_21 = [u] f_+` are matrix units spanning a copy of
   `M_2(F_9)` that contains `1_-`.
5. `[1_-] = 2[f_+]` in `K_0(S_-^(9))`.

*Proof.*
1. `f_+^2 = 4(1 + 2i[h] + i^2 [h]^2) = 4(1 + 2i[h] + 1) = 8(1 + i[h]) = f_+`, using `i^2 [h]^2 =
   (-1)(-1) = 1` and `8 = 2`. The same computation works for `f_-`. The sum is `4 = 1`, and
   `f_+ f_- = 4(1 - i^2[h]^2) = 4(1 - 1) = 0`.
2. `phi` fixes `[h]` and sends `i` to `-i`.
3. `[u](1 + i[h])[u] = 1 + i[uhu] = 1 - i[h]`, since `u^2 = 1`.
4. `E_12 E_21 = f_+ [u][u] f_+ = f_+`. `E_21 E_12 = [u] f_+ [u] = f_-`.
   `E_21 E_21 = [u] f_+ [u] f_+ = [u][u] f_- f_+ = 0`, and likewise `E_12 E_12 = 0`. The remaining
   products follow from these and part 1.
5. `f_+ ~ f_-` through `E_12` and `E_21`, and `f_+ + f_- = 1_-`. QED

**Proposition 2.2.** If `c f_+ b = 1_-` for some `b, c` in `S_-^(9)`, then `S_-^(9)` has a unital
two-pair Cohn family. By Theorem 1.1, so does `S_-`, which refutes Gottschalk's conjecture on `G`.

*Proof.* Put `sigma_1 = f_+ b`, `sigma_2 = [u] f_+ b`, `tau_1 = c f_+` and `tau_2 = c f_+ [u]`.
- `tau_1 sigma_1 = c f_+ b = 1_-`.
- `tau_2 sigma_2 = c f_+ [u][u] f_+ b = 1_-`.
- `tau_1 sigma_2 = tau_2 sigma_1 = c f_+ [u] f_+ b = c [u] f_- f_+ b = 0`. QED

**Proposition 2.3 (the state filter carries over).** Let `Gamma <= G` contain `z`, `h`, `u` and the
supports of `b` and `c`. Suppose some group homomorphism `sigma : Gamma -> M^x` has `sigma(z) != 1`,
where `M` is an algebra over a field `k` containing `F_9` and carries a Sylvester rank function `r`
positive on nonzero idempotents. Then `c f_+ b != 1_-`.

*Proof.*
- **State.** Extend `sigma` `F_9`-linearly to `F_9[Gamma]`. `sigma(eps_-) = 2(1 - sigma(z))` is an
  idempotent, and it is nonzero because `sigma(z) != 1`. On idempotents `p` of `eps_- F_9[Gamma]`, put
  `s(p) = r(sigma(p)) / r(sigma(eps_-))`. It is additive on orthogonal idempotents, constant on
  Murray–von Neumann classes, and `s(1_-) = 1`.
- **Halving.** Part 3 of Proposition 2.1 gives `s(f_+) = s(f_-) = 1/2`.
- **Contradiction.** If `c f_+ b = 1_-`, put `x = f_+ b` and `y = c f_+`. Then `yx = 1_-` and
  `xy <= f_+`, so `1 = s(yx) = s(xy) <= s(f_+) = 1/2`. QED

This is `anti-central-rank-models-kill-ternary-corner-witnesses` with `(h, u)` in place of
`(w, d)`. F_9 does not relax the filter: the support subgroup must have no characteristic-three rank
model that moves `z`.

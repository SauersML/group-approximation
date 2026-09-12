# Stable realization of Z_3-equivariant permutations with one ancilla track

Lane `w4-z3-rotation`, 2026-09-12. This artifact supports the claim
`z3-equivariant-permutations-are-stably-realizable` (route
`z3-equivariant-permutations-stably-realizable-proof`). It also supports Attempts entries on
`z3-weight-one-rotation-is-not-an-automorphism-shadow` and
`injective-binary-automata-are-stably-formalizable`.

**Result in one line.** The weight-one rotation `rho` is not known to be a one-track shadow, but
`rho x id` is the shadow of an explicit equivariant polynomial automorphism of `A^6` over `F_2`. So
the pair `(rho, rho^-1)` is stably formalizable with one identity ancilla track, and so is every
bijective pair on `{0,1}^(Z_3)`.

## 0. Setup and moves

- **Tracks.** Data track `x` and ancilla track `y`, both in `A^3` over `F_2`, with the shift `R` acting
  diagonally. Put `s_1 = x_0 + x_1 + x_2` and `v_1 = x + s_1(1,1,1)`, which lies in the sum-zero plane
  `V`. Define `s_2, v_2` from `y` in the same way. Since 3 is odd, `(s_1, v_1, s_2, v_2)` is a linear
  coordinate system.
- **The field.** `V` is an `F_2[R]`-module with `F_2[R]/(R^2+R+1) = F_4`, where `R` acts as `omega`.
  So `V^2 = F_4^2`, and every matrix over `F_2[R]` commutes with the shift.
- **Boolean points.** In Fourier coordinates, a Boolean point is `(s_1, s_2, u_1, u_2)` with
  `s_i in F_2` and `u_i in F_4`, and the shift acts by `u -> omega u`. So there are 64 points. The fixed
  points are `u = 0`, and the free orbits are indexed by `F_2^2 x P^1(F_4)`: 20 orbits of 3 points.
- **Shadows.** An automorphism defined over `F_2` permutes the Boolean points, and shadows compose.
  By `finite-group-formalizability-equals-equivariant-automorphism` (stable form), `psi x id` being a
  shadow means `(psi, psi^-1)` is stably formalizable with one track.

All the moves below are equivariant polynomial automorphisms over `F_2`.

- **(M0) Diagonal shift.** `R` itself: `(v_1, v_2) -> (omega v_1, omega v_2)`.
- **(M1) Level-controlled `SL_2(F_4)`.**
  - For `c in F_4 = F_2[R]`, the shear `e_12(s_1 c) : v_1 -> v_1 + s_1 c v_2` is triangular, is its
    own inverse in characteristic 2, and is equivariant. The same holds for `e_21(s_1 c)`.
  - `SL_2(F_4) = E_2(F_4)`, so write `A` as a product of elementary matrices `e(c_i)` and put
    `Y_A = prod e(s_1 c_i)`.
  - The shadow of `Y_A` applies `A` to `(u_1, u_2)` at the levels `s_1 = 1` and does nothing at
    `s_1 = 0`.
- **(M2) Controlled level flips.** Let `f` be a Boolean function of `(v_1, v_2)` that is invariant under
  the shift on Boolean points.
  - Take any polynomial `p` restricting to `f`. Then `p + p o R + p o R^2` is an invariant polynomial
    restricting to `3f = f`.
  - Put `X_f : s_1 -> s_1 + (p + p o R + p o R^2)(v_1, v_2)`. It is an equivariant involution, and it
    changes only `s_1`.

## 1. Commutators give nonuniform pure rotations

**Lemma 1.** Let `l in P^1(F_4)` be a line, and let `A in SL_2(F_4)` fix `l` and act on it by `omega`.
Put `f_l(u) = [u != 0 and u in l]`, and let `C_l = X_(f_l) o Y_A o X_(f_l) o Y_A^-1`, with `Y_A^-1`
applied first. The shadow of `C_l` leaves `s_1` and `s_2` unchanged, and:
- on `u in l minus 0` with `s_1 = 1`, it sends `u -> omega^2 u`;
- on `u in l minus 0` with `s_1 = 0`, it sends `u -> omega u`;
- everywhere else it is the identity.

*Proof.* `A` fixes `l` and permutes the other four lines, so `f_l(A^(±1) u) = f_l(u)`.
1. **`u` not on `l`.** Neither flip fires, and `Y_A o Y_A^-1 = id`.
2. **`u in l` at `s_1 = 1`.**
   - `Y_A^-1` sends `u` to `omega^2 u`.
   - `X` moves the point to level 0.
   - `Y_A` does nothing at level 0.
   - `X` moves it back to level 1.
   - Net effect: `omega^2 u`.
3. **`u in l` at `s_1 = 0`.**
   - `Y_A^-1` does nothing.
   - `X` moves the point to level 1.
   - `Y_A` sends `u` to `omega u`.
   - `X` moves it back to level 0.
   - Net effect: `omega u`.

Such an `A` exists for every `l`: `diag(omega, omega^2)` fixes `[1:0]` with eigenvalue `omega`, and
`SL_2(F_4)` is transitive on `P^1(F_4)`. ∎

## 2. The theorem

**Theorem 2.** `Phi = rho x id`, whose shadow is `(s_1, s_2, u_1, u_2) -> (s_1, s_2, omega^(s_1) u_1, u_2)`,
is the shadow of an equivariant polynomial automorphism of `A^6` over `F_2`.

*Proof.*
1. **All lines.** The five `C_l` are pure rotations on disjoint sets, so they commute. Their product
   has shadow `u -> omega^2 u` at `s_1 = 1` and `u -> omega u` at `s_1 = 0`, for all `u != 0`.
2. **Correct the levels.** `Q = R o (prod_l C_l)^-1` has shadow `omega · omega = omega^2` at `s_1 = 1`
   and `omega · omega^2 = 1` at `s_1 = 0`.
3. **Split the rotation.** `B = diag(omega^2, omega)` has determinant `omega^3 = 1`, so `B in SL_2(F_4)`.
   `Y_B o Q` acts at `s_1 = 1` by `diag(omega^2, omega) · omega^2 = diag(omega, 1)`, and at `s_1 = 0` by
   the identity. That is `Phi`.
4. **This is `rho x id`.** `u(Rx) = omega u(x)`.
   - On the weight-one orbit (`s_1 = 1`, `u_1 != 0`), `rho = R`, so it multiplies `u_1` by `omega`.
   - At `111`, `u_1 = 0`.
   - On the weight-two orbit and at `000`, `s_1 = 0`.
   - `s_1` and the whole ancilla are unchanged.
∎

**Corollary 3.** For every shift-equivariant permutation `psi` of `{0,1}^(Z_3)`, `psi x id` is a
shadow. So every bijective pair on `{0,1}^(Z_3)` is stably formalizable with one ancilla track.

*Proof.*
- The order-12 group `K` of uniform shadows is realized on one track by `G_tri`, so `K x id` is
  realized.
- `K` has index 3 in the order-36 group `E` of equivariant permutations. A subgroup strictly between
  them would have order 24, which does not divide 36. So `<K, rho> = E`.
∎

## 3. Scope

- **The one-track claim stays OPEN.** `z3-weight-one-rotation-is-not-an-automorphism-shadow` asks
  whether `rho` is a shadow on `A^3`. Theorem B of the eigen-hyperplane artifact says a realization
  must move the cone. Nothing here decides it. Even if it is true, it cannot witness against
  `injective-binary-automata-are-stably-formalizable`, because one ancilla track removes it.
- **What survives stabilization.**
  - With `k` tracks, the fixed locus is `{v = 0} = A^k`.
  - Weights make the Jacobian block diagonal there, and the normal block is an `F_4`-linear
    `k x k` matrix over `F_4[s]`. Its norm to `F_2` is the constant Jacobian determinant 1, so
    `delta(T) = det_(F_4)` of the normal block is a unit, hence a constant in `F_4^×`.
  - `delta` is a homomorphism. It generalizes `lambda(T)` of Theorem A, but Theorem 2 shows that it
    does not constrain shadows.
- **What dies.** The invariant cone and the triangular stabilizer (Theorem B). Both use multiplicity
  one of `V`.
- **The mechanism.** A level flip controlled by a line, commuted with a shear controlled by the level,
  gives a rotation that depends on the level. Linear level-controlled moves alone keep the
  determinant constant across levels. The controlled flip is what separates lines and so frees the
  rotation.
- **Consequence for the counterexample program.** A finite-group shadow obstruction to stable
  formalizability has to survive this commutator. Candidates must come from infinite groups, where
  ancilla restoration has to cancel formally (the marker residue in the Attempts of the stable
  claim), not from one-track rigidity on `Z_3`.

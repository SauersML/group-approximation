# Liftable masas, part 3: vertex types equidistribute on finite SL_d(Z)-orbits (2026-09-13)

Lane `ex-hs-masa-lift-positive`. Parts 1-2: `research/artifacts/hs-masa-lift-positive-2026-09-13.md`
and `-part2-`. Answers, at the Theorem E pair, the requirement recorded in
`amenable-type-cycle-kills-liftable-masas`: a proof of (LM) must spend property (T) of the group
acting on vertex types.

## 0. Setting

- `Gamma = EL_r(R_+) < G = EL_r(L) x| SL_d(Z)`, with `R_+ = F_q[x_1..x_d]`, `L = F_q[x^(+-1)]`,
  `r, d >= 3`, and `H = SL_d(Z)`.
- `sigma : G -> U(prod_U M_n)` is trace-preserving (`tau o sigma = delta_e`) with (H1) roundings `pi_n`,
  padded so that `sigma_n` and `pi_n` act on the same space.
- `A_n = pi_n(Gamma)'`, and `z_rho` are the minimal central projections of `A_n` (the types
  `rho` of `pi_n`), with multiplicity `m_rho` and dimension `d_rho`. `p_n(rho) = tau(z_rho)`.
- `P_n` is the unit-type projection of `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`.
  By `vertex-rounding-alone-normalizes-each-theorem-e-model`, `tau(1 - P_n) -> 0`.
- `X` is the set of isomorphism classes of irreducible representations of `St_r(L)` that factor
  through `St_r(B)` for a finite quotient ring `B` of `L`. `H` acts on `L` by `phi_M(x^v) = x^(Mv)`,
  hence on `X` by `M . rho = rho o phi_M^(-1)`. This is a genuine action.

## 1. Types and finite orbits

1. **Unit types are points of `X`.** A unit-type constituent factors through `St_r(A_u)`, where `A_u`
   is a finite quotient of `R_+` in which every `x_i` is a unit. So `R_+ -> A_u` extends to
   `L -> A_u`. `St_r(R_+) -> St_r(A_u)` is onto, since it hits every generator `x_ij(a)`. So
   restriction to `Gamma` identifies unit-type `Gamma`-types with points of `X`.
2. **Every orbit is finite.** Units of a finite ring have finite order, so `x_i^m = 1` in `A_u` for
   some `m`. Then `L -> A_u` factors through `L / I_m = F_q[(Z/m)^d]`, where
   `I_m = (x^v - 1 : v in m Z^d)`. `I_m` is `H`-invariant, and `H` acts on `F_q[(Z/m)^d]` through
   `SL_d(Z/m)`. So the orbit of `rho` has at most `|SL_d(Z/m)|` points.
3. **Stabilizers.** The stabilizer of a type of level `m` contains the principal congruence subgroup
   `H(m)`. It has finite index and is Kazhdan.

## 2. Matching: the actor acts on types by the genuine action

**Lemma.** Let `M = e_ij(1)` (`i != j`), a nonnegative strict compressor. Then, along `U`,

```text
sup { || sigma_n(M) g sigma_n(M)^* - g o M^(-1) ||_2 : g = sum_rho c_rho z_rho P_n, |c_rho| <= 1 }  ->  0,
```

where `g o M^(-1) = sum_rho c_rho z_(M . rho)`. The same holds for `M^(-1)`, with `sigma_n(M)^*`.

*Proof.*
- Put `Lambda = M Gamma M^(-1)` and `pi~_n(lambda) = sigma_n(M) pi_n(M^(-1) lambda M) sigma_n(M)^*`.
  Item 3 of `vertex-rounding-reduces-ccr-to-commutant-excess` gives partial isometries `v_n` with
  `v_n pi_n(lambda) = pi~_n(lambda) v_n` and `||v_n - 1||_2 -> 0`.
- `sigma_n(M) z_rho sigma_n(M)^*` is the isotypic projection `z~_tau` of `pi~_n|Lambda` for the
  `Lambda`-type `tau = rho o Ad M^(-1)`. An intertwiner maps isotypic projections to isotypic
  projections: `v_n z^Lambda_tau = z~_tau v_n`, where `z^Lambda_tau` belongs to `pi_n|Lambda`.
- For `g~ = sum c z~_tau` and `g_Lambda = sum c z^Lambda_tau`, write
  `g_Lambda - g~ = (1 - v) g_Lambda + g~ (v - 1)`. So `||g~ - g_Lambda||_2 <= 2 ||v_n - 1||_2`.
- **Unit-type collapse.** Item 2 of the rigidity claim gives `pi_n(Gamma) P_n = pi_n(Lambda) P_n`.
  - On `P_n`, the `Lambda`-isotypic projections are the `Gamma`-isotypic ones.
  - The `Gamma`-type restricting to `rho o Ad M^(-1)` on `Lambda` is `M . rho`, by extension through
    `St_r(L)`.
  - `P_n` commutes with `pi_n(Lambda)''`, so the correction costs `2 tau(1 - P_n)^(1/2)`. ∎

**Consequences.**
- *Summed matching.* Random signs give
  `sum_rho ||sigma_n(M) z_rho P_n sigma_n(M)^* - z_(M . rho) P_n||_2^2 -> 0`.
- *Invariance of the type measure.* For a set `S` of types, `tau` is invariant under conjugation and
  `|tau(e) - tau(f)| <= ||e - f||_2`. So `||M_* p_n - p_n||_1 <= 2 sup_S |p_n(S) - p_n(M S)| -> 0`.

## 3. Property (T) on l^2(X)

**Lemma.** Let `(S_H, kappa_H)` be a Kazhdan pair for `H`, with `S_H = {e_ij(+-1)}`. Let `f_n` be
functions on types with `|f_n| <= 1`, `||M_* p_n - p_n||_1 -> 0` and
`||f_n o M^(-1) - f_n||_(L^2(p_n)) -> 0` for `M in S_H`. Let `E_orb` average over `H`-orbits. Then
`||f_n - E^(p_n)_orb f_n||_(L^2(p_n)) -> 0`, where `E^(p_n)_orb` is the `p_n`-conditional
expectation onto orbit functions. Moreover
`sum_O sum_(rho in O) (sqrt(p_n(rho)) - E_orb sqrt(p_n)(rho))^2 -> 0`.

*Proof.* Put `xi = f sqrt(p)` in `l^2(X)` with the quasi-regular unitary representation `lambda`.
1. **Almost invariance.**
   `||lambda(M) xi - xi||_2 <= ||f o M^(-1) - f||_(L^2(M_* p)) + ||sqrt(M_* p) - sqrt(p)||_2`.
   The first term is at most `||f o M^(-1) - f||_(L^2(p)) + 2 ||M_* p - p||_1^(1/2)`. The second is at
   most `||M_* p - p||_1^(1/2)`, since the squared Hellinger distance is bounded by `l^1`.
2. **Kazhdan.** All orbits are finite, so `l^2(X)^H` consists of the orbit-constant vectors and its
   projection is `E_orb`. Kazhdan gives `||xi - E_orb xi||_2 -> 0`, and likewise
   `||sqrt(p) - E_orb sqrt(p)||_2 -> 0`, which is the equidistribution clause.
3. **Division.** Put `zeta = E_orb sqrt(p)` and `eta = E_orb (f sqrt(p))`. Then `|eta| <= zeta`, so
   `g = eta / zeta` (and `0` where `zeta = 0`) is an orbit function with `|g| <= 1`. Moreover
   `||f sqrt(p) - g sqrt(p)||_2 <= ||f sqrt(p) - eta||_2 + ||g (zeta - sqrt(p))||_2 -> 0`.
   The left side is `||f - g||_(L^2(p))`. ∎

## 4. Theorem 5

With the setting of Section 0, along `U`:
1. **Types.** `pi_n`'s types lie in `X` off trace `tau(1 - P_n) -> 0`, and every `H`-orbit in `X` is finite.
2. **Genuine type dynamics.** `Ad sigma(M)` acts on `prod_U Z(A_n) P_n` by the genuine action
   `g -> g o M^(-1)` on types, for every `M in H`. The type measures are asymptotically `H`-invariant.
3. **Equidistribution.** `p_n` is asymptotically uniform on `H`-orbits, in the Hellinger sense of
   Section 3.
4. **The central fixed algebra lifts.** Let `e_O = sum_(rho in O) z_rho`, and add one block
   `1 - sum_O e_O`, of trace `-> 0`. The partition algebras `C_n` have vanishing boundary, and
   `Q cap prod_U Z(A_n) = prod_U C_n`.
5. **Multiplicity-free rounding gives (LM).** Suppose `lim_U tau(sum_(m_rho >= 2) z_rho) = 0`. Then
   `Q = prod_U C_n` is abelian, so it is a liftable masa of itself.

*Proof.*
- 1-3: Sections 1-3, applied with `f = 1` for the equidistribution clause.
- 4, boundary for vertex generators. For a unitary `D`,
  `sum_O ||[D, e_O]||_2^2 = E_eps ||[D, sum eps_O e_O]||_2^2`. With
  `D = sigma_n(s) - pi_n(s)`, this is at most `4 ||sigma_n(s) - pi_n(s)||_2^2 -> 0`.
- 4, boundary for compressors. The orbit-sign unitaries are orbit functions, so the Lemma of
  Section 2 gives `||[sigma_n(M), sum eps_O e_O]||_2 -> 0` uniformly in the signs.
- 4, the containment `prod_U C_n <= Q` follows from the boundary bound and BG1 (part 1).
- 4, the reverse containment. An element `f in Q cap prod_U Z(A_n)` satisfies `alpha_M(f) = f`. By
  Section 2, `f_n o M^(-1) - f_n -> 0` in `L^2(p_n)`, and Section 3 makes `f` an orbit function.
- 5. `Q <= prod_U A_n`, and `||x - x P'_n||_2 <= tau(1 - P'_n)^(1/2)` with
  `P'_n = sum_(m_rho = 1) z_rho P_n`. `A_n P'_n` is abelian, so `Q <= prod_U Z(A_n)`, and item 4
  applies. ∎

## 5. Reading

- **Type cycles are excluded at this pair.** The mechanism of `amenable-type-cycle-kills-liftable-masas`
  needs a type cycle that is almost invariant under the actor but not orbit-constant. Here the actor
  quotient `SL_d(Z)` acts genuinely on types, and property (T) on `l^2(X)` forbids it. The single
  compressor cycles of `compressor-cycles-block-central-projection-rounding` are almost invariant
  only under `E_12(1)`, not under the whole generating set.
- **Where (LM) still lives here.** Theorem 5 lifts `Q cap prod_U Z(A_n)`. What remains is the
  multiplicity fibres.
  - On an orbit `O = H . rho_0` of level `m`, the fixed algebra of `direct_sum_(rho in O) M_(m_rho)` is
    carried by the holonomy of `sigma` on the multiplicity space of `rho_0`.
  - That holonomy is an almost projective representation of the stabilizer `K_O >= H(m)`, a Kazhdan
    congruence-type subgroup.
  - So (LM) for `sigma` is a masa-lifting problem for relative commutants of such almost
    representations. It is a `DEC`-type problem for finite-index subgroups of `SL_d(Z)`, in the sense
    of part 1. This is a reading, not a claim.
  - In bounded multiplicity the holonomy lives in a fixed `U(m)`, and compactness rounds it. That
    extension of item 5 is not written out here.
- **Consistency with part 2.** None of this is consumed by `non-hyperlinear-group`. It completes the
  positive side of the localization face at the Theorem E pair on the center, and it isolates the
  fibre problem as the only place a counterexample to (LM) can sit.

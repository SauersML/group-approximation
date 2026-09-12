# What flexible HS stability of the GHB_2(7) congruence kernel needs

Lane `ghb7-kernel-stability`, 2026-09-12.

Target: `ghb7-congruence-kernel-flexibly-hs-stable`, the single open input of the route
`kazhdan-hyperbolic-b2-stability-via-ghb7-kernel`. By
`kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` it would give a non-hyperlinear,
nonsofic, non-residually-finite hyperbolic group.

Result of this lane: exact invariants of the candidate, and a proof that the
degree-two cohomological existence scheme cannot establish its stability. Stability
itself stays open.

## 1. Exact invariants

`experiments/ghb7-kernel-index/psi_order.py`, run on MSI; output in
`psi_order-output-2026-09-12.txt`.

- **Invariant form.** The generator images `a = I + E_03 + E_12`, `b = I + E_10 − E_23`,
  `c = I + E_31` preserve a nondegenerate alternating form, unique up to scalar.
- **Image.** Schreier–Sims on the 2400 nonzero vectors gives `|ψ(G)| = 276595200`,
  which is `|Sp_4(F_7)|`. So the image is `Sp_4(F_7)`, not `SL_4(F_7)`.
- **Kernel.**
  - `[G:H] = 276595200`;
  - `χ(H) = 159091200`;
  - `b_2(H;Q) = 159091199`;
  - `b_2^(2)(H) = 159091200`, and `b_2^(2)(G_{HB_2}(7)) = 1381/2401`
    (`ghb7-l2-betti-two-is-orbifold-euler-characteristic`).
- **Consistency.** The finite subgroups of `G` have orders dividing `2401`, and
  `1381/2401` has denominator `2401`, as the Atiyah conjecture requires.

## 2. Decision: stability is a degree-two existence statement

Flexible HS stability asks, for every asymptotic representation `σ_n : H → U(d_n)`, for
genuine finite-dimensional representations `π_n` on `C^(D_n) ⊇ C^(d_n)`, with
`D_n/d_n → 1` and `‖σ_n(s) − P π_n(s) P‖_2 → 0`.

**Degree one.** Property (T) gives `H^1(H;π) = 0` for all unitary `π`, with a uniform
modulus. Żuk and Ballmann–Świątkowski derive this from the spectral gaps of the vertex
links of `Y`, and EJZ angles are compiled for `GHB_2(7)`. The links are the coset graphs
of `U_3(7)` (girth 6) and `U_4(7)` (girth 8). Degree-one vanishing controls conjugacy
of nearby genuine representations. That is rigidity: it is how Dogon–Vigdorovich
consume property (T;FD) in `hs-stability-forces-nonhyperlinear-central-extension`. It
does not produce a genuine representation near an asymptotic one.

**Degree two.** Existence runs through the linearized defect. On the relator cells of
`H\Y`, the defect `c = σ(r) − 1`, rescaled into the tracial ultraproduct `M`, is a
2-cocycle for the `Ad`-module `π = L²(M)`. A Newton step needs `δy = c`, so it needs
`H^2(H;π) = 0` with a modulus. The same holds in the De Chiffre–Glebsky–Lubotzky–Thom
iteration, and in `hs-stability-from-bounded-degree-two-primitives`, which also needs
operator-norm control of `y`.

## 3. Degree-two vanishing fails for `H` on both summands

`ghb7-kernel-blocks-degree-two-newton-stability`:

- **Trivial summand.** `C·1 ⊂ L²(M)` is invariant, and `H^2(H;C) ≠ 0` because
  `b_2(H) = 159091199`. This summand is exactly where Dogon–Vigdorovich's
  asymptotically projective representations live. Their theorem turns stability plus
  this class into a non-hyperlinear central extension; it does not remove the class.
- **Regular summand.** If `H` is hyperlinear, take `ρ = σ ⊗ σ` for a separating `σ`.
  - The vectors `w_{g,k} = [σ(g) ⊗ σ(k)]` are orthonormal in `L²(M)`, and `Ad ρ` acts on
    them by diagonal conjugation.
  - `H` is torsion-free and hyperbolic, so noncommuting pairs have free orbits.
  - So `L²(M) ⊖ C ⊇ ℓ²(H) ⊗ ℓ²(N)`, and `H^2(H;ℓ²H) ≠ 0` because `b_2^(2)(H) > 0`.
- **The flat-calibration refutation is a different failure.**
  `flat-calibrations-refute-bounded-degree-two-primitives` shows, for `SL_N(Z)`, that
  operator control of primitives fails; it uses flats. `H` is hyperbolic and has no
  flats. The obstruction here comes earlier: the cocycles need not be coboundaries.

**Scope.** This refutes a method, not stability. The defect cocycles of actual
asymptotic representations could still be coboundaries, and flexibility (enlarging
`D_n`) changes the module.

## 4. What a proof of stability for `H` would have to do

Any of the following, none attempted to completion here:

1. **Avoidance.** Show that relator-defect cocycles of asymptotic representations of `H`
   always lie in the image of a smaller coefficient module where `H^2` vanishes, e.g.
   modules without regular summands. This is plausible only if `H` is not hyperlinear,
   which would already settle the root.
2. **Flexible killing.** Show that every nonzero class in `H^2(H;π)` hit by a defect
   becomes a coboundary after amplification `π ↦ π ⊕ (extra dimensions)`, i.e. vanishing
   of an asymptotic cohomology in the flexible sense. No such vanishing theorem is known
   for any infinite Kazhdan group.
3. **A non-linearized mechanism,** e.g. direct rounding through finite quotients. `H` is
   a congruence-type kernel, and its residual finiteness is unknown. By
   `flexibly-hs-stable-kazhdan-kernel-quotient-rf-or-nonhyperlinear` a flexibly HS-stable
   `H` is residually finite or non-hyperlinear, and by
   `hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class` a hyperlinear
   stable `H` is not good.

## 5. Not done

- No avoidance, flexible-killing or finite-quotient argument was carried out.
- The Lück and Delorme–Guichardet statements used in §3 were not re-read from the
  sources.
- Residual finiteness and hyperlinearity of `H` remain unknown.

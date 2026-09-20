---
rg: 2
id: brieskorn-345-gauge-pair-has-no-eigencorner
kind: claim
title: "A corona representation of the Brieskorn lattice pi_1 Sigma(3,4,5) moving the centre with no commutant eigencorner: left-regular (3,4,5) congruence generators twisted by a gauge field of prescribed flux"
distinct_from:
  torus-knot-k34-expander-pair-has-no-eigencorner: that pair twists by a function D of the centre, X = D^3 alpha and Y = D^4 beta, which cannot satisfy (yx)^5 = x^12 since 35/12 != 3; this pair uses a gauge field with face fluxes (phi, phi, 3 phi) and satisfies the full Brieskorn presentation, for a perfect group with H_1 = H_2 = 0.
  lifted-thompson-t-centre-has-commutant-eigencorners: that asks for eigencorners for T-bar = Lambda / N-hat; this shows they fail for Lambda itself, so any proof of that claim must use N-hat. It does not refute that claim.
  commutant-projection-extraction: that general claim was already refuted; this is a counterexample where the source is perfect, superperfect and a cocompact lattice, the same covering group as T-bar.
  o2-suspension-central-unitary-evades-commutant-corners: that refutation uses a suspension of O_2; this one is a residually finite, Haagerup cocompact lattice built from finite permutation models.
  lifted-thompson-t-is-a-quotient-of-a-brieskorn-lattice: that node supplies Lambda and kills triangle-local arguments for relative (T) by the Haagerup property; this kills triangle-local arguments for eigencorners, by a different invariant (a spectral gap of finite models with prescribed flux).
  matricially-stable-groups-have-central-eigencorners: that proves eigencorners over matricially stable groups; combined with this pair it shows Lambda is not matricially stable (brieskorn-lattice-345-is-not-matricially-stable).
  central-eigencorners-die-over-full-radical-quotients: that assumes an exact eigencorner and forces lambda = 1 under a full-radical hypothesis; this shows, with no hypothesis, that no corner with lambda != 1 exists for this pair.
artifacts:
  - experiments/brieskorn-gauge-eigencorner-2026-09-17/check.py
  - experiments/brieskorn-gauge-eigencorner-2026-09-17/output.txt
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`brieskorn-345-gauge-pair-has-no-eigencorner-proof`.  The imports are
Salehi Golsefidy--Varjú, *Expansion in perfect groups*, Theorem 1, and
Lubotzky's Definition 1.1 and Proposition 1.11 (ii).  Both are quoted
verbatim in the route.  The rest is classical and recalled there: the
Fuchsian (3,4,5) triangle group and the connected algebraic subgroups of
`SL_2(C)`.

## Statement

Put `Λ = <x, y | x^4 = y^3, (yx)^5 = x^12>`, with `c = x^4`, as in
`lifted-thompson-t-is-a-quotient-of-a-brieskorn-lattice`.  Put
`Δ = Λ/<c> = <a, b | a^4, b^3, (ba)^5>`.

- **Finite models.**  There are finite quotients `G_q` of `Δ`, for all
  primes `q >= q_1`, with the following properties.  Let `α, β` be the
  images of `a, b`.
  - `α`, `β` and `βα` have orders exactly `4`, `3` and `5`.
  - `|G_q| = N_q -> infinity`.
  - One `κ > 0` is a Kazhdan constant for every `G_q` with respect to
    `Σ = {α^(±1), β^(±1)}`.
  These are the congruence quotients of the lifted triangle group in
  `SL_2(O_L)`.
- **Gauge unitaries.**  Put `|g|` for the word length in `Σ`,
  `R_q = floor(log_4(N_q) / 2)`, `φ_q(g) = π max(0, 1 - |g|/R_q)` and
  `D_q = diag(e^(i φ_q))` on `l^2(G_q)`.  There are diagonal unitaries
  `M_a`, `M_b` such that `X_q = M_a L(α)` and `Y_q = M_b L(β)` satisfy

  ```text
  ||X_q^4 - D_q|| <= 2π/R_q + ε_q,     ||Y_q^3 - D_q|| <= π/R_q + ε_q,
  ||(Y_q X_q)^5 - D_q^3|| <= 12π/R_q + ε_q,    ε_q = 60π / (47 N_q).
  ```

  Here `L` is the left-regular representation.  `X_q^4`, `Y_q^3` and
  `(Y_q X_q)^5` are exactly diagonal.
- **Corona representation.**  In `Q = prod_q M_(N_q) / (+)_q M_(N_q)` put
  `X = [(X_q)]` and `Y = [(Y_q)]`.  Then `x -> X`, `y -> Y` is a
  homomorphism `Θ : Λ -> U(Q)` with

  ```text
  Θ(c) = u := [(D_q)],     ||u - 1|| = 2,     sp(u) = {e^(iθ) : 0 <= θ <= π}.
  ```

- **No eigencorner.**  There is no nonzero projection
  `P in Θ(Λ)' ∩ Q = {X, Y}' ∩ Q` with `u P = λ P` for any `λ != 1`.  More
  strongly, suppose `P` is a nonzero projection with
  `||[P, X]||, ||[P, Y]|| <= η` and `||(u - λ) P|| <= ε`.  Then

  ```text
  |λ - 1| <= ε + 2 sqrt(2) η / κ.
  ```

## What this changes

1. **The Brieskorn cover does not have central eigencorners.**  Statement
   (EC) of `lifted-thompson-t-centre-has-commutant-eigencorners` is false
   with `T̄` replaced by `Λ` and `z` by `c`.  This holds although `Λ` is
   perfect and torsion-free, with `H_1(Λ) = H_2(Λ) = 0` (a homology
   sphere).
   - These are exactly the properties that killed the `K(3,4)` twist.  That
     twist uses a function `D` of the centre, `X = D^3 α` and `Y = D^4 β`.
   - Any twist `X = D^s α`, `Y = D^t β` of that kind has
     `X^4 ~ D^(4s)`, `Y^3 ~ D^(3t)` and `(YX)^5 ~ D^(5(s+t))`.  The
     Brieskorn relation then needs `5(s+t) = 3m` with `m = 4s = 3t`, that is
     `35m/12 = 36m/12`.  So `m = 0`, and the twist is trivial.
   - The gauge field removes this obstruction.  Its fluxes are not the
     powers of one diagonal unitary, and they are balanced over the whole
     finite Cayley complex, not face by face.
2. **Class killed: eigencorner arguments that use only relations of `Λ`.**
   Every corona representation of `T̄` is one of `Λ`, through
   `q : Λ -> T̄`.  So an argument for (EC) on `T̄` that uses only relations
   holding in `Λ` would prove (EC) for `Θ`.  This covers:
   - `α̃^4 = β̃^3 = z` and `(β̃α̃)^5 = z^3`;
   - the torsion and rotation-number data;
   - the cocompact lattice `Λ ≤ G̃`, the Seifert structure and the Haagerup
     property;
   - perfectness and `H_2 = 0`.

   Such an argument is false.
   - *Named invariant:* a gauge field with prescribed flux
     `(φ, φ, 3φ)` on the 4-, 3- and 10-gon faces of the finite Cayley
     complexes of `Δ`, together with a uniform Kazhdan constant of those
     complexes.
   - *Death step:* the modulus vector `s_h = ||P e_h||` of any almost
     commuting projection is almost invariant under `L(α)` and `L(β)`.  The
     spectral gap flattens it, and then `P` sees `u` only through
     `τ(|u - 1|^2) <= 4 N^(-1/2)`.

   So any proof of `lifted-thompson-t-centre-has-commutant-eigencorners`
   must use the kernel `N̂`, that is, the commutator relators of `T` that are
   not in `Δ`.  This strengthens the `K(3,4)` kill of
   `torus-knot-k34-expander-pair-has-no-eigencorner`, item 4.  That kill
   left open whether the extra relation `(yx)^5 = x^12` of the Brieskorn
   cover restores eigencorners.  It does not.
3. **`Λ` is not matricially stable.**  This is
   `brieskorn-lattice-345-is-not-matricially-stable`, obtained through
   `matricially-stable-groups-have-central-eigencorners`.
4. **Where the construction stops for `T̄`.**  The models do not descend.
   - The Thompson relator `r_1 = [βαβ, α^2 βαβ α^2]` is non-trivial in
     `G_q`.  The script checks this for `p = 31, 41, 71, 79` in both word
     conventions.  So `r_1 != 1` in `Δ`, and hence in `G_q` for all large
     `q`.
   - Then `W_(r_1)(X_q, Y_q)` is a phase-weighted permutation matrix with
     zero diagonal, so `||W_(r_1)(X_q, Y_q) - 1|| >= 1`.
   - More generally, `T` is infinite and simple, so it has no non-trivial
     finite quotient.  Hence no permutation model of `Δ` with a spectral gap
     kills `N`.
   - The mechanism needs finite permutation models of `Λ/<c>` with a
     uniform gap.  `T̄/<z> = T` has none, and `T̄` has no finite quotients.
     This is the precise gate between `Λ` and `T̄`.

## Scope

- Both `X_q^4 ≈ Y_q^3` and `(Y_q X_q)^5 ≈ X_q^12` hold only
  asymptotically, at rate `O(1/R_q) = O(1/log N_q)`.  The numerics in
  `experiments/brieskorn-gauge-eigencorner-2026-09-17/` confirm the
  following for `PSL_2(F_p)`, `p = 31, 41, 71, 79`:
  - `dim ker F^T = 1`;
  - the gauge system is exactly solvable;
  - all the defect bounds hold;
  - the Kazhdan constant is at least `0.31`.

  They cannot show `||(YX)^5 - X^12||` small.  Its bound `18π/R` drops
  below `2` only for `R > 9π`, which is beyond the diameters (at most `19`)
  of the groups computed.
- It is not claimed that `Λ` is not MF, or anything about `T̄`.

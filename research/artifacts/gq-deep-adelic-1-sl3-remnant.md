# The SL_3(Z) remnant: first candidate host (lane gq-deep-adelic-1, 2026-09-18)

## 1. The target

The remnant of `gq-deep-adelic-1-uhf-class-verdict.md` is crossed-product rings of `Γ = SL_3(Z)` over its
congruence odometer `K = SL_3(Ẑ)`, or a Toeplitz extension of it, and their finitely generated subrings.

The coordinator asked four questions:
- (a) can a finitely generated subring contain `Q`?
- (b) is it simple?
- (c) R1, the non-divisible letter-cylinder corners;
- (d) R2, the torsion index units.

The instruction was to kill the class or produce the first candidate passing both K-budget clauses.

## 2. Answers

| Question | Answer | Node |
|---|---|---|
| (a) `Q` in a finitely generated subring | **yes**, on the odometer itself and on every extension of it: one harmonic function plus translation units, with no clopen sets needed. `E_(d-1) - S E_d = 1/D_M` over the coset representatives of `Γ/Γ_M`, and `M! \| D_M` | `harmonic-elimination-puts-q-in-odometer-crossed-products` |
| (b) simplicity | **yes** for the Toeplitz model `R_T`, whose letter cylinders give `LC(X, Z)`; centre `Q`. Open for the pure odometer ring `R_K` | `sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational` |
| (K1) | **yes**: the Toeplitz subshift of Cecchi Bernales–Cortez–Gómez (arXiv:2305.09835, Thm 1.3) carries a measure conjugate to Haar, which gives a II_1 factor and Fuglede–Kadison | same |
| `K_2(Q)` at the unit | **dies**, since `R_T ≅ M_([Γ:Γ(d)])(...)` for every `d` | same, with `matricial-divisibility-kills-rational-k2-symbols` |
| (d) R2, torsion index units | **settled for block units and group units.** The transfer `Γ(d)^ab -> Γ(d^2)^ab` vanishes (Lee–Szczarba plus a computation), so block units have sign classes and trivial rational symbols | `sl3-congruence-transfer-kills-abelianization`; part 6 of the ring node |
| (c) R1, letter cylinders | **open** | `sl3-toeplitz-harmonic-ring-meets-the-uhf-k-budget` |
| R2, general units | **open** | same |

So the class is not killed. `R_T` is the first finitely generated simple ring containing `Q` with `Q^x`
detected in `K_1` (kernel `⊆ {±1}`), `K_2(Q)` killed, no Laurent-type unit on any block, and trivial
rational symbols on all group units and block units. It is not yet known to pass the full K-budget,
and nothing about the finite presentation or simplicity of `PE_N(R_T)` is known.

## 3. Why the harmonic elimination works

At each point `x`, the `d = [Γ : Γ_M]` translates `f(γx)`, `γ ∈ T_M`, visit every level-`M` ball of the
odometer exactly once. So the multiset of values is fixed, with one exception: the ball of `x_∞`
contributes one "wild" value `t ∈ {1/(j+1) : j >= M} ∪ {0}`. The symmetric functions of the translates
are therefore affine in `t`:

    E_d = t/D_M,   E_(d-1) = 1/D_M + t S_M/D_M,

and `t` cancels. The same trick needs no idempotents, which matters for the next section.

## 4. The pure odometer ring R_K: why simplicity is hard there

In `R_K = ⟨u_s^(±1), f⟩` over `K`, every coefficient is a polynomial in finitely many translates of `f`.
Near each of their finitely many centres it is a polynomial in one harmonic function.

- **Idempotents are locally constant.** A polynomial that takes only the values `0, 1` on a sequence
  accumulating at `0` is constant on a tail. So every idempotent of the coefficient ring is locally
  constant.
- **Ball indicators seem out of reach.** Separating a ball needs `1/(t - b)`-type functions, which are
  not polynomials in `t`.
- **Consequences.** The compression proof of simplicity, and the matrix units behind divisibility of
  `[1]`, both need ball indicators. So for `R_K`, simplicity and divisibility of `[1]` are open.

The Toeplitz model supplies the indicators through expansivity. The price is R1, since letter cylinders
are not saturated.

## 5. The transfer computation (d)

For `x = I + dX ∈ Γ(d)`, the transfer to `Γ(d^2)` is `(d^N/f) W + d[W, S] mod d^2`, where:
- `N = 8`;
- `x^f = I + d^2 W`;
- `S` is the sum of the coset representatives.

The first term vanishes because `d^N/f` is divisible by `d^2`. The second vanishes because the sum of
all elements of the quotient group `sl_3(Z/d)/⟨X⟩` is `0`: its 2-torsion has rank at least `7`. So `S` is
a multiple of `X` modulo `d`, and `[W, X] = 0`.

Consequence: `H_1(SL_3(Z); C(SL_3(Ẑ), Z)) = 0`. This is Matui-type homology of the congruence odometer
groupoid. It is the opposite of the Z-odometer (Bunce–Deddens), whose `H_1` is `Z`: that `Z` is exactly the
Laurent unit.

## 6. What the next lane should do

1. **R1.** Decide equidecomposability (comparison) of clopen sets in `Γ ⋉ X` for the Cecchi
   Bernales–Cortez–Gómez Toeplitz subshift. Alternatively, find a Toeplitz construction whose letter
   cylinders have divisible `K_0` classes, e.g. with the irregular part confined to one orbit and an
   explicit `K_0` computation.
2. **R2.** Compute `H_1(Γ; C(X, Z))` for the Toeplitz extension. If the non-odometer part is torsion,
   check whether it dies under transfer the way the odometer part does.
3. **The pure odometer ring.** Decide whether `R_K` is simple. If it is, R1 at clopens is automatic
   there.
4. **Beyond the budget.**
   - Finite presentation of `E_N(R_T)` needs a finitely presented ring and finite normal generation
     of the Steinberg kernel.
   - Simplicity of `PE_N(R_T)` needs a normal subgroup theorem for `E_N` over `R_T`.

## 7. Trust surfaces

- **T2:** Fuglede–Kadison from a secondary source.
- **T3:** Loday's product formula, not re-read.
- **Secondary quotations:**
  - Lee–Szczarba, through Imoto–Kobayashi arXiv:2212.13181v2, Theorem 1.1, HTML;
  - Cecchi Bernales–Cortez–Gómez, Theorem 1.3, HTML.

All nodes of this round are lane proofs, not refereed.

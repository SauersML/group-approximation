---
rg: 2
id: rational-iwahori-group-is-union-of-fp-self-similar-groups-proof
kind: route
title: The section matrix of an Iwahori matrix keeps its entries in Z[1/m], and the Iwahori factorization over the local ring Z_(p) gives the generators
target: rational-iwahori-group-is-union-of-fp-self-similar-groups
requires:
  - pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori
  - rover-nekrashevych-finite-presentation-criteria
---

Notation as in the target. `Z[1/m] ⊆ Z_(p)` because `p ∤ m`.

**Item 1.**
- *`Γ_p(m) <= Γ_p`.* For `M = [[α,β],[c,δ]] ∈ I_p(m)`, the determinant is a unit
  of `Z[1/m]`, hence of `Z_(p)`. So `M` is an Iwahori matrix over `Z_(p)`, and
  `M ∈ Γ_p` by item 2 of `pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori`.
- *The section matrix.* Let `M` map the cone `a + p^kZ_p` onto `b + p^kZ_p`. As
  in item 1 of that node, the section is
  `[[p^k,b],[0,1]]^{-1} M [[p^k,a],[0,1]] = [[α - bc, N/p^k],[c p^k, ca + δ]]`,
  where `N = αa + β - b(ca + δ)`. Its determinant is `det M`.
- *Entries.* The entries `α - bc`, `c p^k ∈ pZ[1/m]` and `ca + δ` lie in
  `Z[1/m]`. Also `M(a) ≡ b (mod p^k)` in `Z_p`, and `ca + δ` is a `p`-adic unit.
  So `N ∈ p^kZ_p ∩ Z[1/m] = p^kZ[1/m]`, and `N/p^k ∈ Z[1/m]`. Hence the section
  lies in `I_p(m)`.

**Item 2.**
- Reduction mod `p` is a ring map `Z[1/m] -> F_p`, since `p ∤ m`. `I_p(m)` is the
  preimage of the upper triangular Borel subgroup of `GL_2(F_p)`, so it has finite
  index in `GL_2(Z[1/m])`.
- The kernel of `GL_2(Z[1/m]) -> PGL_2(Q)` is the scalar group `Z[1/m]^×`, which
  is finitely generated and central.
- `GL_2(Z[1/m])` is finitely presented (Borel–Serre, as imported). A quotient of
  a finitely presented group by a finitely generated normal subgroup, and a
  finite-index subgroup of a finitely presented group, are finitely presented.
  So `PGL_2(Z[1/m])` and `Γ_p(m)` are finitely presented.

**Item 3.** `[[1,0],[p,1]] ∈ I_p(1)`, and `I_p(1) ⊆ I_p(m)`.

**Item 4.**
- `m | m'` gives `Z[1/m] ⊆ Z[1/m']` and `I_p(m) ⊆ I_p(m')`.
- Let `γ ∈ Γ_p`. It is represented by an Iwahori matrix `M` over `Z_(p)`. Let `m`
  be the product of the primes dividing the denominators of the entries of `M`
  and the numerator of `det M`. All of these are prime to `p`, since
  `det M ∈ Z_(p)^×`. Then `M ∈ I_p(m)`.

**Item 5.** Let `M = [[α,β],[c,δ]]` be an Iwahori matrix over `Z_(p)`. Then `δ`
is a unit, and
`M = [[1,β/δ],[0,1]] · diag(det M/δ, δ) · [[1,0],[c/δ,1]]`
(multiply out: the top left entry is `det M/δ + βc/δ = α`). As Möbius maps this
is `γ = τ_x ∘ d_u ∘ λ_y`, with `x = β/δ ∈ Z_(p)`, `u = det M/δ^2 ∈ Z_(p)^×` and
`λ_y(z) = z/(yz+1)`, where `y = c/δ ∈ pZ_(p)`.

For an integer `D` prime to `p`, write `d_D` for the product of the `d_q` over
the prime factors `q` of `D`, with multiplicity. Then:
- `τ_{n/D} = d_D^{-1} τ_1^n d_D`, and `τ_1 ∈ Γ_p(1)`;
- `u = ±∏ q^{e_q}` over primes `q ≠ p`, and `d_{-1} = [diag(-1,1)] ∈ Γ_p(1)`;
- `λ_{pn/D} = d_D λ_{pn} d_D^{-1}`, since
  `d_D(λ_{pn}(z/D)) = z/(pnz/D + 1)`, and `λ_{pn} = [[1,0],[pn,1]] ∈ Γ_p(1)`.

So `Γ_p <= ⟨Γ_p(1), d_q⟩`. Conversely, `d_q = [diag(q,1)] ∈ Γ_p` and
`Γ_p(1) <= Γ_p`. `Aff_1(Z_(p))` contains every `d_q`, and it lies in `Γ_p`: an
affine map `z ↦ uz + x` is the Iwahori matrix `[[u,x],[0,1]]`.

`Γ_p(1)` is the image of `I_p(1)`, the preimage of the Borel subgroup of
`GL_2(F_p)` in `GL_2(Z)`, which has index `|P^1(F_p)| = p+1`. `PGL_2(Z)` is
virtually free, so `Γ_p(1)` is virtually free and finitely presented.

**Item 6.**
- Let `g ∈ PGL_2(Z[1/(pm)])`. Item 3 of the Möbius node writes `g` piecewise as
  `(chart) ∘ γ ∘ (chart)^{-1}`, with normalized local maps
  `γ = φ_{b,k'}^{-1} ∘ φ_t^{-1} ∘ g ∘ φ_s ∘ φ_{a,k}`.
- All charts are represented by matrices over `Z[1/p]` whose determinants are
  powers of `p` up to sign. So `γ` is represented by a matrix `M` over
  `Z[1/(pm)]` with `det M ∈ ±(pm)^Z`.
- Scale `M` by a power of `p` so that it is primitive at `p`. Since `γ ∈ Γ_p`,
  the scaled matrix is a `Z_(p)`-unit multiple of an Iwahori matrix over `Z_(p)`,
  so it is itself Iwahori over `Z_(p)`. Its entries then lie in
  `Z_(p) ∩ Z[1/(pm)] = Z[1/m]`, its lower left entry in `pZ[1/m]`, and its
  determinant in `Z_(p)^× ∩ ±(pm)^Z = ±m^Z`.
- So `γ ∈ Γ_p(m)`. The two-chart construction and `Θ` of that proof then embed
  `PGL_2(Z[1/(pm)])` in `V_p(Γ_p(m))`.
- By items 1 and 2, `Γ_p(m)` is a finitely presented self-similar group, so
  `V_p(Γ_p(m))` is finitely presented by (FP1, Scott).

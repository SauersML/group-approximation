---
rg: 2
id: sl2-root-triangle-2dim-iff-zero-frobenius-holonomy-proof
kind: route
title: Necessity from the spectrum transport in dimension 2; sufficiency by Frobenius-twisted conjugations whose scalars absorb the twist constants
target: sl2-root-triangle-2dim-iff-zero-frobenius-holonomy
requires: [sl2-root-triangle-char2-frobenius-spectrum-transport, triangle-of-groups-half-girth-structure, kazhdan-hyperbolic-sl2-root-triangles]
---

Notation as in the target. `d_t = diag(t, t^{-1})`, `w = [[0,1],[1,0]]`, and characteristic 2 throughout the
sufficiency part.

**2 ⇒ 1.** Compose with `SL_2(q^2) = SL_2(F) ⊂ GL_2(F)`.

**1 ⇒ 3.** Let `ρ: Λ -> GL_2(K)` be nontrivial.
- By `sl2-root-triangle-char2-frobenius-spectrum-transport` (0), `char K = 2`, because `q - 1 >= 7 > 2`.
- Enlarge `K` to contain `F`.
- By its corollary for dimension 2, `|S_1| = 1`, so the group `H` of (d) is `0`:
  - every `supp(ψ_e)` is a singleton, so every `ψ_e`, and hence every `φ_e = ψ_e^{-1}`, is semilinear;
  - `H = <hol> = 0`, so `hol = 0`.

**3 ⇒ 2.** Assume `φ_e(x) = λ_e x^{2^{a_e}}` and `a_12 + a_23 = a_13` in `Z/f`.

*Reduction to the standard parametrizations.* In `Λ`, `p_i^e(α_i^e(x)) = p_j^e(α_j^e(x))`. With `y = α_i^e(x)`,
maps `ρ_i: A_i -> SL_2(F)` define a homomorphism of `Λ` iff for each edge `e = (i,j)` and all `y ∈ k`:

```text
(E_e)    ρ_i(p_i^e(y)) = ρ_j(p_j^e(φ_e(y))).
```

*Three identities* (all in `SL_2(F)`):
- **(I1)** `h v(x) h^{-1} = u(x)` for `h = [[P,1],[1,0]]`, because `h^{-1} = [[0,1],[1,P]]` and
  `[[P+x,1],[1,0]]·[[0,1],[1,P]] = [[1,x],[0,1]]`.
- **(I2)** `[[α,0],[γ,δ]] v(y) [[α,0],[γ,δ]]^{-1} = v(δy/α)`.
- **(I3)** `d_τ u(y) d_τ^{-1} = u(τ^2 y)` and `d_τ v(y) d_τ^{-1} = v(τ^{-2} y)`.

*The configuration.* Put `Frob^b(M)` for entrywise `2^b`-th powers. It is an automorphism of `SL_2(F)` and
restricts to one of `SL_2(k)`, where `b` matters mod `f`. Use the constants of the target:
- `b_1 = a_13`, `b_2 = a_23`, `b_3 = 0`;
- `μ_12 = λ_12^{2^{a_23}}`, `μ_13 = λ_13`, `μ_23 = s λ_23`, `ν = μ_13 μ_23`;
- `τ^2 = 1/μ_13`, `ω^2 = 1/μ_12`, `P^2 = μ_12/ν`.

All square roots exist in `F`, and all constants are nonzero. Put `ρ_i = conj_{g_i} ∘ Frob^{b_i}` with
`g_1 = h`, `g_2 = h u(1/P) d_ω`, `g_3 = d_τ`. Each `ρ_i` is injective.

- **Edge 13** (`p_1 = v`, `p_3 = u`).
  - Left side, by (I1): `ρ_1(v(y)) = h v(y^{2^{a_13}}) h^{-1} = u(y^{2^{a_13}})`.
  - Right side, by (I3): `ρ_3(u(λ_13 y^{2^{a_13}})) = d_τ u(λ_13 y^{2^{a_13}}) d_τ^{-1} = u(τ^2 λ_13 y^{2^{a_13}}) = u(y^{2^{a_13}})`.
- **Edge 23** (`p_2 = v`, `p_3 = v(s·)`).
  - Left side: `h u(1/P) = [[P, 0],[1, 1/P]]`, so `g_2 = [[Pω, 0],[ω, (Pω)^{-1}]]` is lower triangular.
    By (I2), `ρ_2(v(y)) = v(y^{2^{a_23}}/(P^2 ω^2)) = v(μ_12 y^{2^{a_23}} / P^2) = v(ν y^{2^{a_23}})`.
  - Right side, by (I3): `ρ_3(v(s λ_23 y^{2^{a_23}})) = v(τ^{-2} s λ_23 y^{2^{a_23}}) = v(μ_13 μ_23 y^{2^{a_23}}) = v(ν y^{2^{a_23}})`.
- **Edge 12** (`p_1 = p_2 = u`).
  - Left side: `ρ_1(u(y)) = h u(y^{2^{a_13}}) h^{-1}`.
  - Right side:

```text
ρ_2(u(λ_12 y^{2^{a_12}})) = h u(1/P) d_ω u(λ_12^{2^{a_23}} y^{2^{a_12 + a_23}}) d_ω^{-1} u(1/P)^{-1} h^{-1}
                         = h u(1/P) u(ω^2 μ_12 y^{2^{a_13}}) u(1/P)^{-1} h^{-1}
                         = h u(y^{2^{a_13}}) h^{-1}.
```

    The first line uses `a_12 + a_23 = a_13` mod `f` and `y^{2^f} = y`, the second uses (I3), and the third
    uses `ω^2 μ_12 = 1` and that the `u(·)` commute.

So the `ρ_i` define `ρ: Λ -> SL_2(F)`.
- It is injective on every vertex group.
- It is onto, since `ρ_3(A_3) = d_τ SL_2(F) d_τ^{-1} = SL_2(F)`.
- `Λ` is a triangle of groups with `1/r_1 + 1/r_2 + 1/r_3 < 1` (`kazhdan-hyperbolic-sl2-root-triangles`).
  So `triangle-of-groups-half-girth-structure` (iv) applies to the finite target `SL_2(q^2)`, and `ker ρ` is
  torsion-free. It has index `|SL_2(q^2)|`.

**Machine check of the configuration.** `experiments/sl2-root-triangle-frobenius-holonomy-2026-09-16/holonomy.py`,
part (A), evaluates `(E_e)` on every `x ∈ k` for every edge, with random `α_i^e ∈ GL_f(F_2)`. The results are
80/80 for `q = 8` and 40/40 for `q = 16`.

**Counts.** A semilinear triple is a choice of `(λ_e, a_e)` in `k^* × Z/f` for each edge, `f^3 (q-1)^3` in all,
and `hol = 0` fixes `a_13`, leaving `f^2 (q-1)^3`.

∎

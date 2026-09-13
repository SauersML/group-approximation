---
rg: 2
id: radu-metabelian-quotient-is-not-sofic
kind: claim
title: The metabelian quotient Gamma_R/[Lambda_v, Lambda_v] of Radu's BMW lattice is not sofic
distinct_from:
  radu-nilpotent-by-arithmetic-quotients-are-sofic: that asserts soficity of every Gamma_R/gamma_k(Lambda_v); this asserts nonsoficity of the case k = 2, which would refute it
  radu-bmw-lattice-nonsofic: that is nonsoficity of the lattice itself; this is nonsoficity of a quotient, and neither statement implies the other
  kun-thom-nonsofic-wreath: that gives a nonsofic abelian-by-residually-finite group through Kazhdan pairs; this would give one whose quotient has the Haagerup property and whose relevant subgroup is free
---

**OPEN.** Let `Γ_R` be Radu's BMW lattice, `Λ_v` its free horizontal kernel and
`Q = Γ_R/Λ_v` the cocompact arithmetic lattice in `PGL_2(Q_2) × PGL_2(Q_2)`
(`radu-horizontal-quotient-is-arithmetic-lattice`). The claim is that

```text
G_2 = Γ_R/[Λ_v, Λ_v],        1 → H_1(Y) → G_2 → Q → 1,
```

is not sofic. Here `Y = T_v/Λ_v` is the Cayley graph of `PGL_2(Z)` on `x, y, z`, so the kernel is
the relation module of `PGL_2(Z)`. The mark `δ^4 = (xz)^4` is twice the class of the square
`ℓ = [(xz)^2]` in `H_1(Y)`. It is nonzero in `G_2` and killed in every finite quotient
(`radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups`, item 4).

**What it would give.** A nonsofic extension of a free abelian group by a lattice in a product of
trees, with no property (T) anywhere: `Q` acts properly on `T_h × T'`, and the subgroup
`C = <a,b,c> ≅ C_2 * C_2 * C_2` carrying the parity is a-T-menable. So this is a second
nonsoficity mechanism.

**Framing correction.** The negative horn of `radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups`
(item 3) says a nonsofic `G_k` would refute amenable-by-sofic permanence, "open even for finite
cyclic kernels". The general form is already refuted: Kun–Thom Theorems A and E
(`kun-thom-nonsofic-wreath`) give `(Z/2)^(G/Γ) ⋊ G` nonsofic with `G` residually finite. What
Arzhantseva–Berlai–Finn-Sell–Glebsky record as open is the special case of finite kernels. The
payoff of this claim is the mechanism, not a first counterexample.

## Attempts

* **Expansion of the horizontal slices (this lane's assignment).**
  - *Input.* `C` has finite index in the stabilizer in `Q` of a vertex of the second tree `T'`,
    a `{𝔮}`-arithmetic lattice in `PGL_2(F_𝔮)`. Its congruence Schreier graphs have a uniform
    spectral gap (property τ; recalled, Clozel's τ theorem, not re-read). Exact congruence models
    of `Γ_R` therefore have expanding `C`-slices, which is where the parity argument of
    `radu-nilpotent-by-arithmetic-quotients-are-sofic` gets rigidity.
  - *Where it dies.* τ is a statement about exact finite actions. `C ≅ C_2^(*3)` is a-T-menable,
    so almost invariant vectors of almost actions need not be close to invariant ones. A sofic
    model has no obligation to make its `C`-slices expand: every 3-edge-coloured graph of large
    girth, including ones with a sparse cut, is a Schreier graph of `C`. Transporting τ to sofic
    models needs Hamming correction of almost actions of `Q` to genuine ones, i.e. flexible
    permutation stability of `Q`. That is the input of the template theorem
    `hnn-over-sl2-z-not-sofic-if-sl2-z-inverse-p-p-stable`, and it is open for `Q`.
  - *A second gap.* `Q` is a quotient of `G_2`, not a visible subgroup, so almost actions of
    `G_2` do not restrict to almost actions of `Q`. A stability argument has to run on a host
    containing `Q`, and nonsoficity of a host does not descend to `G_2`.
* **Parity strips in lifted models: dead as a direct argument.** In a model of `G_2`, put
  `σ = φ(δ^2)`. On points where the strips of squares are present, `σ` commutes with `a, b`, and
  `c` conjugates it to `σ^(−1)`. Let `w ∈ C` be a horizontal cycle through `p` with an odd number
  of `c`'s. Then `w·σp = σ^(−1)p`: `w` reflects the `σ`-orbit of `p`, and nothing forces `σ^2p = p`.
  The congruence argument `2[ℓ_p] = 0` used that `ℓ_p` closes in the base complex
  `N\(T_h × Y)`. In a lifted model the horizontal cycle lifts to a path ending at a lamp translate
  of its start, and the two lifts of `w`, at `p` and at `σp`, differ by exactly `2ℓ`. No
  contradiction.

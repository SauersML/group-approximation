---
rg: 2
id: full-shift-topological-full-group-is-residually-finite-proof
kind: route
title: Elements of the full-shift topological full group permute every finite shift orbit, and periodic points are dense
target: full-shift-topological-full-group-is-residually-finite
requires:
  - restricted-burnside-finiteness
---

Notation as in the target.

**Step 1: each element permutes each shift orbit.** For `g ∈ [[σ]]` and `x ∈ X`, `g(x) = σ^(k_g(x))(x)`
lies in the `σ`-orbit of `x`. The inverse `g^(-1)` is also in `[[σ]]` (on the clopen set
`g({k_g = k})` it is `σ^(-k)`), so it too maps each orbit into itself. Hence `g` restricts to a
bijection of every `σ`-orbit, in particular of every finite one. Restriction is compatible with
composition, so `ρ` is a homomorphism.

**Step 2: periodic points are dense.** A basic open set is a cylinder
`[w]_i = {x : x_i … x_(i+m−1) = w}`. Choose `p >= m` and a word `u` of length `p` whose letters at
positions `i, …, i+m−1` (read modulo `p`) spell `w`. The configuration `x` with `x_j = u_(j mod p)`
is `σ^p`-fixed and lies in `[w]_i`.

**Step 3: injectivity.** If `ρ(g) = 1`, then `g` fixes every periodic point. The fixed set of the
continuous map `g` is closed and contains a dense set, so it is all of `X`, and `g = 1`.

**Step 4: residual finiteness.** A subgroup of a direct product of finite groups is residually finite:
for `g ≠ 1` some coordinate projection, a homomorphism to a finite symmetric group, does not kill `g`.

**Step 5: finite exponent.** A finitely generated residually finite group of finite exponent is
finite by Zelmanov's theorem (`restricted-burnside-finiteness`). Subgroups of residually finite groups
are residually finite, so item 2 follows.

**Step 6: the 2V consequence.** Item 3 of the target is item 2 applied to the conjugates of the copy
of `[[σ]]` in `2V`: a conjugate of a residually finite subgroup is residually finite. An element of
`2V` that maps every `σ`-periodic configuration to a `σ`-periodic configuration in the same orbit, by
a locally constant power of `σ`, is an element of that copy; any element outside it either leaves the
set of periodic configurations or moves some configuration off its own orbit, which in the two-stack
picture means rewriting a window or changing its length.

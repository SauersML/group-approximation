---
rg: 2
id: port-generated-square-completions-force-coset-support-proof
kind: route
title: Synchronous self-pairs force the quadrangle criterion, and cross pairs close their support under the generated subgroup
target: port-generated-square-completions-force-coset-support
requires: []
artifacts:
  - research/artifacts/ex-kac-quantum-compiler-latin-completions-2026-09-13.md
---

The complete proof is §2 of the artifact.

**(L1): the rows form a group.**  Within a block both questions decode one
PVM.
- The neighbourhood of the question pair `(x,x')` is the graph of
  `L_(x') L_x^(-1)` (full support).  The rule accepts only equal decoded
  answers.
- Given `x, x', y_0`, pick `z` with `L_z(y_0) = L_(x') L_x^(-1)(y_0)`.  The
  graphs of `L_z` and `L_(x') L_x^(-1)` meet, so `(p_q, z)` shares the
  component.
- Acceptance at `(p_q,z)` forces `L_z = L_(x') L_x^(-1)`.
- So the row set contains `id` and is closed under `(x,x') |-> L_(x')L_x^(-1)`,
  hence it is a group.  It is regular by sharp transitivity.
- Conversely, graphs of distinct elements of a regular group are disjoint,
  and each decodes to equal answers.

**(L2): cross pairs.**  Identify `O_q x O_(q')` with `K_q x K_(q')` through
`s_0`, and put `Σ = {g : g s_0 in S}`.
- The question pair `g` has neighbourhood `g Σ`.
- The answer side of the port pair's component is `<Σ> s_0`.
  - `⊆`: by induction on the component.
  - `⊇`: words in `Σ` propagate, since `w Σ ∋ w`.
- Acceptance at the port pair is `<Σ> s_0 subseteq W`.
- At any `g in <Σ>` it is the same condition, and components of other `g` are
  translates.

**Oracularized consequence.**  Take a functional support `graph(π_i)`
between a context and a variable.
- The regular action of `M` on the graph gives `|M| = |O_c|`.
- An element `(e,k)` fixes the graph only if `k = e`.  So
  `M = {(k, φ_i(k))}` with `φ_i` a homomorphism.
- Hence the context support is the orbit of a point under the subgroup
  `{(φ_i(k))_i}`.

**Sharpness example.**  `S_3` on points ⊔ 2-subsets, coloured by orbitals.
- `Aut = S_3`.
- The uniform measure gives a closure-safe classical trace.
- The support of `(0,{0,1})` is the incidence relation.  It contains
  `(0,{0,1})`, `(1,{0,1})` and `(0,{0,2})` but not `(1,{0,2})`, so it is not
  rectangular.
- Cosets in product groups are rectangular, through `(a',b)(a,b)^(-1)(a,b')`.

**Credit.**  The translation case with exact colour equality is
`harris-circulant-one-matrix-compiler-forces-affine-support`.  The step
"synchronous self-pairs make a Latin square a group" is the classical
quadrangle criterion for Cayley tables, here derived from closure-safety.

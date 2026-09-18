---
rg: 2
id: injective-plane-lift-codings-force-finite-type-proof
kind: route
title: The injective coding is a conjugacy onto T x Y, T recodes as a Z^2-subshift, finite type passes to the literal product, and the slice at Λ_0 x {0} makes Y finite type
target: injective-plane-lift-codings-force-finite-type
requires: []
---

**Route. COMPLETE.** Self-contained hand proof. Conventions: `Λ` acts on
`A^Λ` by `(g·x)(h) = x(hg)`, and similarly for `Λ_0` and `Z^2`. The only
outside fact is Curtis--Hedlund--Lyndon (continuous equivariant maps between
subshifts over a countable group are sliding block codes), which holds over
every countable group by the usual uniform-continuity argument.

**Step 1: `π = (τ,Φ)` is a conjugacy `X -> T x Y`.**
- Let `Λ` act on `T x Y` by `(λ,z)·(t,y) = (z·t, λ·y)`. Then `π` is
  continuous and equivariant, by the hypotheses on `τ` and `Φ`.
- `T = τ(X)` is a minimal `Z^2`-system and `Y = Φ(X)` a minimal
  `Λ_0`-system, being factors of the minimal `X` (with `Λ_0`, respectively
  `Z^2`, acting trivially on them).
- `T x Y` is minimal for `Λ`: the orbit of `(t,y)` is
  `(Z^2·t) x (Λ_0·y)`, a product of dense sets.
- `π(X)` is compact, nonempty and invariant, so it is all of `T x Y`.
- A continuous bijection from a compact space onto a Hausdorff space is a
  homeomorphism. So `π` is a conjugacy.

**Step 2: `T` is conjugate to a `Z^2`-subshift `T' ⊆ C^{Z^2}`.**
- *`T` is zero-dimensional.* `T ≅ T x {y_0}` is a closed subspace of
  `T x Y ≅ X`, and `X` is a closed subset of a Cantor set.
- *`T` is expansive.* Let `c > 0` be an expansive constant of `X`, transported
  to `T x Y` with the max metric of compatible metrics on `T` and `Y`. If
  `t ≠ t'` had `d(z·t, z·t') < c` for all `z`, then `(t,y_0) ≠ (t',y_0)`
  would satisfy `d((λ,z)·(t,y_0), (λ,z)·(t',y_0)) = d(z·t, z·t') < c` for all
  `(λ,z)`, which is a contradiction. So `c` is an expansive constant of `T`.
- *Coding.* Take a finite partition `P` of `T` into clopen sets of diameter
  `< c` (it exists by zero-dimensionality and compactness). The map
  `t ↦ (z ↦ the cell of P containing z·t)` is continuous and equivariant.
  It is injective, since two points with the same coding stay `c`-close along
  the whole orbit. Its image `T'` is a `Z^2`-subshift, and the map is a
  conjugacy onto it (compactness again).

**Step 3: `X` is conjugate to the literal product.** Put

    P = { p ∈ (C x B)^Λ : p(λ,z) = (t(z), y(λ)) for some t ∈ T', y ∈ Y }.

The map `(t,y) ↦ p` is a continuous bijection `T' x Y -> P`, and it is
equivariant:
`((μ,w)·p)(λ,z) = p(λμ, z+w) = ((w·t)(z), (μ·y)(λ))`.
So `P` is a subshift and it is conjugate to `X`, through Steps 1 and 2.

**Step 4: `P` is of finite type.** (Finite type is a conjugacy invariant over
any countable group.) Let `F : P -> X` and `G : X -> P` be mutually inverse
conjugacies.
- By Curtis--Hedlund--Lyndon, `F(p)(g) = f((g·p)|_W)` for a finite window
  `W ⊆ Λ` and a rule `f` defined on the `W`-patterns of `P`. Extend `f`
  arbitrarily to all of `(C x B)^W`, giving a block map
  `F~ : (C x B)^Λ -> A^Λ`. Likewise `G(x)(g) = γ((g·x)|_V)`, extended to
  `G~ : A^Λ -> (C x B)^Λ`.
- *Claim:* `P = { p : F~(p) ∈ X and G~(F~(p)) = p }`.
  - `⊆`: for `p ∈ P`, `F~(p) = F(p) ∈ X` and `G~(F(p)) = G(F(p)) = p`.
  - `⊇`: if `x = F~(p) ∈ X`, then `p = G~(x) = G(x) ∈ P`.
- Both conditions are local. Let `X` be defined by forbidden patterns `ℱ` on a
  window `K`. Since `F~` commutes with the shift, `(g·F~(p))|_K` is a function
  of `(g·p)|_{WK}`, so the first condition forbids a finite set of
  `WK`-patterns. The second says `G~(F~(p))(g) = p(g)` for all `g`, and both
  sides are functions of `(g·p)|_{VW ∪ {1}}`.
- So `P` is defined by finitely many forbidden patterns on the finite window
  `WK ∪ VW ∪ {1}`.

**Step 5: the slice at `Λ_0 x {0}`.** Let `P` be defined by forbidden
patterns on a finite window contained in `K_0 x K_1`, with `K_0 ⊆ Λ_0` and
`K_1 ⊆ Z^2` finite. Let `L = { y|_{K_0} : y ∈ Y }` and

    Y_K = { y' ∈ B^{Λ_0} : (λ·y')|_{K_0} ∈ L for every λ ∈ Λ_0 },

a `Λ_0`-SFT containing `Y`. Take `y' ∈ Y_K` and any `t ∈ T'`, and let `p'` be
the product configuration `p'(λ,z) = (t(z), y'(λ))`.
- For `g = (λ,z)`, `(g·p')(k_0,k_1) = ((z·t)(k_1), (λ·y')(k_0))`.
- Choose `y'' ∈ Y` with `y''|_{K_0} = (λ·y')|_{K_0}`. The product
  configuration of `(z·t, y'')` lies in `P` and agrees with `g·p'` on
  `K_0 x K_1`. So no forbidden pattern of `P` occurs in `p'` at `g`.
- Hence `p' ∈ P`, so `p'(λ,z) = (t_1(z), y_1(λ))` with `y_1 ∈ Y`. Reading the
  second coordinate gives `y' = y_1 ∈ Y`.

So `Y = Y_K` is a `Λ_0`-subshift of finite type. `∎`

**Remark (why global injectivity is needed).** Injectivity of `π` only over a
single fibre `{t_0} x Y`, or over one `Z^2`-orbit in `T`, does not suffice.
Step 1 then gives no conjugacy, and the recoding in Step 4 has no uniform
window over the other fibres. This is where the floating locus of a genuine
M1 solution can live.

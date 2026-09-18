---
rg: 2
id: nv-gap-class-cocycles-are-coboundaries-proof
kind: route
title: "Local gaps bound the cocycle on brick-product subgroups; vanishing on V^n spreads to every H_P, and g H_D g^{-1} = H_R forces b(g) = 0"
target: nv-gap-class-cocycles-are-coboundaries
requires:
  - nv-extractable-cocycles-bounded-on-centralizers
---

Notation as in the target. `‖·‖` is the norm of the representation space `K`. A 1-cocycle
satisfies `b(gh) = b(g) + ρ(g) b(h)`, so `b(e) = 0` and `b(g^{-1}) = −ρ(g)^{-1} b(g)`.
From `nv-extractable-cocycles-bounded-on-centralizers` (and its proof) we use only the elements
`h_1, h_2, h_3 ∈ V` and the construction of its Step 3; everything else is proved here. One
standard fact is imported:
- (F) If an affine isometric action of a group on a Hilbert space has a bounded orbit, it has a
  fixed point (the circumcentre of the orbit; Bekka–de la Harpe–Valette, *Kazhdan's property
  (T)*, Lemma 2.2.7, not re-read at source). For the affine action `h·v = ρ(h)v + b(h)` of a
  subgroup `H`, the orbit of `0` is `{b(h)}`; a fixed point `ξ` gives `b(h) = ξ − ρ(h)ξ` on `H`.

**Step 0 (brick-product subgroups).** For a brick partition `P` put
`H_P = {a ∈ G : aB = B and ι_B^{-1} a ι_B ∈ V^n for every B ∈ P}`, where `V^n = V_{(1)} ⋯ V_{(n)}`
is the subgroup of product maps `a_1 × … × a_n`.
- `H_P` is a subgroup, and `H_P = A_P^{(1)} A_P^{(2)} ⋯ A_P^{(n)}`: write
  `ι_B^{-1} a ι_B = a_{B,1} × … × a_{B,n}` and let `a^{(j)} = (a_{B,j})_B^{P,j}`. The factors act on
  distinct coordinates inside each brick, so they commute and their product is `a`.
- Each `h^{P,j}` is an element of `nV`: on `B` it is the brick table of `h_B` in coordinate `j`,
  prefixed by `w_1,…,w_n`, and the bricks of `P` partition `C^n`.
- **Commuting.** For `j ≠ j'`, every element of `A_P^{(j)}` commutes with every element of
  `A_P^{(j')}`: both preserve each `B ∈ P`, and inside `ι_B` they act on different coordinates.
- `H_{\{C^n\}} = V^n`.

**Step 1 (bounded on each `H_P`).** Fix `P` and `j`. Since `n ≥ 2`, pick `j' ≠ j`. By the gap
hypothesis there are a finite `F ⊆ A_P^{(j')}` and `c > 0` with `c‖r‖ ≤ Σ_{s∈F}‖r − ρ(s)r‖`.
Let `a ∈ A_P^{(j)}`. For `s ∈ F`, `as = sa` gives `b(a) + ρ(a)b(s) = b(s) + ρ(s)b(a)`, that is

`(1 − ρ(s)) b(a) = (1 − ρ(a)) b(s)`, so `‖(1 − ρ(s)) b(a)‖ ≤ 2‖b(s)‖`.

Apply the gap to `r = b(a)`: `‖b(a)‖ ≤ (2/c) Σ_{s∈F} ‖b(s)‖`, a bound independent of `a`. So `b`
is bounded on each `A_P^{(j)}`, and by Step 0 and `‖b(xy)‖ ≤ ‖b(x)‖ + ‖b(y)‖` it is bounded on
`H_P = A_P^{(1)} ⋯ A_P^{(n)}`. (The bound depends on `P`; nothing uniform is needed.)

**Step 2 (normalize on `V^n`).** By Step 1 for `P = {C^n}`, `b` is bounded on `V^n`. By (F)
there is `ξ ∈ K` with `b(h) = ξ − ρ(h)ξ` for `h ∈ V^n`. Replace `b` by `b' = b − (ξ − ρ(·)ξ)`.
This is again a cocycle, `b − b'` is a coboundary, and `b' = 0` on `V^n`. Write `b` for `b'`.

**Step 3 (no invariant vectors).** If `r` is fixed by `A_P^{(j)}` for some `P, j`, then the gap
inequality for `A_P^{(j)}` gives `c‖r‖ ≤ 0`, so `r = 0`.

**Step 4 (`b = 0` on every `H_P`).** Fix `P`. By Step 1 and (F) there is `η` with
`b(a) = η − ρ(a)η` for `a ∈ H_P`. Let `M` be the largest length of a coordinate-1 word of a
brick of `P`, and `P' = {[w] × C^{n−1} : |w| = M}`.
- `A_{P'}^{(1)} ⊆ V^n`: `h^{P',1}` acts by `(wz_1, z_2, …) ↦ (w h_w(z_1), z_2, …)`, which is
  `k × id × … × id` with `k ∈ V` given by `wz ↦ w h_w(z)`.
- `A_{P'}^{(1)} ⊆ H_P`: for `B = [u_1] × … × [u_n] ∈ P`, `|u_1| ≤ M`, so `[u_1]` is a union of
  cylinders `[w]`, `|w| = M`, each preserved by `k`. Hence `kB = B` in coordinate 1 and
  `ι_B^{-1} (k × id) ι_B = k' × id` with `k'(z) = u_1^{-1} k(u_1 z)`. This `k'` is in `V`: for
  each `w'` of length `M − |u_1|`, with `w = u_1 w'`, it acts on `[w']` by `w'z ↦ w' h_w(z)`, a
  finite prefix table.
- So for `a ∈ A_{P'}^{(1)}`: `0 = b(a) = η − ρ(a)η` by Step 2. Then `η` is `A_{P'}^{(1)}`-fixed
  and `η = 0` by Step 3. Hence `b = 0` on `H_P`.

**Step 5 (every element).** Let `g ∈ G`. By definition of `nV`, there are brick partitions
`D = {D_1, …, D_m}` and `R = {R_1, …, R_m}` with `g ∘ ι_{D_k} = ι_{R_k}` on `C^n` for each `k`.
- `g H_D g^{-1} = H_R`. For `a ∈ H_D`, `gag^{-1}` maps `R_k = gD_k` onto itself, and
  `ι_{R_k}^{-1} (g a g^{-1}) ι_{R_k} = ι_{D_k}^{-1} a ι_{D_k} ∈ V^n`. So `g H_D g^{-1} ⊆ H_R`;
  the same with `g^{-1}` (which has table `R → D`) gives equality.
- For `k ∈ H_R` put `h = g^{-1} k g ∈ H_D`. From `gh = kg` and Step 4 (`b(h) = b(k) = 0`):
  `b(g) = b(g) + ρ(g) b(h) = b(gh) = b(kg) = b(k) + ρ(k) b(g) = ρ(k) b(g)`.
- So `b(g)` is fixed by `H_R ⊇ A_R^{(1)}`, and `b(g) = 0` by Step 3.

So the normalized cocycle is `0`, and the original one is the coboundary `g ↦ ξ − ρ(g)ξ`. ∎

**Step 6 (extractable representations are in the gap class).** Let `r ↦ μ_r` be a measure
extraction as in the target's corollary. Fix a brick `B` and a coordinate `j`, and let
`β_i ∈ G` (`i = 1,2,3`) act on `B` by `ι_B h_i^{(j)} ι_B^{-1}` and by the identity off `B`. For
Borel `E ⊆ C` put `Ẽ = ι_B(pr_j^{-1} E) ⊆ B` and `ν_B(E) = μ_r(Ẽ)`, a measure of mass `μ_r(B)`.
Then `β_i^{-1} Ẽ = ι_B(pr_j^{-1} h_i^{-1} E)`, so by equivariance and continuity, with
`s = ρ(β_i) r` (so `‖s‖ = ‖r‖`),

`|ν_B(h_i^{-1}E) − ν_B(E)| = |μ_s(Ẽ) − μ_r(Ẽ)| ≤ 2‖r‖ ‖r − ρ(β_i) r‖ =: δ_i`.

With `δ = max_i δ_i`, the three identities `h_1^{-1}[00] = [0]`, `h_2^{-1}[01] = [0]`,
`h_3^{-1}[1] = [0]` give `ν_B[01] ≤ δ`, `ν_B[00] ≤ δ`, `ν_B[1] ≤ ν_B[0] + δ ≤ 3δ`, so
`μ_r(B) = ν_B(C) ≤ 5δ ≤ 10‖r‖ Σ_i ‖r − ρ(β_i) r‖`. (This is Step 1 of the proof of
`nv-extractable-cocycles-bounded-on-centralizers`, run inside `B`.) Summing over `B ∈ P`:

`‖r‖² = Σ_{B∈P} μ_r(B) ≤ 10‖r‖ Σ_{B∈P} Σ_i ‖r − ρ(β_i^B) r‖`,

so `‖r‖/10 ≤ Σ_{s∈F}‖r − ρ(s)r‖` with `F = {β_i^B} ⊆ A_P^{(j)}` (each `β_i^B = h^{P,j}` with
`h_B = h_i` and `h_{B'} = id` otherwise).

The examples of the target satisfy the hypotheses. Take the construction of Step 3 of
`nv-extractable-cocycles-bounded-on-centralizers-proof`, `(ρ(g)f)(ω) = √(dg_*μ/dμ)(ω) π(g) f(g^{-1}ω)`
on `L²(Ω, μ; H)` with an equivariant `p: Ω → Prob(C^n)`, but extract on all of `C^n`:
`μ_f(E) = ∫ |f(ω)|² p(ω)(E) dμ(ω)`. Mass and continuity are as there. For every `g ∈ G` the
change of variables there gives `μ_{ρ(g)f}(E) = ∫ |f(ω')|² p(gω')(E) dμ(ω') = ∫ |f|² p(ω')(g^{-1}E) dμ = (g_*μ_f)(E)`;
that computation never used that `g` is a coordinate element. Charts (`p(φ) = φ_*λ`),
`G/L` with `L` fixing `μ_L` (`p(gL) = g_*μ_L`; `L = 1` is the regular representation), and the
Koopman representation (`Ω = C^n`, `p(x) = δ_x`) are the cases listed there. Weak containment:
for fixed finite `F` and `c`, the inequality `Σ_{s∈F} (2φ(e) − φ(s) − φ(s^{-1})) ≥ (c²/|F|) φ(e)`
(which follows from the gap by Cauchy–Schwarz, and implies a gap with constant `c/|F|`) is
linear in the function of positive type `φ` and closed under pointwise limits, so it passes to
`σ ≺ ρ`, as in Step 4 of that proof.

**Where every member dies (for the record).** Invariant: spectral gap of brick-local
coordinate copies of `V`. Step: Step 5, the conjugation `g H_D g^{-1} = H_R`, after Steps 1–4
make `b` vanish on every brick-product subgroup. For `n = 1` Step 1 fails (no second
coordinate), consistent with Farley's proper chart cocycle on `V`.

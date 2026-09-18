---
rg: 2
id: rcwa-groups-bh-via-sign-doubling-and-odometer-host-proof
kind: route
title: Sign-double RCWA(Z) into its class-wise increasing part, extend to the P-adic box space, and run the 2V_tau proof for the odometer on the class-transposition k-graph times a binary rose
target: rcwa-groups-satisfy-boone-higman
requires:
  - ct-p-z-is-a-one-vertex-k-graph-full-group
  - odometer-2v-is-fp-simple-and-contains-bs12
---

Notation is that of the target. `Λ_P`, boxes `B(r, m)`, canonical box maps and `Ẑ_P` are as in
`ct-p-z-is-a-one-vertex-k-graph-full-group`. Paths of `Λ_P` are `(m, r)` with `0 ≤ r < m` and
`m` `P'`-smooth, composing by `(m, r)(m', r') = (mm', r + m r')`. The source statements of Li
and Matui are quoted with line numbers in `research/artifacts/gq-affq-kep-odometer-host.md` §1.

## Step 1. Sign doubling

For `g ∈ RCWA(Z)`, let `ε_g(n) ∈ Z/2` be `0` if `g` is increasing on the affine piece
containing `n`, and `1` if decreasing. This does not depend on the modulus chosen, since
refining a piece keeps its slope.
- **Cocycle.** Near `n` (on a small enough class) `gh` is the composite of the pieces of `h` at
  `n` and of `g` at `h(n)`, so `ε_{gh}(n) = ε_g(h(n)) + ε_h(n)`.
- **The action.** `g·(n, i) = (g(n), i + ε_g(n))` is an action of `RCWA(Z)` on `Z × Z/2`, and it
  is faithful.
- **Transport.** Let `φ(n, 0) = 2n` and `φ(n, 1) = −2n − 1`, a bijection `Z × Z/2 → Z`. Put
  `δ(g) = φ g φ^{-1}`. Then `δ` is an injective homomorphism `RCWA(Z) → Sym(Z)`.

**`δ(g)` is RCWA with every piece increasing.** Let `g(n) = (a n + b)/c` on `r(m)`, with slope
`σ = a/c`. The four cases:

| `u` | `ε_g(n)` | `δ(g)(u)` | slope in `u` |
|---|---|---|---|
| `2n`, `n ∈ r(m)` (a class mod `2m`) | `0` | `2g(u/2) = (a u + 2b)/c` | `σ > 0` |
| `2n` | `1` | `−2g(u/2) − 1` | `−σ > 0` |
| `−2n − 1`, `n ∈ r(m)` (a class mod `2m`) | `0` | `−2g(−(u+1)/2) − 1` | `σ > 0` |
| `−2n − 1` | `1` | `2g(−(u+1)/2)` | `−σ > 0` |

So `δ(g)` is affine and increasing on each class mod `2m`. Its multipliers are those of `g`,
and its modulus is `2m`. Hence `δ` maps `RCWA_P(Z)` into `RCWA_P(Z)`, since `2 ∈ P'`, and its
image consists of *class-wise increasing* RCWA permutations.

## Step 2. Class-wise increasing maps extend to `Ẑ_P`

Let `h ∈ RCWA_P(Z)` be class-wise increasing, affine on the classes `r_i(m)`,
`0 ≤ r_i < m`. The argument of `ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers`,
steps 1–2, applies verbatim, since positivity of the slopes was all it used there.
- **Images are residue classes.** `h(r_i(m))` is a residue class `s_i(n_i)`, with
  `0 ≤ s_i < n_i` and `n_i = (a_i/c_i) m` a `P'`-smooth integer. These classes partition `Z`.
- **Integer shift.** There is an integer `c_i` with `h(r_i + t m) = s_i + (t + c_i) n_i` for all
  `t`.

Define `ĥ` on `Ẑ_P` by `ĥ(r_i + m z) = s_i + n_i (z + c_i)` on the box `B(r_i, m)`.
- **A homeomorphism.** The boxes `B(r_i, m)` partition `Ẑ_P`. So do the boxes `B(s_i, n_i)`,
  because boxes meet iff their classes meet, and a clopen set containing the dense set `Z`
  is everything.
- **Extension.** `ĥ` restricts to `h` on `Z`.
- **Faithful.** By density of `Z`, `h ↦ ĥ` is an injective homomorphism.

## Step 3. The host and the embedding

**The category and the action.**
- **The category.** `Λ = Λ_P × F_2^+` is a one-vertex `(k+1)`-graph, with `k = |P'|`, `p` edges
  of colour `p ∈ P'`, and `2` edges of the binary colour `∗`. Paths are `μ = (μ_P, μ_∗)`, and
  the cylinder of `μ` is `μX = B(r_μ, m_μ) × C(μ_∗)`, with `X = Ω_∞ = Ẑ_P × C`.
- **The action of `Z = ⟨a⟩`.** For `n ∈ Z`, `a^n·((m, r), w) = ((m, (r + n) mod m), w)` with
  restriction `a^{⌊(r+n)/m⌋}`.
- **Why it is a self-similar action.** This is the carry arithmetic of the homeomorphism
  `(x, y) ↦ (x + n, y)` of `X`:
  - `r + m z + n = ((r + n) mod m) + m (z + ⌊(r+n)/m⌋)`, and `C` is untouched;
  - for composites, `(mm', r + m r')`, the two-step computation and the direct one give the
    same residue mod `mm'` and the same carry;
  - the binary colour is fixed with restriction `a^n`, and the factorizations
    `(λ, ∅)(∅, w) = (∅, w)(λ, ∅)` are treated alike, exactly as in step A of
    `odometer-2v-is-fp-simple-and-contains-bs12-proof`.

  The action is degree-preserving.
- **Pseudo-free.** `a^n` fixes `((m, r), w)` iff `m | n`, with restriction `a^{n/m}`. So only
  `n = 0` strongly fixes a path.
- **Right cancellation and (F).** As in that step A, `D = Λ ⋈ Z` is right cancellative, so (F)
  holds (Li l.1456). Li also notes (Example ex:ZS) that right cancellation up to `=^*` is
  automatic for degree-preserving actions, since `P = Z_{≥0}^{k+1}` is cancellative.

**The groupoid.** `G = I_l(D) ⋉ X`, with basic bisections `Z(λ, n, μ)` given by the germs of
`μ y ↦ λ(a^n·y)`. Put `H_P = F(G)`.

**The embedding.** For `g ∈ RCWA_P(Z)`, let `h = δ(g)` and `ι(g) = ĥ × id_C`.
- On `B(r_i, m) × C` this is the basic bisection with `μ = ((m, r_i), ∅)`, `λ = ((n_i, s_i), ∅)`
  and `n = c_i`.
- So `ι(g) ∈ H_P`, and `ι` is an injective homomorphism by Steps 1–2.

## Step 4. `G` is effective, Hausdorff and essentially principal; minimal; purely infinite

**Effective.** Suppose `μ y ↦ λ(a^n·y)` is the identity on a cylinder `μνX`. Put `ν' = a^n·ν`
and `a^c = a^n|_ν`.
- **Box part.** For all `z ∈ Ẑ_P`, `r_{μν} + M z = r_{λν'} + M'(z + c)`. Comparing `z = 0` and
  `z = 1` gives `M = M'`. The residues lie in `[0, M)`, so `c = 0` and `μ_P ν_P = λ_P ν'_P`.
  Degrees are preserved, so `d(μ_P) = d(λ_P)`, and unique factorization gives `μ_P = λ_P`.
- **Binary part.** `μ_∗ ν_∗ = λ_∗ ν_∗`, so `μ_∗ = λ_∗`.
- **Conclusion.** `a^n` strongly fixes `ν`, so `n = 0` and the bisection is a unit.

**Hausdorff.** The unit-germ set of `Z(λ, n, μ)` is the interior of its fixed set.
- **Equal degrees, `(λ, n) ≠ (μ, 0)`.** The fixed set is empty.
  - In the box part, `r_μ + M z = r_λ + M(z + n)` forces `n = 0` and `r_μ = r_λ`.
  - In the binary part, words of equal length must be equal.
- **Unequal degrees.** The fixed set has empty interior.
  - A binary fixed point solves `μ_∗ y = λ_∗ y` with `|μ_∗| ≠ |λ_∗|`, which determines `y`.
  - A box fixed point solves `(m_μ − m_λ) z = const` with `m_μ ≠ m_λ`, which has at most one
    solution in each `Z_q`.
- So every unit-germ set is `μX` or `∅`, hence clopen.

**Essentially principal.** Points with nontrivial isotropy lie in countably many such nowhere
dense closed fixed sets. By Baire, trivial isotropy is dense, and `X` is a Cantor set. This is
Matui's standing assumption (l.1183).

**Minimal.** Canonical box maps and binary prefix replacements, all with `n = 0`, take any
cylinder onto any other.

**Purely infinite.** Every clopen `A` is a finite disjoint union of cylinders `μX`. Put
`U = ⋃ {μ y ↦ μ(∅, 0) y}` and `V = ⋃ {μ y ↦ μ(∅, 1) y}`. They satisfy Matui's Definition `pi`,
exactly as in step D of the `2V_τ` route.

## Step 5. `F_∞`

Apply Li, Example ex:ZS (III), with:
- `C = Λ`, `P = Z_{≥0}^{k+1}`, `G = Z` and `X = Ω_∞`;
- `𝔢_P = ∅`, so `Y = X(v; ∅) = X` (Li l.1178).

The hypotheses hold:
- **The category.** `Λ` is a finite one-vertex higher-rank graph with at least two edges of each
  colour. The parent node checks this for `Λ_P`, via Li's Cor. `cor:OneVertex`, and the product
  with the binary rose adds one colour with `2` edges.
- **The action.** It is degree-preserving, and (F) holds (Step 3).
- **Stabilizers.** `Λ^* = Λ^0`, so `D^*(w, w) = St(Z, v) = Z` (rem:ZS-Stab), which is of type
  `F_∞`.

Hence `H_P` is of type `F_∞`, in particular finitely presented.

## Step 6. Perfect, hence simple

**Normal form.** Let `f ∈ H_P` map `μ_i y ↦ λ_i(a^{n_i}·y)` on a partition `{μ_i X}`. For a path
`μ`, let `σ_μ` be `μ y ↦ μ(a·y)` on `μX` and the identity elsewhere. Then
`f = h ∏_i σ_{μ_i}^{n_i}`, where `h(μ_i y) = λ_i y` lies in `[[G_Λ]]`, the full group of the
action-free `(k+1)`-graph groupoid.

**`[[G_Λ]]` is perfect.** The argument of the parent node, steps 3–4, applies with the binary
colour included.
- By Farsi–Kumjian–Pask–Sims, `H_*(G_Λ) = 0`, because the binary colour has
  `N_∗ = 2 − 1 = 1`.
- Li's AH sequence (arXiv:2209.08087, Cor. `cor:AHConj`) then gives `[[G_Λ]]^{ab} = 0`.

**The `σ_μ` die in `H_P^{ab}`.**
- **They are all conjugate.** For proper cylinders `μX ≠ X ≠ μ'X`, split the complements by
  binary letters, each split adding one cylinder, until both are unions of the same number of
  cylinders. Then some `h ∈ [[G_Λ]]` is `μ y ↦ μ' y` on `μX` and maps `X ∖ μX` onto `X ∖ μ'X`,
  so `h σ_μ h^{-1} = σ_{μ'}`.
- **Their common class is `0`.** Let `c` be the common image in `H_P^{ab}`. The action fixes
  binary letters with restriction `a`, so `σ_μ = σ_{μ(∅,0)} σ_{μ(∅,1)}`. Hence `c = 2c`, so
  `c = 0`.
- **`σ_∅` too.** The same splitting shows that `σ_∅ = σ_{(∅,0)} σ_{(∅,1)}` also maps to `0`.

**Conclusion.** `H_P^{ab} = 0`. `G` is purely infinite and minimal (Step 4), so by Matui's
Theorem simple2 `D(H_P)` is simple, and `H_P = D(H_P)`.

## Step 7. The case `P = ∅`

Then `Λ_∅` is the binary rose, `Λ = F_2^+ × F_2^+`, and the action is the binary odometer on
colour `1`. So `H_∅` is exactly `2V_τ`, and Steps 3–6 are the refereed route
`odometer-2v-is-fp-simple-and-contains-bs12-proof`. Hence `RCWA_∅(Z)`, all RCWA permutations
with 2-power data, embeds in `2V_τ` using only refereed inputs together with Steps 1–2.

## Step 8. Conclusion

A finitely generated `H ≤ RCWA(Z)` has finitely many generators, each with finitely many data,
so `H ≤ RCWA_P(Z)` for some finite `P`. Then `ι(H) ≤ H_P`, which is finitely presented and
simple by Steps 5–6.

## Calibration

- **Nonzero shift.** The translation `t(n) = n + 1` is class-wise increasing with shift `c = 1`
  on the single class `0(1)`, so Step 2 extends it directly to `σ_∅`, the odometer `τ × id` for
  `P = ∅`. Its double `δ(t)` is `n ↦ n + 2` on evens and `n ↦ n − 2` on odds, with shifts `+1`
  and `−1`, so `ι(t) = σ_{((2,0),∅)} σ_{((2,1),∅)}^{-1}`. Neither `t` nor `δ(t)` fixes `N_0`, so
  neither lies in any `CT_P(Z)`. For class-wise increasing subgroups the doubling can be
  skipped.
- **A decreasing piece.** The reflection `n ↦ −n − 1` is decreasing on `0(1)`. Its double is
  `δ(g)(2n) = 2n + 1` and `δ(g)(2n + 1) = 2n`, the class transposition `τ_{0(2),1(2)}`, which is
  class-wise increasing with shift `0`.

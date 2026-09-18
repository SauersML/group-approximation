---
rg: 2
id: germ-extension-base-trivial-characters-lie-in-sigma-proof
kind: route
title: Germ charges are coboundaries of a finitely valued potential; the potential is a Morse height on the germ complex with highly connected ascending links
target: germ-extension-base-trivial-characters-lie-in-sigma
requires:
  - germ-complex-and-bux-gonzalez-morse-inputs
---

Notation and the imported items (FGE), (K), (Stab), (Orb), (Conn), (Fin), (BG) and (ML) are those of
`germ-complex-and-bux-gonzalez-morse-inputs`. Fix `m >= 1` and a nonzero `χ: G -> R` with `χ(B) = 0`. Hypotheses 1–4
are those of the claim.

**Paradigm note.**

- **Why this works where the dead approach failed.** The Stein–Farley route (`rover-nekrashevych-higher-sigma-full-via-kernel-brown`)
  has cell stabilizers built from products `G^n`, so it needs `G` itself of type `F_m`. The Basilica group is not even
  finitely presented, and the route gives nothing there.
  - In the germ complex, cell stabilizers are virtually `Fix_B(M)`, where `χ` vanishes.
  - Equivariance of the height comes from a potential on the singular set instead of from cocompactness of a kernel.
- **First falsifiable step.** The existence of an equivariant affine height, which is exactly the vanishing of the
  isotropy charge (Step 2).
- **Calibration.** Thompson's `F` over `F'`, where the step fails and the conclusion is false (see the claim).

## Step 0 (G has type F_m)

Hypothesis 1 for `sing(G)^{m+1}` implies it for `sing(G)^m`, by projecting onto the first `m` coordinates. So
hypotheses 1–3 give (Fin) with `n = m`, and `Σ^m(G)` is defined.

## Step 1 (germ charge)

Let `p in X` and `β in Bgerm(G,p)`. A *representative* of `β` is `k in G` with `sing(k) ⊆ {p}` and `(Bk)_p = β`.

- If `p ∉ sing(G)`, the only germ is trivial, and `k = 1` represents it.
- If `β = (Bg)_p` with `p in sing(g)`, then (FGE)(3) gives `k` with `sing(k) = {p}` and `(k)_p = (g)_p`.
- If `p in sing(G)` but `β` is trivial, `k = 1` represents it.

Define `c(β) = χ(k)`.

**(1a) Well defined.** Let `k, k'` represent `β`. Then `(k')_p = (bk)_p` for some `b in B`.

- At `k(p)`, the element `k'k^{-1}` agrees with `b`.
- At `y != k(p)`: `k^{-1}` is nonsingular at `y`, since `sing(k^{-1}) = k(sing k) ⊆ {k(p)}`. Also `k'` is nonsingular
  at `k^{-1}(y) != p`. Composites of maps that locally agree with elements of `B` again locally agree with elements of `B`.

So `sing(k'k^{-1}) = ∅`, and `k'k^{-1} in B` by (FGE)(2). Hence `χ(k') = χ(k)`. In particular `c((B)_p) = 0`.

**(1b) Right `B`-invariance.** For `b in B`: `c((Bgb)_{b^{-1}x}) = c((Bg)_x)`.

If `k` represents `(Bg)_x`, then `sing(kb) ⊆ b^{-1}sing(k) ∪ sing(b) ⊆ {b^{-1}x}`. Also
`(kb)_{b^{-1}x} = (k)_x (b)_{b^{-1}x} in (Bgb)_{b^{-1}x}`. So `kb` represents `(Bgb)_{b^{-1}x}`, and `χ(kb) = χ(k)`.

**(1c) Cocycle.** For `x, y in G` and `p in X`: `c((Bxy)_p) = c((Bx)_{y(p)}) + c((By)_p)`.

- Let `k_y` represent `(By)_p`, so `(k_y)_p = (by)_p` with `b in B`. Put `q = k_y(p) = b(y(p))`.
- Let `k_x` represent `(Bxb^{-1})_q`, so `(k_x)_q = (b'xb^{-1})_q` with `b' in B`.
- Then `sing(k_x k_y) ⊆ k_y^{-1}{q} ∪ {p} = {p}`.
- Also `(k_x k_y)_p = (k_x)_q (k_y)_p = (b'xb^{-1})_q (by)_p = (b'xy)_p`.

So `k_x k_y` represents `(Bxy)_p`, and `c((Bxy)_p) = c((Bxb^{-1})_q) + c((By)_p)`. By (1b), with `q = b(y(p))`,
`c((Bxb^{-1})_q) = c((Bx)_{y(p)})`.

**(1d) Additivity.** For every `g in G`, `χ(g) = Σ_{p in sing(g)} c((Bg)_p)`.

Note first that `c((Bg)_p) = 0` for `p ∉ sing(g)`: there `(g)_p = (b)_p` for some `b in B`, so the `B`-germ is trivial.

The proof is by induction on `|sing g|`. If `sing g = ∅`, then `g in B` and both sides vanish. Otherwise:

- Pick `p in sing g` and `k` with `sing(k) = {p}` and `(k)_p = (g)_p`. Put `g' = gk^{-1}`.
- Then `sing(g') ⊆ k(sing g) ∪ {k(p)}`. At `k(p)` the germ of `g'` is `(g)_p (k^{-1})_{k(p)} = (k)_p (k^{-1})_{k(p)}`,
  the identity germ. So `sing(g') ⊆ k(sing g \ {p})`.
- By induction and the note, `χ(g') = Σ_{x in sing g \ {p}} c((Bg')_{k(x)})`.
- By (1c), `c((Bg')_{k(x)}) = c((Bg)_x) + c((Bk^{-1})_{k(x)})`. The last term is `0`, because `k^{-1}` is nonsingular
  at `k(x)` for `x != p`.
- Finally `χ(k) = c((Bk)_p) = c((Bg)_p)`.

Adding, `χ(g) = χ(g') + χ(k) = Σ_{x in sing g} c((Bg)_x)`.

**(1e) Action on germs.** For `β in Bgerm(G,p)` and `g in G`: `c(g·β) = c(β) − c((Bg)_p)`.

Write `β = (Bk)_p`, so `g·β = (Bkg^{-1})_{g(p)}`. By (1c), `c(g·β) = c((Bk)_p) + c((Bg^{-1})_{g(p)})`. Also by (1c),
`0 = c((B)_p) = c((Bg^{-1})_{g(p)}) + c((Bg)_p)`.

## Step 2 (the isotropy charge vanishes)

Fix `p in sing(G)`. For `g, g' in Stab_G(p)`, (1c) gives `c((Bgg')_p) = c((Bg)_p) + c((Bg')_p)`. The value depends only
on the germ `(g)_p`, so this is a homomorphism `φ_p: (G)_p -> R`.

- It kills `(B)_p`, whose elements have trivial `B`-germ.
- `(B)_p` has finite index by hypothesis 3, so it contains a finite-index normal subgroup `N`.
- For `z in (G)_p`, some power `z^e` lies in `N`. So `e·φ_p(z) = 0`, and `φ_p = 0`.

## Step 3 (the potential)

`sing(G)` is `G`-invariant. If `x in sing(g)` and `y in G`: when `y` is nonsingular at `x`, `gy^{-1}` is singular at
`y(x)`; otherwise `y(x) in sing(y^{-1})`.

Choose a base point `p_O` in every `G`-orbit `O ⊆ sing(G)` and a constant `κ_O in R`. Put
`ν(g p_O) = κ_O − c((Bg)_{p_O})`.

- **Well defined.** If `g p_O = g' p_O`, then `g'^{-1}g in Stab_G(p_O)`. By (1c) and Step 2,
  `c((Bg)_{p_O}) = c((Bg')_{p_O}) + c((Bg'^{-1}g)_{p_O}) = c((Bg')_{p_O})`.
- **Transformation law.** For `y in G` and `q in sing(G)`, `ν(y q) = ν(q) − c((By)_q)`, by (1c).
- **Constant on `B`-orbits.** `c((Bb)_q) = 0` for `b in B`. By hypothesis 1 there are finitely many `B`-orbits, so `ν`
  takes finitely many values, and so do the germ charges.
- **Coboundary.** For `β = (Bk)_p` with target orbit `B·k(p)`, `c(β) = ν(p) − ν(k(p))`. Write `τ(β) = ν(k(p))`. It does
  not depend on the representative, since `ν` is constant on `B`-orbits.

**Choice of constants.** On an orbit `O`, `ν = κ_O + a` where `a` runs through the finite set
`A_O = {−c((Bg)_{p_O}) : g in G}`.

- If `A_O` has at least two elements, choose `κ_O` with `−max A_O < κ_O < −min A_O` and `κ_O ∉ −A_O`. Then `ν` takes
  both signs on `O` and never vanishes.
- If `A_O` is a single point, choose `κ_O` with `ν > 0` on `O`.
- Some orbit `O_1` has `|A_{O_1}| >= 2`. Otherwise `ν` is constant on each `G`-orbit. Every germ `β` at `p` has target in
  `G·p`, so `c(β) = 0`, and (1d) gives `χ = 0`.

Summary of the choice:

- (P1) `ν` is nowhere zero, with `ε = min |ν| > 0`.
- (P2) Every `G`-orbit contains a `B`-orbit with `ν > 0`.
- (P3) Some `B`-orbit `Ω_−` has `ν < 0`.

## Step 4 (the height)

For `p in sing(G)` define `f_p: T_p -> R` on vertices by `f_p(*) = ν(p)` and `f_p(β) = c(β)`, extended affinely on
edges.

For a point `γ` of `K`, put `h(γ) = Σ_p f_p(γ_p)`.

- On any cube only finitely many coordinates vary, and the rest sit at the basepoint `(B)_p`, where `f_p = 0`.
- So `h` is a finite sum of affine functions on each cube, hence continuous and affine on cells.

Put `H = −h`.

**Equivariance.** Let `γ` be a vertex with hidden set `S`. The hidden set of `g·γ` is `g(S)`, and
`(g·γ)(g(p)) = g·γ(p)`. By (1e) and the transformation law,

- `h(g·γ) = Σ_{p ∉ S} [c(γ(p)) − c((Bg)_p)] + Σ_{p in S} [ν(p) − c((Bg)_p)] = h(γ) − Σ_{p in sing(G)} c((Bg)_p)`;
- by (1d) this is `h(γ) − χ(g)`.

Both sides are affine on cubes and `G` acts by cubical maps, so `H(gy) = χ(g) + H(y)` for all `y in K`.

**Edge increments.** Every edge of `K` changes one coordinate `p` between `*` and some `β in Bgerm(G,p)`. Going from
`*` to `β` changes `H` by `−(c(β) − ν(p)) = τ(β)`.

- *Revealing* `p` as `β` raises `H` iff `τ(β) > 0`.
- *Hiding* a visible `p` with germ `β` raises `H` iff `τ(β) < 0`.
- By (P1), `|ΔH| >= ε` on every edge, so `(H, 0)` is a Morse function in the sense of (ML) on any subcomplex of `K`.

## Step 5 (ascending links in Y = K_{<=m+1})

Put `n = m+1`. Let `γ` be a vertex of `Y` with hidden set `S`, `|S| = k <= n`, and visible set `V = sing(G) \ S`.

**The link.** A cube containing `γ` is given by:

- a finite set `R ⊆ S` of coordinates to reveal, with a germ chosen at each;
- a finite set `D ⊆ V` of coordinates to hide.

The largest number of `*` on the cube is `k + |D|`, so the cube lies in `Y` iff `|D| <= n − k`. Hence
`lk_Y(γ) = (join_{p in S} Bgerm(G,p)) * Skel_{n−k−1}(Δ_V)`, where each `Bgerm(G,p)` is discrete and `Δ_V` is the full
simplex on `V`. This is the computation in the proof of (Conn), extended to visible coordinates.

**The ascending link.** It is the full subcomplex on the ascending neighbours (ML), so
`lk↑(γ) = (join_{p in S} A_p) * Skel_{n−k−1}(Δ_{V↑})`, where:

- `A_p = {β in Bgerm(G,p) : τ(β) > 0}`;
- `V↑ = {q in V : τ(γ(q)) < 0}`.

**Nonempty factors.**

- `A_p != ∅`. By (P2), `G·p` contains a `B`-orbit `B·g(p)` with `ν > 0`, and `β = (Bg)_p` has `τ(β) = ν(g(p)) > 0`.
- `V↑` is infinite. By hypothesis 4 the orbit `Ω_−` of (P3) is infinite. All but finitely many of its points are
  visible in `γ` with trivial germ, and the trivial germ at `q` has `τ = ν(q) < 0`.

**Connectivity.**

- A join of `k` nonempty discrete sets is `(k−2)`-connected (Milnor). For `k = 0` it is empty, which is `(−2)`-connected.
- The `(n−k−1)`-skeleton of a simplex with at least `n−k+1` vertices is `(n−k−2)`-connected.
- `conn(A * B) >= conn(A) + conn(B) + 2`.

So `lk↑(γ)` is `(n−2)`-connected, that is `(m−1)`-connected, for every vertex `γ` of `Y`.

## Step 6 (conclusion)

**Morse Lemma.** Apply (ML) to `Y` with `(H,0)`, `p = −∞`, `r = +∞` and any `q in R`. All ascending links are
`(m−1)`-connected, so the pair `(Y, Y_{q<=H})` is `m`-connected. By (Conn), `Y = K_{<=m+1}` is `m`-connected. Hence
`π_i(Y_{q<=H}) ≅ π_i(Y) = 0` for `i < m`, and `Y_{q<=H}` is nonempty. So every `Y_{q<=H}` is `(m−1)`-connected, and the
filtration is essentially `(m−1)`-connected.

**Bux–Gonzalez.** Check the hypotheses of (BG) for `G` acting on `Y`:

- `G` has type `F_m` by Step 0.
- `Y` is `(m−1)`-connected.
- By (Stab) and hypothesis 3, every cube stabilizer has a finite-index subgroup conjugate to `Fix_B(M')` with
  `|M'| <= m+1`. That subgroup has type `F_m` by hypothesis 2, so the stabilizer has type `F_m`, hence type `F_{m−k}`.
- By (Orb) and hypothesis 1 there are finitely many orbits of cubes. The cubes of `Y` have dimension at most `m+1`,
  because the vertex hiding every varying coordinate carries that many `*`. So the action on `Y^{(m)}` is cocompact.
- `H` is continuous with `H(gy) = χ(g) + H(y)`.

So (BG) gives `[χ] in Σ^m(G)`. The corollary is the Bieri–Renz criterion: every `χ` vanishing on `N` vanishes on `B`,
so it lies in `Σ^m(G)`. ∎

## Model tests

- **Thompson's `F` over `F'`.** Hypotheses 3 and 4 fail, and Step 2 fails: `φ_0 = χ_0|_{(F)_0} != 0`. The conclusion
  is false: one of `[±χ_0]` lies outside `Σ^1(F)` (Witzel–Zaremsky Theorem A), while the theorem would put both in.
- **Binary odometer, `Γ = V_2(Z)`, `a = σ(1,a)`.** Take `B = V_2`, `χ(a) = 1`, as in
  `rover-nekrashevych-characters-are-sum-invariant`.
  - `sing(a) = {1^∞}` and `a(1^∞) = 0^∞`. So `sing(Γ)` is one `Γ`-orbit made of the two `V_2`-orbits (tail classes)
    of `1^∞` and `0^∞`.
  - `c((Ba)_{1^∞}) = 1`, so `ν(1^∞) = κ` and `ν(0^∞) = κ − 1`. The choice `κ = 1/2` gives `ν = ±1/2`.
  - At the basepoint vertex no coordinate is hidden. The ascending link is the `m`-skeleton of the simplex on the tail
    class of `0^∞`, which is infinite and `(m−1)`-connected, as the proof requires.

---
rg: 2
id: substitution-inflation-hosts-contracting-rsg-proof
kind: route
title: Proof that the translation-plus-inflation full group of a recognizable primitive aperiodic box substitution is a full contracting RSG on the collared hierarchy shift, via a carry calculus in which every deep local action is a one-level translation by a vector in {-1,0,1}^d
target: substitution-inflation-hosts-are-full-contracting-rsgs
requires:
  - labbe-substitution-is-primitive-and-recognizable
  - free-sft-hosts-admit-no-finite-type-coding
  - fp-v-times-subshift-full-groups-force-quantum-rigidity
  - contracting-rsgs-embed-in-fp-simple-groups
  - hyperbolic-groups-lie-in-the-permutational-class
---

Notation is as on the claim. BBMZ means arXiv:2309.06224v3, local TeX `$GQ/src/bh-free-03/bbmz2-2309.06224.tex`.
The following were read there:
- local actions `f|_α` and `f̄(α)` (l.335);
- rational maps (l.363);
- irreducible core (l.514);
- RSG, and `prop:RSGsAndV` (l.637–643): with an irreducible core, every subgroup of `R_Γ` containing `V_Γ` is an
  RSG;
- full (l.557);
- nucleus and contracting (`def:contracting`, l.695);
- `thrm:fin_pres` (l.840): every full, contracting RSG is finitely presented;
- `prop:contr_to_simple` (l.1752).

For a pattern `π` on `[-1,1]^d`, `[π] ⊆ X_ω` is its cylinder. Write `coll(x) := x|_([-1,1]^d)`.

## Step 0: the carry rule

Fix `y ∈ X_ω`. Its image boxes `R_z(y)` (the box of `y(z)` inside `ω(y)`) form a product grid, and
`R_0(y) = R(y(0))`. Two facts:
- `S^(corner R_c(y)) ω(y) = ω(S^c y)`;
- the width of `R_c(y)` along axis `i` is `s_i(y(c))`, and it depends only on `c_i`.

For `p ∈ R_0(y)` and `v ∈ Z^d`, let `R_c(y)` be the box containing `v + p`, and put
`q = v + p − corner R_c(y)`. Then

> **(C)** `t_v ι_p (y) = S^(v+p) ω(y) = S^q ω(S^c y) = ι_q (t_c y)`.

Write `(c, q) = carry(y, v, p)`.
- By (H4) every box has width at least 2, so `|c|_∞ <= ⌈|v|_∞ / 2⌉`. Iterating (C) along a hierarchy, carries
  drop to `{-1,0,1}^d` after at most `log_2 |v| + 1` levels and stay there.
- For `|v|_∞ <= 1`, the pair `(c, q)` depends only on `coll(y)` and `p`.

**Side lemma.** Suppose `(c, q) = carry(y, c′, p)` with `|c′|_∞ <= 1`. Then for each axis `i`:
- if `c_i = +1`, then `q_i = 0`;
- if `c_i = −1`, then `q_i = s_i(y(c)) − 1`.

*Proof.* If `c_i = +1`, then `c′_i + p_i >= s_i(y(0))` with `c′_i <= 1` and `p_i <= s_i(y(0)) − 1`. So both are
equalities and `q_i = 0`. If `c_i = −1`, then `c′_i + p_i < 0`, so `c′_i = −1` and `p_i = 0`. So the cell is the
last one of the box of `y(c)` along `i`. ∎

## Step 1: the collared hierarchy shift

For `π′` a node of `Γ` and `p ∈ R(π′(0))`, put `child(π′, p) = ω(π′)|_(p+[-1,1]^d)`. This is defined because every
neighbour of a cell of `R_0` lies in some `R_u` with `|u|_∞ <= 1`.

**Locality.** Let `U(p)` be the set of `u` with `R_u(π′) ∩ (p + [-1,1]^d) ≠ ∅`. Then `child(π′, p)` depends only
on `π′|_(U(p))`. By (H4), along axis `i` the index `u_i` lies in:
- `{-1, 0}` when `p_i = 0`;
- `{0, 1}` when `p_i = s_i − 1`;
- `{0}` otherwise.

**The map Φ.** For `x ∈ X_ω`, (H3) gives `x_0 = x` and `x_n = ι_(p_n)(x_(n+1))`. Put
`Φ(x) = e_0 e_1 ⋯` with `e_n = (coll(x_n), p_n, coll(x_(n+1)))`. These are edges of `Γ`, because
`coll(x_n) = child(coll(x_(n+1)), p_n)`.
- **Continuous.** `{(x, y, p) : x = S^p ω(y)}` is closed and, by (H3), the graph of a function on a compact space.
  So `x ↦ (x_1, p_0)` is continuous.
- **Injective.** `x = S^(P_n) ω^n(x_n)`, and `ω^n(coll(x_n))` covers a ball of radius `2^n` around the origin by
  (H4). So the first `n` edges determine `x` on that ball.
- **Surjective.**
  - Take a path `(π_n, p_n)`, with `π_n = child(π_(n+1), p_n)`.
  - Let `W_n` be `ω^n(π_n)`, shifted so that the cell with positions `p_0, …, p_(n−1)` is the origin.
  - `W_n` is legal by (H1), its domain contains `B(0, 2^n)`, and `W_(n+1)` extends `W_n`, since `ω^n` of a child
    is a restriction of `ω^(n+1)` of the parent.
  - The union is some `x ∈ X_ω`. The same construction from level 1 gives `x_1 ∈ X_ω` with
    `x = S^(p_0) ω(x_1)`.
  - By uniqueness in (H3), this is the decomposition of `x`. Induction gives `Φ(x) =` the path.
- So `Φ` is a homeomorphism. Also `Φ(ι_p y) = (child(π′, p), p, π′)·Φ(y)` for `y ∈ [π′]`, so `ι_p|_([π′])` is the
  canonical similarity `L_e`, which prepends the edge `e`. Iterating, `L_α` corresponds to
  `ι_(P_α)|_([t(α)])`, where `P_α` is the position word of `α`.

**Irreducible.**
- A legal `π` occurs in some `ω^N(a)` by (H1).
- `a` occurs in `ω^M(b)` for every letter `b`, by primitivity.
- So `π` occurs in `ω^(N+M)(π″(0))`, with its centre in the central box. This is a path from `π` to `π″` in `Γ`.
- `Σ_Γ ≅ X_ω` is infinite, so `Γ` is not a cycle.

So `Σ_Γ` is irreducible. It is its own irreducible core, and it is a Cantor space with no empty cones.

## Step 2: germs and the full group

Let `𝒮` be the set of partial maps `ι_(P′) t_v ι_P^(−1)`, where `P, P′` are position words and `v ∈ Z^d`.
- `𝒮` contains the generators `t_v` and `ι_p`.
- It is closed under inversion, since `(ι_(P′) t_v ι_P^(−1))^(−1) = ι_P t_(−v) ι_(P′)^(−1)`.

It is closed under composition at the level of germs. At a point, one of `P` and `R′` is a prefix of the other,
because both are prefixes of the same point's position word.
- **If `R′ = P R″`.** Then `ι_P^(−1) ι_(R′) = ι_(R″)`, and (C) along `R″` gives `t_v ι_(R″) = ι_(R‴) t_c`.
- **If `P = R′ P″`.** Write the point as `ι_Q(a′)` with `|Q| = |P″|`. Then (C) and uniqueness give
  `t_w ι_Q = ι_(P″) t_c`, so `ι_(P″)^(−1) t_w = t_c ι_Q^(−1)`.

Either way the composite is again in `𝒮`. So **every germ of `𝒢⁺` is a germ of some `ι_(P′) t_v ι_P^(−1)`.**

By Step 1 a canonical similarity `C_α → C_β` is `ι_(P_β) ι_(P_α)^(−1)`. So `V_Γ ≤ F(𝒢⁺)`. `F(𝒢⁺)`, the group of
all homeomorphisms with germs in `𝒢⁺`, is full in BBMZ's sense.

## Step 3: deep local actions

Let `g ∈ F(𝒢⁺)`.
- Refine its pieces to a finite cone partition `{C_β}`. By Step 2 and (C), `g = ι_(P′_β) t_(v_β) ι_(P_β)^(−1)` on
  `C_β`.
- Make the partition deep enough that the carries of `v_β` are uniform on `C_β`.
  - A carry `c_j` at level `j` depends on the level-`j` configuration within distance `|c_j|_∞ + 1`.
  - A cone of depth `n` fixes the level-`j` configuration on a ball of radius at least `2^(n−j)`.
  - The carries decrease geometrically, so large `n` suffices.
- Take `α = βγ`, where `|γ| >= 2 + log_2 max |v_β| + 1`, and put `π = t(α)`.
- For `y ∈ [π]`, (C) along `γ` gives `g(L_α y) = ι_Q(t_c y)`. Here `|c|_∞ <= 1`, and `Q = P′_β P″` ends with a
  position `q` produced by a carry from `|c′| <= 1`.
- By the side lemma, `q` is consistent with `c`.

**Determinacy.** `child(coll(t_c y), q)` depends only on `π`.
- By locality, it uses `(t_c y)(u) = y(u + c)` for `u ∈ U(q)`, and the box widths of those letters.
- By the side lemma, along axis `i` the needed `u_i` lie in `{-1, 0}` when `c_i = +1`, in `{0, 1}` when
  `c_i = −1`, and in `{-1, 0, 1}` when `c_i = 0`.
- So `u + c ∈ [-1,1]^d`, which is inside `π`.

The higher output collars are `coll_i = child(coll_(i+1), q_i)` along `Q`. So all output edges except the last one
of `Q` are independent of `y ∈ [π]`. Hence

`Φ(g L_α y) = η · F_(π,c,q)(y)`, with `F_(π,c,q)(y) := Φ(ι_q t_c y)` and `η` fixed.

So `g|_α = strip(F_(π,c,q))`, where `strip(F) = L_κ^(−1) ∘ F` and `κ` is the greatest common prefix of `F(C_π)`.

Let `𝒩 = { strip(F_(π,c,q)) : π ∈ Γ, c ∈ {-1,0,1}^d, q in a box }`. This is a finite set. For `c = 0`,
`F_(π,0,q) = L_e`, and its strip is `id_(C_π)`.

All but finitely many `α` are of the form above, so all but finitely many local actions of `g` lie in `𝒩`. Hence:
- `g` has finitely many local actions, so it is **rational**;
- `Nuc_g ⊆ 𝒩`.

## Step 4: conclusion

- `F(𝒢⁺) ≤ R_Γ` by Step 3. It contains `V_Γ` (Step 2), and `Σ_Γ` has an irreducible core (Step 1). So it is an RSG
  by `prop:RSGsAndV`.
- It is full (Step 2), and `Nuc_(F(𝒢⁺)) = ⋃_g Nuc_g ⊆ 𝒩` is finite. So it is contracting (`def:contracting`).
- It is finitely presented by `thrm:fin_pres`.
- It embeds in a finitely presented simple group by `prop:contr_to_simple`.
- It is a type (A) actor by the "full, contracting RSG" read-off in `hyperbolic-groups-lie-in-the-permutational-class`.
- `v ↦ t_v` embeds `Z^d`, freely on `X_ω` by (H2).

**Item 4 of the claim.**
- Freeness and item (4a) of `free-sft-hosts-admit-no-finite-type-coding` show that the labelled host has no finite
  coding.
- `F(G_V × (Z^d ⋉ X_ω))` contains the `t_s`, the `e_a` and `V × 1`. So part 2 of
  `fp-v-times-subshift-full-groups-force-quantum-rigidity` makes finite presentation imply finite type.
- A nonempty `Z`-SFT has periodic points, so for `d = 1` the aperiodic `X_ω` is never of finite type.
- **A contracting loop of `𝒢⁺`.** Take `π` and a corner position `p` with `child(π, p) = π`. Such a pair exists
  for some power of `ω` by pigeonhole along corner paths. Then `ι_p` maps `[π]` into itself with mesh tending to
  0, and its limit point is a fixed tiling of `S^p ω`. ∎

## Step 5: Labbé's instance

- **Morphism.** `ω = α∘β∘γ` from `labbe-substitution-is-primitive-and-recognizable`. It is a 2-dimensional
  morphism, its images of legal configurations are product grids, and `Ω_U = X_ω` (item 4 there).
- **Recognizability.** The node's item 1 (Labbé `prop:pre-main`) says that `ω` is recognizable in `Ω_U` and
  that `Ω_U` is the union of the four shifts of `ω(Ω_U)`. This is (H3) for `ω`.
  - *Caveat.* The exact definition of "recognizable" in the source TeX was not re-read by this lane; the standard
    one is unique `(y, k)`.
  - *Powers.* (H3) passes to `ω^8` by composing unique decompositions.
- **Other hypotheses for `ω^8`.**
  - (H1): primitivity of `ω` gives primitivity of `ω^8` and `X_(ω^8) = X_ω`.
  - (H2): `Ω_U` is aperiodic (node item 4).
  - (H4): Step 2 of `research/artifacts/un-labbe-ring-substitution-complexity-2026-09-13.md`, a lane proof, gives
    `shape(ω^8(a)) >= (2, 2)` for every letter.

**Trust surface.**
- The BBMZ statements listed at the top.
- Recognizability: imported for Labbé; Mossé's theorem for `d = 1`, not re-read.
- Everything else is elementary and proved above.

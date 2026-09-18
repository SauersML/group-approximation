---
rg: 2
id: bs-chain-configurations-exist-in-finite-germ-extensions-of-v
kind: claim
title: A finitely generated finite germ extension of Thompson's V with two singular orbits of rational points contains a Baumslag-Solitar chain configuration, realized tamely by translation, dilation and a dyadic square map on the extended line
distinct_from:
  higman-chain-group-pbh-iff-chain-configuration: that reduces BH for the chain G_1 (and so a necessary step for H4 and BG) to finding a chain configuration in some B_A group, and records where configurations cannot live; this exhibits one in an explicit finitely generated finite germ extension of V, so what remains is only that this host (or a relative of it) is in B_A.
  tame-power-conjugators-have-more-hyperbolic-points: that shows fixed-point sets strictly grow along proper-power conjugations of tame homeomorphisms, which kills cycles such as H4 and BG in tame hosts; this shows chains of length two survive that obstruction and are realized by tame elements.
  piecewise-analytic-circle-square-conjugate-has-parabolic-ends: that forbids square-conjugate elements with finitely many analytic pieces from having non-parabolic fixed points; here the conjugator necessarily has infinitely many pieces, accumulating exactly at its singular points.
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no priority claimed).

## Setting

Let `X` be the Cantorized extended line `[-∞, +∞]`: the integer blocks `[n, n+1)` are coded by their binary fractions, with block `n ≥ 0` at address `1^(n+1) 0 C`, block `-m` (`m ≥ 1`) at `0^m 1 C`, and `+∞ = 1^∞`, `-∞ = 0^∞`. So `X` is the Cantor set `C = {0,1}^N`, every dyadic rational is doubled (`q^-`, `q^+`), and a dyadic PL map with dyadic breakpoints and slopes in `2^Z` is locally a prefix replacement at every point where it has finitely many pieces nearby. Let `V` act on `X = C` as usual.

Three homeomorphisms of `X`:
- `c(x) = x + 1`. In the coding, `c` is `00v ↦ 0v`, `01w ↦ 10w`, `1v ↦ 11v`, an element of Thompson's `F`.
- `b(x) = 2x`. It fixes `0^±` and `±∞`.
- `a` is the odd dyadic square map: `a(0) = 0`, `a(-x) = -a(x)`, `a(2x) = 4 a(x)` for all `x`, and on `[1,2)`: `a(x) = 2x - 1` on `[1, 3/2)`, `a(x) = 4x - 4` on `[3/2, 2)`. It is dyadic PL on `(0, ∞)` with breakpoints exactly at `3·2^(j-1)`, `j ∈ Z`, accumulating only at `0` and `∞`.

## Statement

1. **Chain configuration.** `a b a^-1 = b^2` and `b c b^-1 = c^2`, and `c` has infinite order. In the convention of `higman-chain-group-pbh-iff-chain-configuration` (`a^-1 b a = b^2`, `b^-1 c b = c^2`) the configuration is `(a^-1, b^-1, c)`.
2. **The host.** `Γ = ⟨V, a, b⟩`, and its full closure `Γ̄` (all homeomorphisms locally agreeing with elements of `Γ`), are finite germ extensions of `V` in the sense of Belk–Hyde–Matucci (arXiv:2407.03149).
   - `sing(b) = {+∞, -∞}` and `sing(a) = {0^+, 0^-, +∞, -∞}`.
   - `sing(Γ̄) = O_0 ∪ O_1`, the two `V`-orbits of rational points with tails `0^∞` (containing `-∞`, `0^+`) and `1^∞` (containing `+∞`, `0^-`).
   - `Γ̄` is full and clopen transitive, since it contains `V`.
3. **Germ groups.** At `+∞`, in annulus coordinates (block `n`, content `w ∈ C`):
   - the `V`-germs are `⟨σ⟩`, `σ = [c]: (n, w) ↦ (n+1, w)` (the zoom);
   - `δ = [b]: (n, xw) ↦ (2n + x, w)` (index doubling);
   - `s = [a]`, with `s δ s^-1 = δ^2` and `δ σ δ^-1 = σ^2`;
   - the germ of `a` at `0^-`, moved to `+∞` by the prefix replacement `01u ↦ 1u`, is exactly `δ`.

   So `(Γ̄)_(+∞) = ⟨σ, δ, s⟩`, a quotient of `G_1 = ⟨s,δ⟩ *_⟨δ⟩ ⟨δ,σ⟩` in which both `BS(1,2)` factors are faithful. The same holds at `-∞`, where the moved germ of `a` at `0^+` (by `10y ↦ 0y`) is exactly the germ of `b`.
4. **Tame and zero entropy.** Every element above wanders off a finite set.
   - The fixed sets are `F_c = {±∞}`, `F_b = {0^±, ±∞}` and `F_a = {0^±, 1^±, (-1)^±, ±∞}`, so `F_c ⊊ F_b ⊊ F_a`, exactly as `tame-power-conjugators-have-more-hyperbolic-points` demands.
   - All topological entropies are zero, consistent with `homogeneous-conjugation-invariants-vanish-on-bs-bases`.
5. **Consequence.** By `higman-chain-group-pbh-iff-chain-configuration` and `fp-clopen-transitive-full-cantor-groups-have-type-a-actions`, if `Γ̄` is finitely presented then `G_1 ∈ B_A`. Then `G_1` embeds in a finitely presented simple group, and the common vertex group of H4 and the base of BG pass their first test.

## Proof

- **Relations.** `a(2x) = 4a(x)` gives `a∘b = b^2∘a`. And `b(x+1) = 2x + 2 = c^2(b(x))` gives `b∘c = c^2∘b`.
- **Local form.** `a` and `b` are dyadic PL, with finitely many pieces near every point outside their fixed accumulation points. So they are locally prefix replacements there. At `±∞` (and at `0^±` for `a`) the index map of their germ is unbounded relative to `V`'s shifts, so they are singular. Checking the finite germ extension axioms is routine; the full closure satisfies BHM axiom (3) by gluing with `V`.
- **Germs.**
  - `b` maps block `n = [n, n+1)` to blocks `2n, 2n+1` by `n + 0.xw ↦ 2n + x + 0.w`.
  - Near `0^-`, `a` maps the annulus `[-2^(-k), -2^(-k-1))` (address `0 1^(k+1) 0 w`) to annuli `2k, 2k+1`. A direct computation from the two pieces of `a|[1,2)` gives `(k, xw) ↦ (2k + x, w)`.
  - The prefix replacement `01u ↦ 1u` matches annulus `k` at `0^-` with block `k` at `+∞`, content preserved. So the moved germ is `δ`.
  - Every non-`V` germ in the orbit `O_1` is one of these, so the isotropy of the germ groupoid at `+∞` is `⟨σ, δ, s⟩`. The `-∞` side is the mirror computation.
- **Faithful factors.** A quotient of `BS(1,2)` in which the base has infinite order is faithful (a nonzero ×2-invariant subgroup of `Z[1/2]` contains a power of the base). Here the bases `σ` and `δ` have infinite order as germs.
- **Fixed sets.** `a(x) = x` only at `x = 0, ±1`, because `a(y) > y` on `(1, 2)`.

## Lesson for general BH

A chain of Baumslag–Solitar squarings is a **tower of coordinate changes** at one point. Level 0 is a translation (`x+1`), level 1 a dilation (`2x`, a translation in `log x`), and level 2 a square map (a dilation in `log x`). Each level's stable letter is the next level's base.

Tame (wandering) elements make fundamental domains available. So the tower closes up with finitely many singular points, and the dyadic square map is PL off `{0, ±∞}`.

Two things break this:
- **Cycles.** They fail by the fixed-set growth law. For H4 and BG a host needs non-tame, zero-entropy renormalizable elements.
- **Minimal (odometer-like) bases.** They force positive-entropy conjugators.

So every attempt on the H4 and BG vertex group lands in the germ group at one rational point. There the whole question is finite presentation (`bhm-singfix-condition-forces-fp-germ-groups`). See `scale-periodic-bs-chain-germ-representations-are-not-faithful` for why this germ group is not `G_1` itself, and `zoom-tower-germ-groups-give-f-infinity-germ-extensions` for the finiteness engine that would apply if it were.

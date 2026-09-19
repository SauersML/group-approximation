---
rg: 2
id: shortlex-adjacent-refinement-fails-for-a-virtually-free-racg
kind: claim
title: One-level (indeed any bounded-level) refinement of ShortLex descent trees at adjacent bases fails for a virtually free right-angled Coxeter group with a suitable generator order, so hypothesis (M1) of the far-base node is a property of the ordered generating set, not a consequence of hyperbolicity; the obstruction is a late large letter that commutes with a blocked infinite word
requires:
  - shortlex-far-base-finiteness-is-the-contracting-lemma
distinct_from:
  shortlex-far-base-finiteness-is-the-contracting-lemma: that derives rationality and the contraction criterion from (M1); this shows (M1) can fail for hyperbolic groups, so that node stays conditional.
  shortlex-cone-tiles-certify-upstream-leaving-crossing: that proves exact cone tiles (true for every group); this concerns the relation between trees at different bases, which needs more.
---

**ESTABLISHED** (lane proof, bh-finf-hyp, 2026-09-19; elementary; not reviewed).
- Inputs: Moussong's hyperbolicity criterion for right-angled Coxeter groups (no induced 4-cycle), and the
  Anisimov–Knuth lexicographic normal form of traces, which is the ShortLex normal form here. Both are recalled.

## The group

- **Graph `Λ`.** The tree on vertices `u, v, y, s, r` with edges `y–u`, `y–v`, `y–s` and `s–r`.
- **Group.** `W = W_Λ`: generators are involutions, and adjacent generators commute.
- **Order.** `u < v < y < s < r`.
- **Properties.**
  - `Λ` has no cycles, so `W` is hyperbolic (Moussong) and virtually free (`Λ` is chordal).
  - `W` has no nontrivial finite normal subgroup, since no vertex is adjacent to all others.

## ShortLex in `W`

- A reduced word is a linearization of a trace: a poset of letter occurrences in which non-commuting occurrences
  are ordered.
- `SL(g)` is the greedy linearization: repeatedly write the smallest minimal letter. (Lexicographically least,
  by Anisimov–Knuth.)

## Theorem

Put `g_N = (uv)^N y` and `g'_N = (uv)^N`. Then:
1. `SL(g_N) = (uv)^N y` and `SL(g'_N) = (uv)^N`. These agree on their first `2N` letters.
2. `SL(s g_N) = y s (uv)^N` and `SL(s g'_N) = s (uv)^N`. These differ in the first letter.
3. So in the notation of `shortlex-far-base-finiteness-is-the-contracting-lemma`, the depth-1 tiles of `𝒯_s`
   containing `g_N` and `g'_N` differ, although their `𝒯_1`-addresses agree to depth `2N`.
   - The limit points `P = lim g_N` and `P' = lim g'_N` of `Ω` are distinct: their letters at the site `s` are
     `y` and `s`.
   - Yet `P` and `P'` lie in the same `𝒯_1`-tile at every depth, both on the ray `(uv)^∞`.
   - Hence no depth-1 tile of `𝒯_s` is a union of `𝒯_1`-tiles near `P`. (M1) fails, even with any bounded
     delay `D` in place of one level, and the `𝒯_1`-tiles are not a basis of `∂Ω`.

## Proof

1. **`g_N`.**
   - `y` commutes with `u` and `v`, so it is minimal in the trace of `(uv)^N y`. The occurrences of `u` and `v`
     alternate, since they do not commute.
   - Greedy choice: at every step the available letters are the next one of `u, v` and `y`. Since `u, v < y`,
     `y` is written last.
2. **`s g_N`.**
   - `s` commutes with `y` but not with `u` or `v`, and `s` is not a left descent of `g_N` (no `s` occurs). So
     the trace of `s g_N` puts `s` below every `u` and `v`, while `y` stays minimal.
   - The first available set is `{s, y}`, and `y < s`, so `y` comes first. Then `s`, then `(uv)^N`.
   - For `s g'_N` the first available set is `{s}`.
3. **Tiles and limits.**
   - The depth-1 tile of `𝒯_s` containing `g` is read from the first letter of `SL(s^{-1}g) = SL(sg)`.
   - The letter fields converge sitewise, because `SL(x^{-1}g_N)` stabilizes letter by letter for fixed `x`.
     That gives distinct limits differing at `s`.
   - The `𝒯_1`-tile of depth `k ≤ 2N` of either element is read from the first `k` letters of `SL`. ∎

## The mechanism

- **The pattern.** A letter `y` stays available, because it commutes with a long word, but is postponed because
  that word's letters are smaller. Left multiplication by an `s` that commutes with `y` and blocks the word then
  brings `y` to the front.
- **Why hyperbolicity does not exclude it.** The configuration needs `y` to centralize an infinite subgroup
  `⟨u, v⟩`. That is allowed in hyperbolic groups: `⟨u,v,y⟩ ≅ D_∞ × Z/2` is virtually cyclic.
- **Why the tested groups passed.** In the right-angled pentagon group the link of each vertex is two
  non-adjacent vertices, so `s` cannot also commute with `y`. The (4,4,4) group has no commuting generators.
- **The order matters.** With `y` smallest, `y` is never postponed, and this configuration disappears. Whether a
  good order always exists is open.

## Consequences

- `shortlex-far-base-finiteness-is-the-contracting-lemma` **stays conditional** on (M1) for the chosen ordered
  generating set. It cannot be made unconditional for all hyperbolic groups and orders.
- The right hypothesis is **bounded left delay**: there is `D` such that the first `n` letters of `SL(s g)`
  depend only on the first `n + D` letters of `SL(g)`. With this, Lemma 2 and Theorem 3 of that node hold with
  losses of `D` per step.
- Without it, `∂Ω` (the letter-field model, a factor of `∂_h Γ`) is still a Γ-space. But a single descent tree no
  longer gives coordinates, and the RSG structure of that node is lost.

## Lesson for general BH

A canonical combing is canonical only from one side. ShortLex is a right-multiplication structure. Left
multiplication, the group action on the boundary, can need unbounded look-ahead, already in a virtually free
group. So any coding that reads addresses from one base must prove bounded left delay for its order. This is
not a hyperbolicity statement. Horofunction atoms avoid the issue by being two-sided (distance functions), at the
price of branching.

## Next

- Find a sufficient condition on `(S, <)` for bounded left delay. For RACGs, a candidate is: no generator is
  larger than a letter of an infinite special subgroup it centralizes while being blocked by another centralizing
  generator.
- Decide whether every hyperbolic group admits some finite generating set and order with bounded left delay.

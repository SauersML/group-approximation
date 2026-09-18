---
rg: 2
id: linear-activity-odometer-automaton-has-fp-nekrashevych-group
kind: claim
title: The linear-activity automaton a = σ(1,a), b = (a,b) has every relator splitting freely, so its non-contracting group has a finitely presented Nekrashevych group and satisfies Boone–Higman
distinct_from:
  spinal-extensions-of-lift-presented-groups-satisfy-boone-higman: that needs the loop letter fixed by every state; here the base generator a moves the loop letter of b, and a descent argument replaces compression.
  rover-nekrashevych-group-of-lamplighter-automaton-is-fp: that is another automaton with N = K_∞ (the lamplighter, exponential activity); this is a linear-activity example over an odometer base.
---

**ESTABLISHED** (lane proof below via `relator-complexity-descent-gives-free-splitting`; not yet refereed; no
priority claimed; whether Boone–Higman for this group was known by other means was not checked).

## The automaton

`X = {0,1}`; `u = π(u_0,u_1)` means `u(0w) = π(0)u_0(w)`, `u(1w) = π(1)u_1(w)`. Let `a = σ(1,a)` (the odometer)
and `b = (a,b)`; `S = {1, a^{±1}, b^{±1}}`, closed under sections and inverses, `G = ⟨a,b⟩`.

## Statement

1. `G` has linear activity and is not contracting.
2. Every relator of `G` becomes freely trivial after finitely many splittings: `N = K_∞`.
3. So `V_2(G)` is finitely presented, and `G` embeds in a finitely presented simple group.

## Proof

**Letter rules.** For a letter `ℓ` receiving the point `p` (the letter to its right outputs `p`; the rightmost
letter receives the vertex `x`), the section and the output point are:

| letter | at `p = 0` | at `p = 1` |
|---|---|---|
| `a` | section `1`, output `1` | section `a`, output `0` |
| `a^{-1}` | section `a^{-1}`, output `1` | section `1`, output `0` |
| `b` | section `a`, output `0` | section `b`, output `1` |
| `b^{-1}` | section `a^{-1}`, output `0` | section `b^{-1}`, output `1` |

(From `a(0w) = 1w`, `a(1w) = 0a(w)`, `b(0w) = 0a(w)`, `b(1w) = 1b(w)`.)

**Complexity.** For a reduced word `w` let `c(w) = (β(w), α(w))`, ordered lexicographically, where `β` counts
letters `b^{±1}` and `α` counts letters `a^{±1}`. By the table, `β(red(w|_x)) <= β(w)`, with equality only if
every `b^{±1}` receives `1`. If so, `b`-letters give `b`-letters, and `α(red(w|_x)) <= α(w)`, with equality only
if every `a` receives `1` and every `a^{-1}` receives `0`, with no cancellation.

**Equality forces a special word.** Suppose `c(red(w|_x)) = c(w)` for a reduced `w`.
- An `a` outputs `0`. Its left neighbour would receive `0`, which is forbidden for `b^{±1}` and for `a`, and
  `a^{-1}a` is not reduced. So an `a` is the leftmost letter.
- An `a^{-1}` must receive `0`. Only an `a` outputs `0` among allowed letters, and `a^{-1}a` is not reduced, so
  an `a^{-1}` is the rightmost letter (with `x = 0`).
- So `w in {b^e, a b^e, b^e a^{-1}, a b^e a^{-1} : e in Z}`.

**No special word is a nontrivial relator.** `b` has infinite order (`b^e = (a^e, b^e)` and `a` has infinite
order). `b` fixes `1^ω` and `a^{±1}` moves it, so `a b^e ≠ 1` and `b^e a^{-1} ≠ 1`; and `a b^e a^{-1} = 1`
forces `e = 0`. So every nontrivial relator drops in complexity at both sections, and
`relator-complexity-descent-gives-free-splitting` gives `N = K_∞` and (3).

**(1).** `a` is bounded (one nontrivial section per level), and `b|_{1^k 0} = a`, `b|_{1^k} = b`, so `b` has
`O(n)` nontrivial sections at level `n`. `b^e|_1 = b^e` for all `e`, and these are infinitely many distinct
elements, so no finite nucleus exists.

## Significance

The base `⟨a⟩` moves the loop letter of `b`, so `commonly-fixed-letters-compress-to-faithful-actions` and
`spinal-extensions-of-lift-presented-groups-satisfy-boone-higman` do not apply; descent does. This was the
sharpest open test recorded in the spinal node.

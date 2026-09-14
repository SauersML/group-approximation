---
rg: 2
id: arrow-shift-strict-automata-proof
kind: route
title: Double a Følner-failing window by Hall matching, copy along the arrows, and count preimages on finite coset spaces
target: nonamenable-groups-carry-arrow-shift-strict-automata
requires: []
artifacts:
  - research/artifacts/ideas-gottschalk-2-2026-09-14.md
---

Notation is as in the target claim. Right multiplication commutes with the
left action, so `X_S` is `G`-invariant. Membership of `φ` is checked at each `h`
on the window `h S^(-1)`, so `X_S` is of finite type.

**Imports.**
- **(F) Følner's criterion.** `G` is amenable iff for every finite `K` and
  every `ε > 0` there is a finite nonempty `F` with `|FK| < (1+ε)|F|`.
- **(H) Marshall Hall, 1948.** A family of finite sets has a system of distinct
  representatives iff every finite subfamily of size `r` has a union with at
  least `r` elements.

**Step 1: a doubling window.**
- Suppose `G` is nonamenable. By (F) there are a finite `K` containing `e` and
  an `ε > 0` with `|FK| >= (1+ε)|F|` for every finite nonempty `F`.
- Applying this to `FK^(j-1)` gives `|FK^j| >= (1+ε)^j |F|`.
- Choose `j` with `(1+ε)^j >= 2` and put `S = K^j ∪ (K^j)^(-1)`. Then `e in S`,
  `S = S^(-1)`, and `|FS| >= 2|F|` for all finite `F`.

**Step 2: nonemptiness.**
- The targets are `T = G × {1,2}`, and target `(h, i)` has candidate set
  `N(h,i) = hS`. Each candidate set is finite.
- Take a finite set of targets with projection `F`. It has at most `2|F|`
  elements, and its candidates form `FS`, with `|FS| >= 2|F|`. So Hall's
  condition holds.
- By (H) there is an injective `r : T -> G` with `r(h,i) in hS`.
- Define `φ(g) = g^(-1) h` if `g = r(h,i)`. Since `S = S^(-1)`, this lies in
  `S`. Define `φ(g) = e` for `g` outside the image of `r`.
- Then `r(h,1) != r(h,2)` both satisfy `g φ(g) = h`, so `φ` lies in `X_S`.

**Step 3: amenable groups have empty arrow shifts.**
- Let `φ` be in `X_S` and let `F` be finite and nonempty.
- Distinct points have disjoint preimages, and `f_φ^(-1)(F) <= F S^(-1) = FS`.
  So `|FS| >= 2|F|` for every `F`.
- By (F) with `K = S` and `ε = 1/2`, `G` is nonamenable. This proves (1).

**Step 4: the hotel map.**
- Put `Ψ_φ(x)(g) = x(g φ(g))`.
- **Block map.** The value at `g` depends only on `φ(g)` and on `x` restricted
  to `gS`.
- **Equivariance.**
  `Ψ_(k.φ)(k.x)(g) = x(k^(-1) g φ(k^(-1) g)) = (k.Ψ_φ(x))(g)`.
- **Injective.** Every `h` has a preimage under `f_φ`. So `Ψ_φ(x) = Ψ_φ(x')`
  forces `x(h) = x'(h)` for all `h`.
- **Not surjective.** Choose `g_1 != g_2` with `f_φ(g_1) = f_φ(g_2)`. Every
  image configuration takes equal values at `g_1` and `g_2`, and `|A| >= 2`
  gives a configuration that does not. So `Φ` is strict on every fibre, which
  proves (2).

**Step 5: no finite orbits.**
- Suppose `φ` in `X_S` has finite orbit. Its stabilizer `L` has finite index.
- From `φ(l^(-1) g) = φ(g)` for all `l in L`, we get `f_φ(lg) = l f_φ(g)`. So
  `f̄(Lg) = L f_φ(g)` is a well-defined self-map of the finite set `L\G`.
- Fix `h` and choose `g_1 != g_2` with `f_φ(g_i) = h`. If `g_2 = l g_1` with
  `l != e`, then `h = f_φ(g_2) = l h`, which is impossible. So `L g_1 != L g_2`.
- Then every point of `L\G` has at least two preimages under `f̄`, which gives
  `|L\G| >= 2|L\G|`. That is a contradiction, and it proves (3).

**Step 6: no equivariant maps from full shifts.**
- An equivariant map sends a point with finite orbit to a point with finite
  orbit.
- Every full shift has the constant configurations, which are fixed by `G`.
- By Step 5, `X_S` has no such point. This proves (4).

**Remark: why this is a firewall and not a construction.**
- Suppose `τ` is a strict automaton on a full shift. For every finite-index
  `L`, the configurations fixed by `L` form a finite set that `τ` maps into
  itself, so `τ` is bijective on them.
- Step 6 says that any arrow field computed from the data must fail on those
  configurations. So a hotel-type counterexample must absorb its defects on a
  set that Step 5 forces to be nonempty.

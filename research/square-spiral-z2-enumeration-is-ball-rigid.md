---
rg: 2
id: square-spiral-z2-enumeration-is-ball-rigid
kind: claim
title: The square-spiral enumeration of Z^2 is ball-rigid, since its far Schreier balls determine it from a finite seed; ball-transplant flexibility therefore cannot kill every one-ended input
distinct_from:
  houghton-like-envelope-fp-pins-the-enumeration-by-near-relators: that proves finite presentation forces nu to be pinned, and kills free-shift and subgroup-supported designs by flexibility. This shows the flexibility route has a limit, with an explicit one-ended enumeration that no ball transplant can move.
  fsym-containing-fp-groups-are-pinned-by-finitely-many-equations: that gives the ball test as a non-finite-presentation criterion. This shows the criterion's hypothesis fails for the square spiral at every radius at least 5, so the test cannot be the decisive kill for one-ended inputs.
  square-spiral-z2-near-shift-group-is-not-finitely-presented: that kills the spiral through R_nu, the germ gate. This shows that for the spiral the rigidity gate is passed in the ball sense, so its germ-gate failure is the operative one.
---

**ESTABLISHED** (lane proof, bh-free-48, not independently reviewed, no priority claimed). The proof is below.

**Setting.**
- `nu : Z^2 -> N` is the square spiral of `square-spiral-z2-enumeration-passes-the-finite-window-gate`.
- `sigma = nu^-1 s nu` is its successor, and `d(p) = sigma(p) - p`. The field `d` equals `+e2` on `R`, `-e1` on
  `T`, `-e2` on `Lf` and `+e1` on `B`, using the four cones of that node.
- For a bijection `nu'`, `Σ(nu')` is the labeled graph on `Z^2` with edges `p -> p+e1` (label `a`), `p -> p+e2`
  (label `b`) and `p -> sigma'(p)` (label `s`), where `sigma' = nu'^-1 s nu'`.
- This is the Schreier graph of `<lambda(P), s>` on `N`, transported by `nu'`.
- An `L`-ball is the induced rooted labeled subgraph on the vertices at graph distance at most `L` from the root.

**Statement.** Let `L >= 5` and `R >= 1`. Put `F = {max(|x|,|y|) <= R} = nu^-1([0, (2R+1)^2))`. Suppose a bijection
`nu'` satisfies:
- `nu' = nu` on `F`;
- for every `p ∉ F`, the `L`-ball of `Σ(nu')` at `p` is isomorphic to the `L`-ball of `Σ(nu)` at some `q` with
  `max(|q_1|,|q_2|) >= 3L`.

Then `nu' = nu`.

**Consequences.**
1. **Ball flexibility cannot move the spiral.** No perturbation of the spiral built from spiral balls exists, beyond
   a seed and at any radius at least 5. This includes the finitary swaps, coset moves and generic transplants behind
   `free-shift-houghton-like-envelopes-are-not-fp` and item 5 of the pinning node.
   - So the ball test of `fsym-containing-fp-groups-are-pinned-by-finitely-many-equations`, applied through `Σ`,
     cannot be the decisive kill for one-ended inputs.
   - A flexibility kill of a one-ended enumeration must produce far balls that do **not** occur in `Σ(nu)`, yet still
     close the finitely many near relators. By compactness, `u` is a near relator of `nu` exactly when it closes on
     every limit of far balls of `Σ(nu)`. Other closing structures always exist: for example, the Cayley graph of
     `R_nu` itself.
2. **Which gate kills the spiral.** The spiral is killed by the germ gate, since `R_nu` is not finitely presented
   (`square-spiral-z2-near-shift-group-is-not-finitely-presented`). It is not killed by flexibility of its local
   patterns.
3. **Scope.** The proof uses only three facts: the successor steps are bounded; far windows see at most one straight
   boundary; boundaries leave `F` at finitely many places. So it applies verbatim to polyhedral piecewise-translation
   enumerations of `Z^2` whose far windows see at most one boundary line. All of these are also killed by the germ
   gate (`piecewise-translation-z2-enumerations-are-not-fp`).

## Proof

**Step 1: unit steps, and the field is copied.** Fix `p ∉ F` and an isomorphism `Psi` from the `L`-ball of
`Σ(nu')` at `p` onto the `L`-ball of `Σ(nu)` at `q`.
- Along any path of `a`/`b` edges from `p` to `x`, the endpoint satisfies `x - p` = the signed count of `a`- and
  `b`-edges on the path. `Psi` maps the path to a path with the same labels from `q`. So `Psi(x) = x + t` with
  `t = q - p` for every `x` in the `l^1`-ball `D_p` of radius `L` around `p`.
- For `x` with `|x - p|_1 <= L - 2`, the vertex `sigma'(x)` lies in the ball, and `Psi(sigma'(x)) = sigma(x + t)`.
- The point `sigma(x + t) = x + t + d(x + t)` is joined to `x + t` by an `a`- or `b`-edge, and both ends lie in the
  ball. So the preimage `sigma'(x)` is joined to `x` by an edge with the same label, and `sigma'(x) = x + d(x + t)`.
- So `d' = sigma' - id` satisfies `d'(x) = d(x + t)` on `D'_p = {|x - p|_1 <= L - 2}`.

**Step 2: far spiral windows.** Let `max(|q_1|,|q_2|) >= 3L`. The four cone boundaries are staircases along the rays
`x = y > 0` (NE), `x = -y < 0` (NW), `x = y < 0` (SW) and `x = -y > 0` (SE). Any two of them are at `l^1`-distance
more than `2L` near `q`. So on `q + D'_0` the field `d`:
- is constant, or
- takes exactly two values, separated by one straight staircase of one of four oriented types:
  - NE: `+e2` below and right, `-e1` above and left;
  - NW: `-e1` to the right, `-e2` to the left;
  - SW: `-e2` above and left, `+e1` below and right;
  - SE: `+e1` below, `+e2` above.

By Step 1, `d'` has the same property on every window `D'_p` with `p ∉ F`. Since `L - 2 >= 3`, a window can tell
these cases apart and detect a boundary that ends, bends or meets a second one.

**Step 3: inside `F`.** Let `x_last = (R, -R) = nu^-1((2R+1)^2 - 1)`, the last point of ring `R`. For `x ∈ F` other
than `x_last`, `nu'(x) + 1 = nu(x) + 1` lies in `nu(F)`, so `sigma'(x) = sigma(x)`. Hence `d' = d` on `F ∖ {x_last}`.
Also `x_last` lies in a window `D'_p` for a neighbor `p ∉ F`, so `d'(x_last)` obeys Step 2.

**Step 4: propagation.** Let `β'` be the set of adjacent pairs where `d'` jumps, and `Ω = Z^2 ∖ F`.
- By Step 2, each connected component of `β'` meeting `Ω` is locally a straight diagonal staircase of one fixed
  type. So globally it is a straight diagonal line or ray that meets no other component and ends only at `F`.
- Consider windows centered just outside `F` that overlap `F`. They show the spiral field on their part inside `F`.
  - At the four corners of `F`, the spiral's four boundaries enter the window. So they continue outward as the four
    spiral rays.
  - At a non-corner point of a side, the part inside `F` is constant. A component starting there would end at `F`
    inside the window, which Step 2 forbids.
- A component contained in `Ω` is a full line. A slope-one line avoiding `F` is `x - y = c` with `|c| > 2R`. It meets
  the line `x + y = 0` at a point outside `F`, which lies on the SE or NW spiral ray. That is a window with two
  boundaries. Slope `-1` lines are excluded the same way.
- So `β' ∩ Ω` equals the spiral's boundary set in `Ω`. Each of the four components of `Ω` minus the boundaries is
  connected, carries a constant `d'`, and touches `F ∖ {x_last}`, where `d' = d`.
- So `d' = d` on `Ω`, and therefore on `Z^2 ∖ {x_last}`.

**Step 5: conclusion.**
- `sigma'` is a bijection onto `Z^2 ∖ {nu'^-1(0)}`, and `nu'^-1(0) = nu^-1(0)`. It agrees with `sigma` off `x_last`,
  so `sigma'(x_last) = sigma(x_last)` and `sigma' = sigma`.
- `nu'` is determined by `sigma'` and `nu'^-1(0)`, via `nu'(sigma'^k(nu'^-1(0))) = k`. So `nu' = nu`. ∎

## Lesson for general BH

Local-flexibility obstructions (ball tests, swaps, coset moves) only kill enumerations whose far structure is
homogeneous enough to transplant. Polyhedral enumerations of a one-ended group are locally rigid, because their
defect lines propagate straight out of a finite seed. So for one-ended inputs, transplant flexibility does not break
pinning. Full relator-pinning of the spiral is not proved here. The Houghton
and shell obstruction for them has to come from finite presentation of the near shift group `R_nu` (the germ gate,
e.g. the zero-flux strand stacks of bh-houghton-morse), or from realizing foreign `R_nu`-sets as far-out patterns.
It cannot come from transplanting the enumeration's own patterns.

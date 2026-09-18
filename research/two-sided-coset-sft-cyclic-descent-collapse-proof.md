---
rg: 2
id: two-sided-coset-sft-cyclic-descent-collapse-proof
kind: route
title: Conjugate-short pairs have close lifts; cyclic descent is local, hence occurs inside every long linear word, and the tail frame turns it into distance descent from a ball
target: two-sided-free-group-coset-sfts-collapse-under-cyclic-descent
requires: [coset-invariant-sft-rigidity-descends-along-double-cosets]
---

The notation is that of the target. Put `M = max |s|` over the finitely many rule sets `S`.

**Frames.** If `z ∈ Z`, then `z_r : k -> z(kr)` lies in `Z`. Apply the rule to `z_r` at `k r^(-1)`: this
gives `z(k) = φ(t -> z(k r^(-1) t r))`, for `t ∈ S`.

**1. Free commutation.** Let `w` be a cyclically reduced conjugate of `k^(-1)k'`, say
`k^(-1)k' = q w q^(-1)`, with `|w| ≤ 2D`.
- The lifts `(kq, q)` and `(kqw, q)` map to `k` and `kqwq^(-1) = k'`, and lie at distance `|w|`.
- By parts 1 and 2 of the descent theorem, `F(k)` and `F(k')` commute.

**2. Rigidity under CD.** Use the descent criterion with `c = ℓ` and `c_0 = L_0`.
- *Base.* This is 1.
- *Step.* For a pair `(k, k')` whose class `w` has `ℓ(w) = L > L_0`, take the rotation
  `w' = q^(-1)k^(-1)k'q` and the rule `(S, φ)` supplied by CD.
  - Use the lift `λ' = (k'q, q)` and `T = {(s, 1) : s ∈ S}`, which lies in `B_M`.
  - By the frame identity with `r = q^(-1)`, `z(k')` is a function of `z` on
    `π(λ'(s,1)) = k'qsq^(-1)`.
  - The types `k^(-1)k'qsq^(-1) ~ w's` have `ℓ < L`.

  So the criterion applies once `D ≥ max(L_0/2, M, 2)`.

**3. Finiteness.**

*(i) Locality.* Insert `s` at a cut of a reduced word, cyclic or linear. The resulting word is shorter
exactly when one of two things happens.
- `s` cancels completely. The length then drops by at least `|s|`, and any further cascade only
  shortens it more.
- The cancellation stops inside `s`. The change is then decided by at most `|s|` letters on each side.

Either way, "insertion at this cut shortens the word" is decided by the context `(β, α)`: the `M`
letters before the cut and the `M` letters after it. Call a context a *descent context* if some rule
`S` has every `s ∈ S` shortening at such a cut.

*(ii) Acyclicity.* Consider the finite graph of reduced words of length `2M`, with an edge for each
one-letter shift. A cyclically reduced word of length `L ≥ 2M` is a closed walk of length `L`, whose
vertices are its cut contexts. By CD every closed walk of length `> L_0` meets a descent context. If
the non-descent contexts contained a directed cycle, going round it `n` times would give arbitrarily
long cyclically reduced words with no descent. Hence the non-descent subgraph is acyclic, and its walks
have length `< N`, the number of contexts.

*(iii) Linear descent.* Let `v` be reduced with `|v| ≥ N + 4M`. Its interior cuts, those with `M`
letters on both sides, form a walk of length `≥ N`. So one of them, `v = PQ`, is a descent context
for a rule `(S, φ)`. By (i), `|PsQ| < |v|` for every `s ∈ S`.

*(iv) Balls determine balls.* Let `z, z' ∈ Z` agree on `B_R(g)` with `R ≥ N + 4M`. Let `k = gv` with
`|v| = R + 1`, and choose `v = PQ` as in (iii).
- The frame identity with `r = Q` gives `z(k) = φ(s -> z(g P s Q))`, since `vQ^(-1) s Q = PsQ`.
- All the points `gPsQ` lie in `B_R(g)`, so `z(k) = z'(k)`.

By induction on `R`, `z = z'`. Restriction to `B_(N+4M)(1)` is therefore injective, and `Z` is finite.
An infinite group cannot act freely on a nonempty finite set.

**4. Walls.** For a vertical wall, `(p, k^(-1)p)` with `p ∈ N(e)` lies in the wall and maps to `k`. For a
horizontal wall, use `(kq, q)` with `q ∈ N(e')`.

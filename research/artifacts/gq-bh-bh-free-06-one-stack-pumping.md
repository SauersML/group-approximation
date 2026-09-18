# One-stack pumping: why V has only finite periodic subgroups, and why the argument stops at 2V

Lane bh-free-06, 2026-09-18. This is a lane proof, not reviewed. It is an independent
re-proof of a KNOWN theorem, so no priority is claimed: Röver, "Thompson's group V is
torsion locally finite", as quoted by Burillo–Cleary–Röver, arXiv:1402.3860 (Theorem 1.3;
read from the arXiv HTML, 2026-09-18). It is recorded because the mechanism shows exactly
which host feature an infinite bounded-exponent subgroup needs.

## Setup
Let `H = <S> <= V` be finitely generated, with `S` finite and symmetric. Refine every
generator so that it reads exactly `L` letters: `s(p w) = τ_s(p) w` for `|p| = L`, with
`1 <= |τ_s(p)| <= M`. A point `y` of the Cantor set is a stack whose top is its first
letter. Applying a generator pops `L` letters and pushes `|τ_s(p)|`. Along a path of
generators, the height `h` changes by `|τ_s(p)| - L ∈ [1-L, M-L]` per step, and letters
below the current reading depth keep their "level".

## Lemma 1 (pure push)
Let `K = (2^L + 1) M`. If some path of generators from `y` raises the height by at least
`K`, then `H` contains an element of infinite order.

*Proof.* For each level `c`, let `t_c` be the last time at or before the peak with
`h ≤ c`. After `t_c`, reads never go below level `h_{t_c} - L + 1`. Take the levels
`c = h_0 + jM` for `j = 1, ..., 2^L + 1`. The top `L`-letter windows at the times `t_c`
repeat for two of them, `c_1 < c_2`, and then `h_{t_{c_2}} > h_{t_{c_1}}`. The segment
`g` between these two times reads only its own writes and the window `W`. So for all `w`,
`g(W w) = W z w` with `z` nonempty, and `g^k(W w) = W z^k w`. Hence `g` has infinite
order. `∎`

By symmetry of `S`, the same holds for a drop of `K`. If two paths from `x` to `y` gave
different heights, the loop would fix `x` with a shift germ, which also has infinite order.
So in a periodic `H` the height is a well-defined function on each orbit.

## Theorem (Röver; re-proved)
Every finitely generated periodic subgroup of `V` is finite.

*Proof.* Suppose `H` is periodic.
- **Orbits are uniformly bounded.** By Lemma 1, every orbit has height range at most `2K`.
  So a path from `x` consumes at most `K + L` letters of `x`, and every orbit point is
  `u σ^b(x)` with `b ≤ K + L` and `|u| ≤ 2K + L`. Hence `|Hx| ≤ N_0`, independent of `x`.
- **`H` is finite.** The kernels of the actions on orbits have index at most `N_0!`, and a
  finitely generated group has only finitely many such subgroups. The action is faithful,
  so their intersection is trivial and `H` is finite. `∎`

(The same proof works verbatim for the Higman–Thompson groups `V_{n,r}`.)

## Where it stops
- **`2V`.** Elements of `2V` are two-stack machines: they pop and push bounded prefixes in
  both coordinates. The window pigeonhole fails, because the second stack carries unbounded
  information. Two stacks simulate Turing machines, and Belk–Bleak (arXiv:1405.0982) prove
  that the torsion problem of `2V` is undecidable. So no uniform bound of this kind can
  hold. Whether `2V` is torsion locally finite is recorded as OPEN in
  `brin-thompson-2v-is-torsion-locally-finite`. The only published claim for `nV`
  (arXiv:2209.11982) is WITHDRAWN.
- **Röver–Nekrashevych groups `V_d(G)`.** Elements act on the untouched tail through `G`,
  so the tail is not read-only. Indeed Röver's group contains Grigorchuk's group.
- **Twisted Brin–Thompson groups and germ extensions.** These have the same two defects:
  several coordinates, or non-trivial germs on tails.

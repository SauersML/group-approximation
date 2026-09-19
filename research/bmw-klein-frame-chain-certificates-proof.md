---
rg: 2
id: bmw-klein-frame-chain-certificates-proof
kind: route
title: Frame chains checked by two rewriting algorithms, and exact flat-Klein-bottle searches with Theorem 4
target: bmw-klein-frame-chain-certificates
requires:
  - bmw-census-klein-power-chain-certificates
artifacts:
  - experiments/bmw-klein-frames-2026-09-18/README.md
  - experiments/bmw-klein-frames-2026-09-18/kframe.py
  - experiments/bmw-klein-frames-2026-09-18/kbottle.py
  - experiments/bmw-klein-frames-2026-09-18/kbottleB.py
  - experiments/bmw-klein-frames-2026-09-18/chains_41_30.json
  - experiments/bmw-klein-frames-2026-09-18/chains_52_30.json
  - experiments/bmw-klein-frames-2026-09-18/verify_41_30.log
  - experiments/bmw-klein-frames-2026-09-18/verify_52_30.log
  - experiments/bmw-klein-frames-2026-09-18/kbottle_31_30_26.jsonl
  - experiments/bmw-klein-frames-2026-09-18/kbottle_31_31_12.jsonl
  - experiments/bmw-klein-frames-2026-09-18/kbottleB_31_30_26.jsonl
  - experiments/bmw-klein-frames-2026-09-18/kbottleB_31_31_12.jsonl
  - experiments/bmw-klein-chains-transposed-2026-09-17/verify_klein2.py
  - experiments/bmw-klein-chains-transposed-2026-09-17/crosscheck2.py
---

The proof uses four facts from `bmw-census-klein-power-chain-certificates-proof`:
- **§1 there:** a cycle of (K) and (R) steps with at least one (K) step rules out a left order.
- **§2 there:** every element of `Γ_c` has a unique normal form `(reduced v-word)(reduced h-word)`,
  and also one in the order `(reduced h-word)(reduced v-word)`. This holds with transposed letters too.
- **§3 there:** the checkers `verify_klein2.py` and `crosscheck2.py`.
- **§5 there, Theorem 4:** every Klein pair of `Γ^+` is `Γ`-conjugate to a pure pair.

## 1. Part (a): the certificates

The chain files use the checkers' format. An element is written `v<letters>|h<letters>`, its normal
form. A chain is a list of elements. Power steps carry their root in `roots` when it is not the smaller
element itself.

For each consecutive pair `(x_i, x_{i+1})`, taken cyclically, `verify_klein2.py` does the following:
- it tests `x_{i+1} x_i x_{i+1}^{-1} = x_i^{-1}` by rewriting to normal form;
- or, for a power step, it tests `x_i = r^e` and `x_{i+1} = r^f` with `1 ≤ |e| < |f|`;
- it requires at least one (K) step;
- it writes every rewriting step to `verify_X.log`.

`crosscheck2.py` recomputes the same identities with a separate normal-form routine. Both logs end with
these lines:
- `41_30`, #80 and #113: `chain of length 8 with 4 inverting steps verified` and
  `ok: 8 steps, 4 inverting`.
- `52_30` #158: `chain of length 10 with 4 inverting steps verified` and `ok: 10 steps, 4 inverting`.

Every element has even `h`-length and even `v`-length, so it lies in `Γ_c^+`. §1 of the cited proof
then shows that `Γ_c^+` is not left-orderable. ∎(a)

The power steps of #158 can also be seen by hand. All `v`-letters of `52_30` are involutions. So
`r = v2012` gives `r^k = 2 (01)^k 2` after cancelling each `2 2`, and `t = v120121 = 1 r 1` gives
`t^k = 1 2 (01)^k 2 1`. The chain elements `v201012`, `v2010101012` and `v20101010101012` are
`r², r⁴, r⁶`, and the `t`-elements are the same with `1 · 1` around them.

## 2. Part (b): no short pure pairs

Fix a class, and let `A` be a reduced word of one family and `B` a nonempty reduced word of the other,
both of even length. Since `A^{-1}` also inverts `B`,
`A B A^{-1} = B^{-1}  ⇔  A B = B^{-1} A  ⇔  B A = A B^{-1}`.

**Pushing.**
- Each square `a b = b' a'` is unique given `(a, b)`, and also given `(b', a')`.
- So pushing a reduced word of one family through a reduced word of the other gives a unique pair of
  reduced words of the same lengths. By uniqueness of normal forms, it computes the normal form of
  the product.
- Hence `A B = B^{-1} A` holds exactly when pushing `B` through `A` returns `B^{-1}` on the left and
  `A` on the right.
- Likewise, `B A = A B^{-1}` holds exactly when pushing `A` through `B` returns every letter of `A`
  unchanged and leaves `B^{-1}` behind.

**`kbottleB.py` (fixed `|B| = q`, any `|A|`).** Push the letters `a_1, a_2, …` of `A` through `B` one at
a time: `S_{i-1} a_i = a_i' S_i`, with `S_0 = B`.
- The pair is valid exactly when `a_i' = a_i` for every `i` and `S_{|A|} = B^{-1}`.
- The state `(S_i, a_i, i mod 2)` determines which next letters are allowed: `a_{i+1}` must keep `A`
  reduced and must satisfy `a_{i+1}' = a_{i+1}`.
- So valid pairs with this `B` are exactly the paths of at least one step from `(B, –, 0)` to some
  `(B^{-1}, c, 0)`. The graph has `2 (1 + #letters) · #{reduced words of length q}` states.
- The script decides reachability exactly, for paths of every length. It condenses the strongly
  connected components (iterative Tarjan) and propagates target bitsets in reverse topological order.
- So a record `pairs: 0` at `q` means that no `A` of any length inverts a `B` of length `q`.

**`kbottle.py` (fixed `|A| = p`, any `|B| = 2k`).** Push `B = b_1 ⋯ b_{2k}` through `A`:
`S_{i-1} b_i = x_i S_i`, with `S_0 = A`.
- Validity means `x_i = b_{2k+1-i}^{-1}` and `S_{2k} = A`.
- The script pairs the front letter `b_i` with the back letter `b_{2k+1-i}`. It runs the front sections
  `S_i` forwards from `A`, and the back sections `T_i` backwards from `S_{2k} = A` using the inverse
  squares.
- A step chooses `x = b_i` and computes `S x = x' S'`. It then solves `T' y = x^{-1} T` for
  `(T', y)`, which is unique by the second uniqueness above, and requires `x' = y^{-1}`, i.e.
  `x_i = b_{2k+1-i}^{-1}`.
- The sections meet in the middle exactly when `S_k = T_k`, with the junction `b_k b_{k+1}` reduced.
  The last letters on each side are kept in the state, so `B` is reduced.
- Every state lies in a finite set (pairs of reduced words of length `p`, plus two letters). A BFS from
  all diagonal states `(A, A, –, –)` visits every reachable state and tests the meeting condition on
  every edge. So a record `complete: true, pairs: []` at `p` means that no `B` of any length is
  inverted by an `A` of length `p`.

**Runs.** Both scripts were run for `31_30` #26 and `31_31` #12, in both orientations (`--swap` exchanges
the families).
- `kbottle` for `p = 2, 4, …, 16`: every record is complete, uncapped and empty. The largest has 1010312
  states.
- `kbottleB` for `q = 2, 4, …, 14`: every record has `pairs: 0`.

Odd lengths cannot occur in `Γ^+`. So every pure pair `(A, B)` of these classes has `|A| ≥ 18` and
`|B| ≥ 16`.

Theorem 4 turns any Klein pair `(a, b)` of `Γ_c^+` into a pure pair `(g^{-1} a g, g^{-1} b g)`. This pair
lies in `Γ_c^+`, because `Γ_c^+` is normal in `Γ_c`. So it obeys these bounds. ∎(b)

**Calibration.** On `41_30` #55, which has a known chain, `kbottleB` finds `B ∈ {01, 02, 10, 20}` at
`q = 2`. With `--swap` it finds `2323` and `3232` at `q = 4`. These are that chain's words.

## 3. How the certificates were found (not part of the proof)

`kframe.py` keeps each node as a frame `x = c W c^{-1}`, with `W` a cyclically reduced pure word.
- **K-moves.** By Theorem 4 and the axis argument of its proof, the inverters of `W` are the elements
  `W^{2j} p A p^{-1}`.
  - Here `p = W[:t]` is a prefix of `W`, and `A` is a pure word of the other family that inverts the
    rotation `W[t:] W[:t]`.
  - The move goes to `c p A p^{-1} c^{-1}`, with frame `(c p u, A')`, where `A = u A' u^{-1}` and `A'`
    is cyclically reduced.
- **Power moves.** They go from `c ρ^e c^{-1}` to `c ρ^{e+1} c^{-1}` and `c ρ^{e+2} c^{-1}`.

The conjugators are products of prefixes. Each one maps the base vertex to a vertex on the axis of a
frame word, so no ball of conjugators is enumerated. The earlier ball search ran out of memory at
radius 4.

A strongly connected component containing a K edge yields a certificate cycle. It is written out and
then checked by §1 alone.

Pass 1 used `L = S = 6` and `NB = 16`. The per-class logs `kf_p1_X.jsonl` record the seeds, nodes,
edges, cap flag and chain of every class searched.

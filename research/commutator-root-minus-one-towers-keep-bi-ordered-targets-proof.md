---
rg: 2
id: commutator-root-minus-one-towers-keep-bi-ordered-targets-proof
kind: route
title: Kill-propagation keeps every tower letter; the identity's factors are conjugates of two different letters, so it only forces opposite signs; the mirror of the hyperseries conjugator lemma gives the sign σ_{n-1}σ_n at every step, which alternates through N_[0,4] and fails at the first (+, -) step of N_[0,5]
target: commutator-root-minus-one-towers-keep-bi-ordered-targets
requires:
  - edge-injective-quotients-give-hughes-free-division-rings
  - vertex-injective-quotients-give-hughes-free-division-rings
  - commutator-root-minus-one-groups-have-generalized-torsion
  - commutator-root-frontier-kills-pl-and-bi-ordered-targets
  - hyperseries-conjugators-put-commutator-roots-in-h
---

Notation is that of [[commutator-root-minus-one-towers-keep-bi-ordered-targets]]. Write `Y_i = φ(y_i)`. In `N_[0,L]`
the relations are `R_j`, for `0 ≤ j ≤ L - 2`:

`R_j:  y_{j+2}^{-1} y_j^{-1} y_{j+2} = y_j^{-1} y_{j+1}^K`.

This is `y_{j+1}^K = [y_j^{-1}, y_{j+2}] = y_j y_{j+2}^{-1} y_j^{-1} y_{j+2}`, rearranged.

## Item 1

Let `Q` be torsion-free, and suppose `Y_m = 1`.
- If `m ≤ L - 2`, then `R_m` reads `1 = Y_{m+1}^K`, so `Y_{m+1} = 1`.
- If `m ≥ 2`, then `R_{m-2}` reads `Y_{m-2}^{-1} = Y_{m-2}^{-1} Y_{m-1}^K`, so `Y_{m-1} = 1`.

Starting from `m`, the first rule moves up to `L - 1`. From `L - 1 ≥ 1` the second rule moves down to `1`. So
`Y_1 = … = Y_{L-1} = 1`. For `L ≥ 3` the edge letter `y_{L-2}` lies in `[1, L-1]`. So if it is kept, no letter
dies.

## Item 2

Fix `j` with `0 ≤ j ≤ L - 3`. Conjugation by `t^j` in `G` is an isomorphism `N_[0,3] → N_[j,j+3]` sending `y_i` to
`y_{i+j}`. So the identity of [[commutator-root-minus-one-groups-have-generalized-torsion]] item 1 shifts to a
trivial word in `N_[j,j+3] ⊆ N_[0,L]`:

`P_1 · (y_{j+2}^K P_2)^{K-1} · y_{j+2}^{K-1} · (y_{j+2} P_2 y_{j+2}^{-1}) = 1`,

with `P_1 = y_j y_{j+2} y_j^{-1}` and `P_2 = y_{j+3}^{-1} y_{j+1} y_{j+3}`.
- Each factor is a conjugate, inside `N_[0,L]`, of `y_{j+2}` or of `y_{j+1}`.
- If `σ_{j+1} = σ_{j+2} = +`, every factor maps above `1`. A product of positive elements is positive, not `1`.
  The case `-` is the same.
- So `σ_{j+1} ≠ σ_{j+2}`.

Nothing more follows from the identity alone. In [[commutator-root-minus-one-groups-have-generalized-torsion]]
the map is defined on `G`, so `y_{j+1} = t^{-1} y_{j+2} t` forces one sign for all factors, and that is the
contradiction there. A map of `N_[0,L]` need not extend over `t`, and items 3 and 4 show that alternating signs
are realised.

## Item 3

We use (B1)-(B4) of [[hyperseries-conjugators-put-commutator-roots-in-h-proof]]: `Γ` is bi-ordered, `∘ h`
fixes `ℝ` and is increasing, each `f > x` has an Abel function `V_f` with `V_f ∘ f = V_f + 1`, and the
centraliser of `x + 1` is `{x + s : s ∈ ℝ}`. We also use Bagayoko's Cor. 4.22: any two elements `> x` of `Γ` are
conjugate.

**(a) Extension rule.** Since `N_[0,n+1]` is the HNN extension of `N_[0,n]` by `R_{n-1}`, a map `φ` of `N_[0,n]`
extends exactly when some `c ∈ Γ` has `c^{-1} A c = B`, that is `A c = c B`. Here `A = Y_{n-1}^{-1}` and
`B = A Y_n^K`.
- Conjugate elements lie on the same side of `x`, so that side condition is necessary.
- It is sufficient by Cor. 4.22, applied to `(A, B)` or to `(A^{-1}, B^{-1})`, since `A c = c B` iff
  `A^{-1} c = c B^{-1}`.
- Under alternation, suppose `σ_{n-1} = -` and `σ_n = +`. Then `A > x` and `Y_n^K > x`, so `B > A > x`.
- If `σ_{n-1} = +` and `σ_n = -`, then `A < x` and `B < A < x`.

**(b) Conjugators and signs.** Let `(A', B')` be the pair above `x`, so `A' c = c B'`.
- Step 3 of the lemma in [[hyperseries-conjugators-put-commutator-roots-in-h-proof]] shows the solutions are
  exactly `c_s = V_{A'}^{-1} ∘ (V_{B'} + s)`, for `s ∈ ℝ`. It also shows `c_s < x` iff `V_{A'} - V_{B'} > s`.
- So some `c_s < x` iff `V_{A'} - V_{B'}` is bounded below by a real. Likewise some `c_s > x` iff it is bounded
  above by a real.
- Step 2 of that lemma shows `A' < B' ⇒` bounded below. Swapping the roles of `A'` and `B'` gives the mirror:
  `B' < A' ⇒` bounded above. Explicitly, the lemma gives `d < x` with `B' d = d A'`, and `c = d^{-1} > x`
  solves `A' c = c B'`.
- So the sign that always exists is `-` when `A' < B'` and `+` when `B' < A'`.
- In terms of `σ`, the four cases are as follows. When `σ_{n-1} = -`, the pair is `(A, B)`; `B' > A'` iff
  `σ_n = +`. When `σ_{n-1} = +`, the pair is `(A^{-1}, B^{-1}) = (Y_{n-1}, Y_n^{-K} Y_{n-1})`; `B' > A'` iff
  `σ_n = -`. So the always-available sign is:

| `σ_{n-1}` | `σ_n` | order of `A', B'` | default `σ_{n+1}` |
|---|---|---|---|
| - | + | `A' < B'` | - |
| - | - | `B' < A'` | + |
| + | + | `B' < A'` | + |
| + | - | `A' < B'` | - |

  This is `σ_{n+1} = σ_{n-1} σ_n`.

**(c) N_[0,4].** Put `Y_0 = x - 2` and `Y_1 = x - 1/K`. These are elements of `Γ` below `x`. Since `N_[0,1]` is
free, they define `φ` on `N_[0,1]`.
- *Step n = 1.* `A = x + 2`, and `Y_1^K = x - 1` under composition. So `B = (x + 2) ∘ (x - 1) = x + 1`. Both are
  above `x`, so (a) extends `φ`, and (b) gives `c > x`: `σ_2 = +`.
- *Step n = 2.* `(σ_1, σ_2) = (-, +)`. (a) holds automatically, and the default is `σ_3 = -`.
- *Step n = 3.* `(σ_2, σ_3) = (+, -)`. (a) holds automatically, and the default is `σ_4 = -`.

This gives `φ: N_[0,4] → Γ` with signs `(-, -, +, -, -)`, and every `Y_i ≠ x`.
- *Membership in 𝓗.* `Γ` is bi-orderable, so it lies in 𝓗 by
  [[vertex-injective-quotients-give-hughes-free-division-rings]]. It is torsion-free, so the restriction of `φ`
  to `N_[0,n+1]` is injective on the infinite cyclic edge group `<y_{n-1}>`, for `n = 1, 2, 3`.
- The edge-injective quotient lemma (item 1 of [[edge-injective-quotients-give-hughes-free-division-rings]]),
  applied to the one-edge graph of groups `N_[0,n+1] = N_[0,n] *_{<y_{n-1}>}`, then gives `N_[0,2]`, `N_[0,3]`
  and `N_[0,4]` in 𝓗, in turn, starting from the free group `N_[0,1]`.
- Conjugation by `t^m` gives `N_[m,m+4] ≅ N_[0,4]`.

**(d) Hard steps.** Let `φ: N_[0,L] → Γ` keep `y_{L-2}`, with `L ≥ 3`. By item 1 it keeps every letter. By
item 2, `σ_1, …, σ_{L-1}` alternate.
- Every such `φ` is built by the extensions `n = 1, …, L - 1` of (a), with `φ(y_{n+1})` one of the `c_s` of (b).
- For `2 ≤ n ≤ L - 2`, both `σ_n` and `σ_{n+1}` lie in the alternating range, so `σ_{n+1} = -σ_n`. The default
  `σ_{n-1} σ_n` equals `-σ_n` iff `σ_{n-1} = -`.
- So the step is non-default exactly when `σ_{n-1} = +`, where `(σ_{n-1}, σ_n) = (+, -)`. Among the `L - 3`
  alternating signs `σ_1, …, σ_{L-3}` at least `⌊(L-3)/2⌋` are `+`.
- At a non-default step `(A', B') = (Y_{n-1}, Y_n^{-K} Y_{n-1})` with `A' < B'`, and `σ_{n+1} = +` is needed. By
  (b) this exists iff `V_{A'} - V_{B'}` is bounded above by a real.
- For `L = 4` the count is `0`, as in (c). For `L = 5` it is `1`: one of the steps `n = 2, 3` has
  `σ_{n-1} = +`, since `σ_1 ≠ σ_2`.

So a map using only the always-available sign stops at `N_[0,4]`. This is not an obstruction: (b) does not
decide whether a bounded Abel difference can be arranged, using the free choice of `Y_0, Y_1` and of the
parameters `s` at the earlier steps.

## Item 4

`bo_sat_ns.py` extends `bo_sat.py` of [[commutator-root-minus-one-groups-have-generalized-torsion]] by one
argument, `SHIFT`, that selects the clause linking `g` with its index shift `t^{-1} g t`:
- `1` gives `g > 1 ⇔ shift(g) > 1`;
- `-1` gives `g > 1 ⇔ shift(g) < 1`;
- `0` gives no clause.

The other clauses are unchanged. They say exactly one of `g, g^{-1}` is positive, positives multiply to
positives inside the ball, and conjugation by a letter preserves positivity. Equalities in the ball come from
the exact Britton word problem of `tower_wp.py`, with candidate identities from the permutation images in
`perms_2_-1_1.txt`. Each clause is a necessary condition, so UNSAT would certify that no order of that kind
exists. The runs are listed in `runs.log`, with the solver's positive letters. They were run as
`bo_sat_ns.py 2 -1 1 perms_2_-1_1.txt W r 24 SHIFT` under `nice -n 10 timeout 1200`, single-threaded, each
under 400 s.
- The `SHIFT = 1` UNSAT results reproduce the node above.
- The `SHIFT = 0` and `SHIFT = -1` results are all SAT. The positive letters in each model satisfy item 2.
- Under `SHIFT = -1` the signs alternate on all of `y_0, …, y_{W-1}`, as the clause forces.

## Item 5

- `G = N ⋊ <t>`, and 𝓗 is closed under subgroups and extensions by `ℤ`. So `G ∈ 𝓗` iff `N ∈ 𝓗`.
- Bi-orderable groups lie in 𝓗 ([[vertex-injective-quotients-give-hughes-free-division-rings]]).
- If `P` is the positive cone of a bi-order of `N` with `t^{-1} P t = P^{-1}`, then `t^{-2} P t^2 = P`. So the
  lexicographic order (the `t^2`-exponent first, then `P`) bi-orders `G_2 = N ⋊ <t^2>`, of index 2 in `G`.
- Such a `P` is compatible with item 2, since its signs alternate on every `y_i`.
- Item 4 finds no finite obstruction up to `W = 7`, `r = 3` and `W = 5`, `r = 4`. No such order is constructed
  here.

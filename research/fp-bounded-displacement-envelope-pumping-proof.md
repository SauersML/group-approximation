---
rg: 2
id: fp-bounded-displacement-envelope-pumping-proof
kind: route
title: Relators of a bounded-displacement envelope form a one-sided shift of finite type, and pumping a unique solution makes it periodic
target: fp-bounded-displacement-e2-envelopes-are-eventually-periodic
requires: [fp-alt-fin-envelopes-are-unique-solutions-of-their-relators]
---

Products are compositions. Let `R` be a finite presentation of `G` on the
letters `g_1, ..., g_k, sl, flip, (1 2)`, and `t` the longest word length in `R`.

**Step 0. `S_0 = {sl, flip, (1 2)}` generates a group containing `Alt_fin(N)`.**
Put `L_p = 2p+1` for `p >= 0` and `L_p = -2p` for `p < 0`, a bijection
`Z -> N` with `sl(L_p) = L_(p+1)` and `(1 2) = (L_(-1) L_0)`. Conjugation relabels
supports, so `sl^p (1 2) sl^-p = (L_(p-1) L_p)`. These adjacent transpositions
along a bijection `Z -> N` generate `Sym_fin(N) ⊇ Alt_fin(N)`. This is (HFP1) of
`half-finite-shift-envelope-wp-computes-generators-proof`.

**Step 1. Folded coordinates.** Write `x = 2i+1` as `(i,+)` and `x = 2i+2` as
`(i,-)`, with `i >= 0`. Then:
- `sl(i,+) = (i+1,+)`; `sl(i,-) = (i-1,-)` for `i >= 1`; `sl(0,-) = (0,+)`;
- `flip(i,s) = (i,-s)`;
- `(1 2)` swaps `(0,+)` and `(0,-)` and fixes every point with `i >= 1`.

A permutation moving points of `N` by at most `D` moves the fold index `i` by at
most `D`, and so does its inverse. Let `D_0` be such a bound for all
`gamma_i^(±1)`.

**Step 2. Configurations.** Put `A = ({-D_0, ..., D_0} x {+,-})^(4k)`. A
configuration `c' ∈ A^(N_0)` records, at each fold index `i` and sheet `s`, the
fold displacement and target sheet of `gamma'_j` and of `gamma'_j^-1` at
`(i,s)`, for every `j`. The **conditions at `i`** are:
- (C1) the recorded maps are mutually inverse at `(i,+)` and `(i,-)`: that is,
  `gamma'_j^-1(gamma'_j(i,s)) = (i,s)` and `gamma'_j(gamma'_j^-1(i,s)) = (i,s)`,
  with no fold index below `0`;
- (C2) every `r ∈ R` fixes `(i,+)` and `(i,-)`.

A configuration satisfying (C1) at every `i` defines a tuple
`gamma' ∈ Sym(N)^k` with the recorded inverses. It satisfies `R` exactly when
(C2) holds at every `i`. Let `c` be the configuration of `gamma` itself. It
satisfies all conditions.

**Step 3. Locality and translation invariance.** Put `W = t(D_0+1) + D_0`. Each
letter moves the fold index by at most `D_0+1`, so the trajectory of `(i,s)`
under `r ∈ R` stays within `t(D_0+1)` of `i`. Two consequences:
- (L1) The conditions at `i` depend only on the block `c'|[i-W, i+W]`
  (intersected with `N_0`).
- (L2) For `i > W` the trajectory never reaches fold index `0`. There `sl^(±1)`
  shifts `i` by `±1` according to the sheet, `flip` changes the sheet, `(1 2)`
  does nothing, and `gamma'_j^(±1)` follows the letter recorded at the current
  index. None of these rules refers to the value of `i`. So there is a fixed set
  `Allowed ⊆ A^(2W+1)` with: for every `i > W`, the conditions at `i` hold iff
  `c'|[i-W, i+W] ∈ Allowed`.

**Step 4. Pumping.** Put `M = 3W`. Among the blocks `c|[a, a+2W]` with
`M <= a <= M + |A|^(2W+1)`, two coincide, at `a < b`. Define

```text
c'(i) = c(i)                              for i < a,
c'(i) = c(a + ((i - a) mod (b - a)))      for i >= a.
```

- (P1) `c' = c` on `[0, b+2W]`. For `i < b` this is the definition. For
  `i ∈ [b, b+2W]`, the coinciding blocks give `c(i) = c(i - (b-a))`, and `c'`
  has period `b - a` on `[a, ∞)`, so induction on `i` gives `c'(i) = c(i)`.
- (P2) For `i <= W`, the conditions at `i` only read `c'` on `[0, 2W + D_0]`,
  which lies below `a`, where `c' = c`. So they hold.
- (P3) For `i > W`, either `i + W <= b + 2W`, and the block lies in `[0, b+2W]`
  where `c' = c`; or `i - W >= b`, and subtracting a multiple of `b - a` moves
  the block to one of `c'` starting in `[a, b)`, still with centre `> W`. That
  block ends by `b + 2W`, so it is a block of `c` with centre `> W`. In both
  cases it is in `Allowed`, and the conditions at `i` hold by (L2).

So `c'` defines a tuple `gamma' ∈ Sym(N)^k` satisfying every relator in `R`. By
Step 0, clause 1 of `fp-alt-fin-envelopes-are-unique-solutions-of-their-relators`
applies with `Omega = N` and `S_0 = {sl, flip, (1 2)}`, and gives
`gamma' = gamma`. Hence `c = c'`, and `c` has period `b - a` on `[a, ∞)`.

**Step 5. Conclusion.** Put `m = 2(b-a)`. For `x >= 2a+1`, the points `x` and
`x + m` have fold indices `i` and `i + (b-a)` on the same sheet, with equal
recorded letters. So `gamma_j(x+m) = gamma_j(x) + m` for all `j`, i.e. every
`gamma_j ∈ E_m`. `∎`

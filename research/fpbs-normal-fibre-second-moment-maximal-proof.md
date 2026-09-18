---
rg: 2
id: fpbs-normal-fibre-second-moment-maximal-proof
kind: route
title: Truncated mass transport between conjugate cosets plus a Cauchy--Schwarz bootstrap
target: fpbs-normal-fibre-second-moment-maximal
requires:
  - fpbs-hp-relative-sharpness
---

Notation as in the target. `tau(x,y) = P_p(x <-> y)`, and `|g|` is word length.
If `E X^2 = infinity` there is nothing to prove, so assume `M := E X^2 < infinity`.
Fix `q` and write `Y = |K_o ∩ qN|` and `Z = |K_o ∩ q^{-1}N|`.

**Step 1: finite a priori.** By Harris--FKG, `tau(o,x) >= tau(o,h) tau(h,x)`.
Left multiplication by `h` is a graph automorphism preserving the law, so
`tau(h,hn') = tau(o,n')`. Hence

```text
chi^N := E X = sum_{n in N} tau(o,n) >= tau(o,h) sum_{n in N} tau(h,n)
       = tau(o,h) E|K_o ∩ h^{-1}N|.
```

Since `tau(o,h) >= p^{|h|} > 0` and `chi^N <= M^{1/2}`, every
`E|K_o ∩ gN|` is finite, and in particular `Y < infinity` and `Z < infinity`
a.s.

**Step 2: mass transport.** For vertices `x`, `y` put
`A_x = |K_x ∩ xN|` and `B_x = |K_x ∩ xqN|`. Fix `n >= 1` and define

```text
m(x,y) = 1{x <-> y} 1{y in xqN} A_x 1{A_x <= n, B_x <= n}.
```

This is nonnegative, bounded by `n` times an indicator, and invariant under
the diagonal left action of `Gamma` (left multiplication maps `xN` to `gxN`,
`xqN` to `gxqN`, and clusters to clusters). `Gamma` is unimodular, so the
mass-transport principle gives
`sum_y E m(o,y) = sum_x E m(x,o)`.

* **Outgoing mass.** `sum_y m(o,y) = |K_o ∩ qN| · X · 1{X<=n, Y<=n}`.
* **Incoming mass.** `o in xqN` means `x in N q^{-1} = q^{-1}N`, by normality.
  For such `x = q^{-1}n'`:
  * `xN = q^{-1}N`, so `A_x = |K_o ∩ q^{-1}N| = Z`, because `K_x = K_o` when
    `x <-> o`;
  * `xqN = q^{-1}n'qN = N`, so `B_x = X`.

  Hence `sum_x m(x,o) = Z · Z · 1{Z<=n, X<=n}`.

So, with `A_n = {X<=n, Y<=n}` and `B_n = {X<=n, Z<=n}`,

```text
(1)  E[XY; A_n] = E[Z^2; B_n].
```

The same computation with `q` replaced by `q^{-1}` swaps `Y` and `Z`:

```text
(2)  E[XZ; B_n] = E[Y^2; A_n].
```

**Step 3: bootstrap.** Put `a_n = E[Z^2; B_n]` and `b_n = E[Y^2; A_n]`. Both
are at most `n^2`, hence finite. By (1) and Cauchy--Schwarz,

```text
a_n = E[XY; A_n] <= (E X^2)^(1/2) (E[Y^2; A_n])^(1/2) = M^(1/2) b_n^(1/2),
```

and by (2), `b_n <= M^(1/2) a_n^(1/2)`. Combining these,
`a_n <= M^(3/4) a_n^(1/4)`, so `a_n <= M` because `a_n` is finite. Likewise
`b_n <= M`.

**Step 4: remove the truncation.** The events `B_n` increase to
`{X < infinity, Z < infinity}`, which has probability one by Step 1 and
`M < infinity`. Monotone convergence gives `E Z^2 <= M`, and in the same way
`E Y^2 <= M`. Since `q` was arbitrary, `E[Y_q^2] <= E[X^2]` for all `q`.

**Corollary.** For `p < p_c(N;G)`, `fpbs-hp-relative-sharpness` gives
`P_p(X >= k) <= exp(-ck)`, so `E X^2 = sum_k (2k-1) P(X >= k) < infinity`.
Jensen then gives `E|K_o ∩ qN| <= (E Y_q^2)^(1/2) <= (E X^2)^(1/2)` uniformly
in `q`. ∎

**Remark (where normality is used).** Normality enters only in identifying
`o in xqN` with `xN = q^{-1}N` and `xqN = N`. For a non-normal subgroup `I`,
the senders `x` with `o in xqI` form the set `I q^{-1}`, which is not a single
left coset of `I`. Then (1) and (2) no longer pair the same two fibres.

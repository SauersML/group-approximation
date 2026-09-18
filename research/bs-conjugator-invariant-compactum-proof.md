---
rg: 2
id: bs-conjugator-invariant-compactum-proof
kind: route
title: The BS(1,k) conjugator divides levels of a cocompactly wandering map by k, so a bounded band of fundamental domains is backward invariant and its backward limit is a compact invariant set
target: bs-conjugators-of-wandering-maps-have-invariant-compacta
---

Notation as in the target. Write `W = W(a)`, `Ω = Ω(a)`, and fix a compact
`D ⊆ W` with `W = ⋃_n a^n D`.

## Step 0. b^-1 preserves W

`Ω(g h g^-1) = g(Ω(h))` and `Ω(h^k) ⊆ Ω(h)` for homeomorphisms. So
`b(Ω) = Ω(b a b^-1) = Ω(a^k) ⊆ Ω`, hence `Ω ⊆ b^-1(Ω)` and
`b^-1(W) = X \ b^-1(Ω) ⊆ W`.

## Step 1. Levels

For compact `C ⊆ W`, properness applied to the compact set `C ∪ D` shows that
`N(C) = {n : a^n D ∩ C ≠ ∅}` is finite; since every point of `C` lies in some
`a^n D`, `C ⊆ ⋃_(n ∈ N(C)) a^n D`.

Put `E = D ∪ aD ∪ ... ∪ a^(|k|-1) D`. By Step 0, `b^-1(E)` is a compact subset of
`W`, so `b^-1(E) ⊆ ⋃_(|j| ≤ R) a^j D` for some `R`.

## Step 2. b^-1 divides levels by k

From `b a b^-1 = a^k` we get `b a^q b^-1 = a^(qk)`, so `b^-1 a^(qk) = a^q b^-1` for
all `q ∈ Z`.

Let `x = a^n y` with `y ∈ D`. Write `n = qk + r` with `0 ≤ r < |k|`, so `|q| ≤ |n|/|k| + 1`.
Then `x = a^(qk) (a^r y)` with `a^r y ∈ E`, and

```text
b^-1(x) = a^q b^-1(a^r y) ∈ a^q ⋃_(|j| ≤ R) a^j D = ⋃_(|j| ≤ R) a^(q+j) D.
```

## Step 3. A backward-invariant band

For `M ≥ 0` let `B_M = ⋃_(|n| ≤ M) a^n D`, a nonempty compact subset of `W`.
Take `M ≥ 2R + 4`. If `x ∈ a^n D` with `|n| ≤ M`, Step 2 puts `b^-1(x)` in some
`a^m D` with `|m| ≤ M/|k| + 1 + R ≤ M/2 + 1 + R ≤ M`. So `b^-1(B_M) ⊆ B_M`.

## Step 4. The invariant compactum (Part 1)

The sets `b^-m(B_M)`, `m ≥ 0`, are nonempty, compact and decreasing, since
`b^-1(B_M) ⊆ B_M`. Their intersection `K` is nonempty and compact, and

```text
b^-1(K) = ⋂_(m ≥ 1) b^-m(B_M) = ⋂_(m ≥ 0) b^-m(B_M) = K,
```

so `b(K) = K`. And `K ⊆ B_M ⊆ W`. By Zorn's lemma `K` contains a `b`-minimal set,
and every minimal set of `b` lies in `Ω(b)`.

## Step 5. Finite non-wandering sets (Part 2)

Assume `Ω` finite and `t a t^-1 = b`. Then `Ω(b) = t(Ω)`, so `|Ω(b)| = |Ω|`.
By Step 0, `b` maps the finite set `Ω` injectively into itself, hence onto itself, so
every point of `Ω` is `b`-periodic and `Ω ⊆ Ω(b)`. If `W ≠ ∅`, Step 4 gives a
point of `Ω(b)` in `W`, so `|Ω(b)| ≥ |Ω| + 1`, a contradiction. Hence `W = ∅`.

## Step 6. Part 3

In an action of `BG_k` put `b = t a t^-1`; then `b a b^-1 = a^k` holds in `Homeo(X)`.
If `a` were cocompactly wandering with finite `Ω(a)`, Part 2 would make `X = Ω(a)`
finite, and then `a` would have finite order. So an infinite-order image of `a` is
never of that type.

## Calibration

- **Affine model.** On the circle `X = R ∪ {∞}` take `a(x) = x + 1` and `b(x) = 2x`.
  Then `b a b^-1 = a^2`, `Ω(a) = {∞}`, and `a` acts properly and cocompactly on
  `W(a) = R` with `D = [0,1]`. Part 1 predicts a compact `b`-invariant subset of `R`:
  it is the fixed point `{0}`. Part 2 predicts that `a` and `b` are not conjugate:
  indeed `Ω(b) = {0, ∞}` has two points and `Ω(a)` has one.
- **Cantor model.** For a north--south map `a` of the Cantor set with fundamental
  domain `D`, every `b` with `b a b^-1 = a^2` has the form `(d, n) ↦ (ψ(d), 2n + c(d))`
  on `D × Z` with `ψ` a two-sheeted covering of `D`. Its bounded-level points form the
  set `K` of Step 4 (for `c` with values in `{0,1}`, the points whose `ψ`-itinerary has
  constant `c`).
- Nothing in the proof uses that `X` is totally disconnected.

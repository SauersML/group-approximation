---
rg: 2
id: kl-sign-index-two-infinite-order-loops-inject
kind: claim
title: A nonsingular word with one positive run and one negative run injects when both sign-change coefficients have infinite order, whatever its coincidences
distinct_from:
  kl-four-same-sign-corner-words-inject: that allows torsion loops but needs four light same-sign corners; this allows every coincidence pattern but needs both loop coefficients of infinite order.
  kl-length-six-one-coincidence-words-inject: that allows exactly one same-sign coincidence under conditions on the light cycle; this imposes no condition on the same-sign labels at all.
  kl-unit-exponent-words-inject-when-same-sign-corners-are-free: that needs the same-sign labels to be free and unabsorbed at any number of sign changes; this needs only infinite-order loops, at exactly two sign changes.
---

Let `G` be any group and `w in G * <t>` cyclically reduced, not a proper power,
with `deg_t(w) != 0`. Split powers of `t` into single letters. Suppose the
cyclic sign sequence has exactly two sign changes, i.e. one run of `+` and one
run of `-`:

```text
w = t a_1 t ... t a_(p-1) t y t^(-1) n_1 t^(-1) ... n_(q-1) t^(-1) x,     p != q.
```

If the two sign-change coefficients `y` and `x` both have infinite order, then
`G -> (G * <t>)/<<w>>` is injective, and every reduced spherical picture over
`<G, t | w>` is empty. The same-sign labels `a_i`, `n_j` are arbitrary: they
may repeat, invert each other, or be `1`.

**Status and credit.** `kl-four-same-sign-corner-words-inject` records that
Stallings' sign-index-two theorem and Clifford--Goldstein need infinite order
at exactly these two coefficients. So this is very likely a restatement of the
classical theorem, not a new result. Neither source was read here; the proof
route derives it directly from the weight test.

**Consequence at length six.** For the classes `+++++-` and `++++--`, a
Kervaire--Laudenbach violation needs at least one of `x`, `y` to have finite
order. Coincidences alone never make a violation. In the Leavitt lane both
sign-change coefficients are involutions, so this theorem gives nothing there.

DERIVATION
kl-sign-index-two-infinite-order-loops-proof

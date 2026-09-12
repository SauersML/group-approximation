---
rg: 2
id: parity-flip-models-satisfy-two-point-proof
kind: route
title: One bit of state carries the pair, and additivity is all the definition tests
target: parity-flip-models-satisfy-two-point
requires: []
---

# One bit of state carries the pair, and additivity is all the definition tests

**The model satisfies the definition.**  `φ(1) = flip^{P(1)}` and
`P(1) = P(1) + P(1) = 0` (additivity at `(1,1)`; harmless to include `1`
in `F`, and unitality can also just be imposed), so `φ` is unital.
Multiplicativity: for `g, g' ∈ F`,
`φ(g)φ(g') = flip^{P(g)+P(g')} = flip^{P(gg')} = φ(gg')`, distance `0` in
normalized Hamming — `(F,ε)`-multiplicative for every `ε`.  Distinctness:
`j_s(p) = s ≠ 1 − s = j_s(q)`.  Equivariance: identify `B = {0,1}` and
write `⊕` for mod-2 sum, so `j_s(p) = s` and `j_s(q) = s ⊕ 1`, and
`j_{φ(g)s}(x) = s ⊕ P(g) ⊕ [x = q]`.  The clause
`j_{φ(g)s}(x) = j_s(g^{-1}x)` is tested only when `g^{-1}x ∈ {p,q}`, and
`j_s(g^{-1}x) = s ⊕ [g^{-1}x = q]`.  The two sides agree iff

```text
P(g) = [x = q] ⊕ [g^{-1}x = q],
```

and the right side is `0` when `g` fixes the slot (`x = g·x'` with
`x' = x`) and `1` when it transports — i.e. it equals `τ(g)` in every
tested instance.  Since `P = τ` on the letters where `τ` is defined, and
letters with `τ` undefined are never tested (no `x` qualifies), all
clauses hold with `S = A`.

**The converse.**  Let `A = ℤ/2` and `φ(w) = flip^{P(w)}` satisfy the
definition at `(F, ε)`, `ε < 1`.  `Sym(ℤ/2)` has two elements at
normalized Hamming distance `1`, so `d(φ(g)φ(g'), φ(gg')) ≤ ε < 1` forces
equality, i.e. exact additivity of `P` on `F × F`.  With `|A| = 2` the
density condition `|S| > (1−ε)|A|` forces `S = A`.  Fix `s ∈ A`; the
distinctness and equivariance clauses at each letter `g` with `τ(g)`
defined read, by the display above, `P(g) = τ(g)`.

**Scope.**  Nothing here concerns the marked pair specifically; the
statement is pure bookkeeping about the definition, valid for any `G`-set
and any pair.  Its force is entirely negative-space: it locates the
minimum a refutation must clear, and `parity-trap-window` clears it for
the Kun--Thom pair.

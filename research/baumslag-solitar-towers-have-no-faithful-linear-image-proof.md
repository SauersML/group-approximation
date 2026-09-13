---
rg: 2
id: baumslag-solitar-towers-have-no-faithful-linear-image-proof
kind: route
title: Squaring permutes eigenvalues, and a unipotent adjoint cannot scale a nilpotent logarithm
target: baumslag-solitar-towers-have-no-faithful-linear-image
requires: []
---

**Step 1: a conjugate of its square is virtually unipotent.** Suppose
`g h g^-1 = h^2` in `GL_n(k)`. Then `h` and `h^2` have the same eigenvalues in the
algebraic closure `k̄`. Let `E` be the finite set of distinct eigenvalues of `h`,
all nonzero. Squaring maps `E` onto the eigenvalue set of `h^2`, which is `E`, so it
permutes `E`. Hence `lambda^(2^j) = lambda` for some `j >= 1`, and every eigenvalue
is a root of unity. So `h^N` is unipotent for some `N >= 1`.

Apply Step 1 to `(g, h) = (b, a)` and to `(c, b)`: `u = a^N` and `v = b^M` are
unipotent for some `N, M >= 1`.

**Step 2, characteristic p > 0.** A unipotent matrix `u` satisfies
`(u - 1)^n = 0`, so `u^(p^m) = 1` when `p^m >= n`. Hence `a^(N p^m) = 1`.

**Step 3, characteristic 0.** From `b a b^-1 = a^2` we get `b u b^-1 = u^2`, and by
induction `v u v^-1 = b^M u b^-M = u^(2^M)`. Write `u = exp(X)`, where
`X = log u = sum_(i >= 1) (-1)^(i+1) (u-1)^i / i` is a finite sum and nilpotent.
Conjugation commutes with these polynomial expressions, so
`v X v^-1 = log(u^(2^M)) = 2^M X`. The operator `Ad(v): Y ↦ v Y v^-1` on
`M_n(k)` equals `L_v R_(v^-1)`, a product of two commuting unipotent operators, so
it is unipotent and its only eigenvalue is `1`. Since `2^M ≠ 1` in characteristic
`0`, `Ad(v) X = 2^M X` forces `X = 0`, so `u = 1` and `a^N = 1`.

**Consequences.** In the tower group `<a, b, c | b a b^-1 = a^2, c b c^-1 = b^2>`,
`<a, b> ≅ BS(1,2)` and `<b, c> ≅ BS(1,2)` meet in `<b>`, which is infinite cyclic in
both. So the group is the amalgam of the two factors over `<b>`, the factors embed,
and `a` has infinite order. A faithful representation would contradict Steps 2–3.
For the Baumslag–Gersten group, `a` has infinite order (it lies in the
`BS(1,2) = <a,b>` subgroup of the HNN extension), and `c = t b t^-1` satisfies
`c b c^-1 = t (b a b^-1) t^-1 = t a^2 t^-1 = b^2`. `∎`

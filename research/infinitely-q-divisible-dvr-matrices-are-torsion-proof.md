---
rg: 2
id: infinitely-q-divisible-dvr-matrices-are-torsion-proof
kind: route
title: Congruence filtration proof that infinitely q-divisible matrices over a mixed-characteristic DVR are torsion
target: infinitely-q-divisible-dvr-matrices-are-torsion
requires: []
---

Complete direct proof. Notation as in the target. Let `π` be a uniformizer and
`e = v(q) >= 1`. Put `Γ_s = I + π^s M_N(O)` for `s >= 1`; these are normal
subgroups of `GL_N(O)` and `∩_s Γ_s = {I}`, because `∩_s π^s O = 0`.

**Step 1 (q-th powers raise the level).** If `s >= 1` and `y in Γ_s` then
`y^q in Γ_(s+1)`. Write `y = I + π^s X`. Then
`y^q = I + Σ_{i=1}^{q} C(q,i) π^(si) X^i`. For `1 <= i <= q-1` the binomial
coefficient is divisible by `q`, so the term lies in `π^(si+e) M_N(O)`, inside
`π^(s+1) M_N(O)`. For `i = q` the term lies in `π^(sq) M_N(O)` with
`sq >= 2s >= s+1`. By induction, `y in Γ_1` gives `y^(q^m) in Γ_(1+m)`.

**Step 2 (the reduction is semisimple of order prime to q).** Reduce modulo `π`:
`ḡ = h̄_j^(q^j)` in `GL_N(k)`. Choose `e_0` with `q^(e_0) >= N`. A unipotent
`u in GL_N(k)` satisfies `(u-1)^N = 0`, so `u^(q^(e_0)) - 1 = (u-1)^(q^(e_0)) = 0`.
Write `h̄_j = s_j u_j` (commuting Jordan parts over an algebraic closure).
For `j >= e_0` this gives `ḡ = s_j^(q^j)`, so `ḡ` is semisimple.
Let `λ` be an eigenvalue of `ḡ`. There is an eigenvalue `μ_j` of `h̄_j` with
`μ_j^(q^j) = λ`, and in characteristic `q` the `q^j`-th root of `λ` is unique.
So `μ_j = μ_(j+1)^q`, and the fields `k(μ_j)` increase with `j`. Each has degree
at most `N` over `k`, so the chain stops at a finite extension `k'` of `k`. Then
`λ` lies in `∩_j k'^(q^j)`.
That intersection is a perfect subfield of the finitely generated field `k'`.
- An element `x` of it that is transcendental over `F_q` would make
  `F_q(x^(1/q^∞))` an infinite algebraic extension of `F_q(x)` inside `k'`.
- But the algebraic closure of `F_q(x)` in the finitely generated field `k'` is
  finite over `F_q(x)`.
So the intersection is algebraic over `F_q`. Being a subfield of `k'`, it is
finite, so `λ` is a root of unity of order prime to `q`. Let `M` be the least
common multiple of these orders over the `N` eigenvalues. Then `ḡ^M = I`, since
`ḡ` is semisimple.

**Step 3 (conclusion).** For `j >= e_0`, `(h̄_j^M)^(q^j) = ḡ^M = I`.
- So every eigenvalue of `h̄_j^M` is a `q`-power root of unity in characteristic
  `q`, hence equal to 1, and `h̄_j^M` is unipotent.
- So `(h̄_j^M)^(q^(e_0)) = I`, and `y_j := h_j^(M q^(e_0))` lies in `Γ_1`.
- Now `y_j^(q^(j-e_0)) = h_j^(M q^j) = g^M`. By Step 1, `g^M in Γ_(1+j-e_0)`.
This holds for every `j >= e_0`, so `g^M in ∩_s Γ_s = {I}`. Hence `g` has finite
order dividing `M`, which is prime to `q`. ∎

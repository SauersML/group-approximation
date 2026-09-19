---
rg: 2
id: lifted-thompson-t-conjugate-templates-bounded-cliques-proof
kind: route
title: Localize each cross commutator to <h> times a finite centralizer ball, then pin the power of h by translation number or by the slope spectrum at fixed points
target: lifted-thompson-t-conjugate-template-codes-have-bounded-cliques
requires:
  - bounded-area-commuting-conjugator-localization
  - lifted-thompson-t-mf-radical-dichotomy
---

Area is the algebraic area in the free group `F(S)`.  It is invariant under
free reduction, under inversion, and under conjugation by any word: if
`g w g^(-1)` is a product of `m` conjugates of relators, so is `w`.  Let `M`
be the largest relator length.  `T̄` is finitely presented and torsion-free
(`lifted-thompson-t-mf-radical-dichotomy`, item 4), and `z(x) = x+1` is
central.  Since `x = [c,h] != 1`, neither `c` nor `h` lies in `<z>`.

## 1. Localization of an edge

Fix an oriented edge `(v,w)` and put `k = u_v^(-1) u_w`.  Then

```text
[C_w, H_v] = u_v [k c k^(-1), h] u_v^(-1),
[C_w, H_v] = u_w [c, k^(-1) h k] u_w^(-1),
```

so `Area([k c k^(-1), h]) = Area([k^(-1) h k, c]) <= A_0`.  Apply
`bounded-area-commuting-conjugator-localization` to `y = k c k^(-1)` and to
`y' = k^(-1) h k`:

```text
k c k^(-1) = h^n t,  t ∈ T_0 := C(h) ∩ B(A_0 M + 2|h|),
k^(-1) h k = c^m t', t' ∈ T_1 := C(c) ∩ B(A_0 M + 2|c|).        (1.1)
```

Both `T_0` and `T_1` are finite.

## 2. Pinning the power (the invariant)

**Lemma P.**  Let `h ∈ T̄ \ <z>` and `t ∈ C(h)`.  For every `c ∈ T̄`, the set
`N_t = { n ∈ Z : h^n t is conjugate to c }` is finite.

*Translation number.*  Let `tau(f) = lim f^j(0)/j`.  It is a conjugacy
invariant, and `tau(f z^p) = tau(f) + p`.  If `fg = gf`, then

```text
(fg)^j(0) - f^j(0) - g^j(0) = [f^j(g^j(0)) - g^j(0)] - [f^j(0) - 0]
```

is a difference of two values of the displacement of the lift `f^j`, which
is 1-periodic and monotone-lifted, so the difference lies in `(-1,1)`.
Hence `tau(fg) = tau(f) + tau(g)`.

*Case tau(h) != 0.*  `tau(h^n t) = n tau(h) + tau(t)` must equal `tau(c)`.
At most one `n` does.

*Case tau(h) = 0.*  Then `h` has a fixed point.  Otherwise `h(x) - x` has
constant sign and, being 1-periodic, has absolute value at least some
`eps > 0`, which gives `|tau(h)| >= eps`.  Also `h != id`.  `h - id` is
piecewise linear with finitely many pieces per period, so `Fix(h)` is, per
period, a finite union of points and closed intervals.

Let `E` be the set of left endpoints of the bounded components `(a,b)` of
`R \ Fix(h)`.  It is discrete, `z`-invariant and nonempty, with `N >= 1`
points per period.  At `a ∈ E` the right slope `h'_+(a) = 2^e` has `e != 0`:
if `e = 0` then `h`, which fixes `a` and is linear on some `[a, a+delta)`,
would be the identity there.

`t` commutes with `h`, so it permutes `Fix(h)`, its complementary
components, and `E`, preserving order.  Enumerate `E = {e_j}` increasingly,
with `e_(j+N) = e_j + 1`.  Then `t(e_j) = e_(j+s)` for a fixed `s`, so
`tau(t) = s/N`.  Put

```text
g_n = h^n t,   G_n = g_n^N z^(-s) = h^(nN) t_0,   t_0 = t^N z^(-s).
```

`t_0 ∈ C(h)` shifts `E` by `Ns - sN = 0`, so it fixes `E` pointwise.  By the
one-sided chain rule at the common fixed point `a ∈ E`,

```text
log_2 (G_n)'_+(a) = e n N + e_0,     e_0 = log_2 (t_0)'_+(a).       (2.1)
```

*Slope spectrum.*  For `f ∈ T̄` put
`Sigma(f) = { log_2 f'_(+-)(p) : p ∈ Fix(f) } ⊂ Z`.  It is finite, since `f`
commutes with `z` and has finitely many pieces per period.  It is a conjugacy
invariant: for orientation-preserving `u` and `p ∈ Fix(f)`,
`(u f u^(-1))'_+(u(p)) = u'_+(p) f'_+(p) / u'_+(p) = f'_+(p)`, and likewise
for the left slope.

If `g_n` is conjugate to `c` by `u`, then `G_n` is conjugate to
`c^N z^(-s)` by the same `u`, because `z` is central.  So by (2.1),
`e n N + e_0 ∈ Sigma(c^N z^(-s))`, a finite set that does not depend on `n`.
Since `e N != 0`, only finitely many `n` qualify.  `QED`

## 3. The finite sets

Put `F = { h^n t : t ∈ T_0, n ∈ N_t }`.  It is finite by Lemma P, since
`T_0` is finite.  By (1.1), `k c k^(-1)` is conjugate to `c` and equals some
`h^n t`, so it lies in `F`.  Hence `C_w = u_v (k c k^(-1)) u_v^(-1)` lies in
`u_v F u_v^(-1)`.

Symmetrically, apply Lemma P with the roles of `c` and `h` exchanged; this is
legitimate because `c ∉ <z>`.  This gives a finite `F_1` with
`k^(-1) h k ∈ F_1`, and `H_v = u_w (k^(-1) h k) u_w^(-1)` lies in
`u_w F_1 u_w^(-1)`.  That is (N).

## 4. Independence and cliques

Suppose `(v,w)` is an edge and `C_v = C_w`.  Then
`[C_w, H_v] = u_v x u_v^(-1) != 1`.  So it has no finite area, which
contradicts (CCC2).  Likewise, if `H_v = H_w` then
`[C_w, H_v] = u_w x u_w^(-1) != 1`.  So each class of equal `C`, and each
class of equal `H`, is an independent set.

For fixed `v`, the out-neighbours split into at most `|F|` classes of equal
`C`, by (N).  This gives item 1 for out-neighbourhoods, and the same argument
with `H` gives it for in-neighbourhoods.

For item 2, let `Q` be a clique with `m` vertices.  Every pair in `Q` carries
at least one oriented edge, so some `v ∈ Q` has at least `(m-1)/2`
out-neighbours in `Q`.  Those out-neighbours are pairwise adjacent, so they
have pairwise distinct `C`-values, all lying in `u_v F u_v^(-1)`.  Hence
`(m-1)/2 <= |F|`.  In-degrees give `(m-1)/2 <= |F_1|` in the same way.

Item 3 is the case of the complete graph on `Z` with vertex words `u_n` for
`x0^n`.  Its cliques are unbounded, so no constant `A_0` works, whatever the
words.  `QED`

## Scope

This does not bound the chromatic number.  The line digraph of a digraph `H`
satisfies the structural conclusion (N): the out-neighbours of `(a,b)` all
have the form `(b,.)`.  Its chromatic number is at least `log_2 chi(H)`.  So
(N) and the clique bound are compatible with infinite chromatic number.  The
surviving conjugate templates therefore live on shift-graph-like, clique-poor
graphs.

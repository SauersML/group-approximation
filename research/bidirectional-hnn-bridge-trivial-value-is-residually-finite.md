---
rg: 2
id: bidirectional-hnn-bridge-trivial-value-is-residually-finite
kind: claim
title: The bidirectional HNN bridges have residually finite value on the trivial group
distinct_from:
  exact-literal-e-fin-inf-switch: that is the countably generated FIN switch; this is the finitely generated bridge wrapped around it, and the new content is that the bridge's value on the trivial group is residually finite when the conjugation index runs over all of Z.
  mf-safe-asymmetric-hnn-replacement: that concerns the finite-presentation rope; this stays at recursive presentations and never compiles.
---

ESTABLISHED.  Let `C` be a countable group with a generating sequence
`(c_i)_(i in Z)` in which `c_i = 1` for every `i <= 0`.

**Three-generator bridge.**  Put `y_i = x^i y x^-i` in the free group `F(x,y)`
and

```text
B3(C) = < C * F(x,y), t | t y_i t^-1 = c_i y_i,  i in Z >.        (BB1)
```

**Two-generator bridge.**  Put `a_i = a^i b a^-i` and `b_i = b^i a b^-i` in
`F(a,b)` and

```text
B2(C) = < C * F(a,b), t | t a_i t^-1 = c_i b_i,  i in Z >.        (BB2)
```

Both are HNN extensions of the base `C * F`, both contain `C`, both are
finitely generated (`B3(C)` by `x,y,t` and `B2(C)` by `a,t`), and both are
recursively presented uniformly in a recursive presentation of `C`.  The
values on the trivial group are

```text
B3(1) = < x,y,t | [t, y_i] = 1, i in Z >   ~=  (F_oo x F_oo) x| Z,
B2(1) = < a,b,t | t a_i t^-1 = b_i, i in Z >,
```

and **both are residually finite**.  `B3(1)` embeds in `F_2 x F_2`.

## Proof

*HNN structure.*  The set `{y_i}` freely generates the normal closure of `y`
in `F(x,y)`, and `{c_i y_i}` is carried to `{y_i}` by the retraction
`C * F -> F` killing `C`, so it freely generates a free subgroup of the same
rank.  Hence `y_i -> c_i y_i` is an isomorphism between free subgroups and
`(BB1)` is an HNN extension; the base, hence `C`, embeds.  The same argument
with `{a_i}` (normal closure of `b`) and `{c_i b_i}` (retracting to `{b_i}`,
the normal closure of `a`) handles `(BB2)`.

*Generation.*  `c_i = t y_i t^-1 y_i^-1` shows `B3(C) = <x,y,t>`.  In
`(BB2)` the index `i = 0` gives `t b t^-1 = a`, so `b = t^-1 a t`, and then
`c_i = t a_i t^-1 b_i^-1`; thus `B2(C) = <a,t>`.

*Structure of `B3(1)`.*  Let `N_0` be the normal closure of `{y,t}`; the
quotient is `<x> ~= Z` and the extension splits.  Reidemeister--Schreier over
the transversal `{x^n}` presents `N_0` on `y_n = x^n y x^-n` and
`t_m = x^m t x^-m` with relators the conjugates `x^m [t,y_n] x^-m = [t_m,
y_(n+m)]`, i.e. exactly all `[t_m, y_n] = 1`.  So `N_0 = F(y_n) x F(t_m)` and
`B3(1) = (F_oo x F_oo) x| Z` with `x` shifting both indices.  The map

```text
x -> (x_1, x_2),   y -> (y, 1),   t -> (1, t)                     (BB3)
```

to `F(x_1,y) x F(x_2,t)` respects `(BB1)`, is injective on `N_0` because it
carries the free bases `{y_n}`, `{t_m}` onto free bases of the normal
closures of `y` and `t`, and its image of `N_0` meets `<(x_1^n,x_2^n)>`
trivially.  Hence `(BB3)` is injective and `B3(1) <= F_2 x F_2` is
residually finite.

*Residual finiteness of `B2(1)`.*  Write `F = F(a,b)`, `A = <<b>>_F`, `B =
<<a>>_F`, and let `sigma` be the automorphism of `F` swapping `a` and `b`.
Then `A = <a_i>`, `B = <b_i>`, `sigma(a_i) = b_i`, so `B2(1)` is the HNN
extension `< F, t | t x t^-1 = sigma(x), x in A >`.  Both `A` and `B` are
kernels of maps to `Z`, hence closed in the profinite topology of `F`.  Let
`g = f_0 t^(e_1) f_1 ... t^(e_n) f_n` be Britton-reduced.  Choose a
finite-index normal `M_0 <= F` with `f_j notin A M_0` whenever the pattern
forces `f_j notin A`, `f_j notin B M_0` whenever it forces `f_j notin B`, and
`f_j notin M_0` whenever `f_j != 1`; let `M` be the intersection of all
subgroups of index at most `[F:M_0]`, a characteristic subgroup of finite index
inside `M_0`.  Since `sigma(M) = M`,

```text
sigma(A cap M) = B cap M,
```

so `sigma` descends to an isomorphism `AM/M -> BM/M` and

```text
D = < F/M, t | t xbar t^-1 = sigmabar(xbar), xbar in AM/M >
```

is an HNN extension of a finite group.  `D` acts on its Bass--Serre tree with
finite stabilizers, so it is virtually free and residually finite.  The image
of `g` in `D` is still Britton-reduced by the choice of `M`, hence nontrivial,
and a finite quotient of `D` separates it.  Thus `B2(1)` is residually
finite.

## Why the index set is all of `Z`

With `i >= 0` only, the associated subgroup `<a^i b a^-i : i >= 0>` is not
profinitely closed in `F` (its closure contains every conjugate `a^i b a^-i`,
`i in Z`), and the corresponding value on `1` is the non-residually-finite
scaffold `(B1)` of `research/artifacts/fp-mf-pi2-compiler-audit-2026-08-25.md`.
Running the index over `Z` is what makes both associated subgroups normal
closures, hence closed, and makes the value residually finite.

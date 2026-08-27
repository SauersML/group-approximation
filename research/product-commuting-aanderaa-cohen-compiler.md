---
rg: 2
id: product-commuting-aanderaa-cohen-compiler
kind: claim
title: Making the embedded group commute with the whole insertion subgroup keeps the Aanderaa-Cohen compiler finitely presented and turns its last edge into a graph edge
distinct_from:
  mf-safe-asymmetric-hnn-replacement: that is the product-twist edge of the benign-witness rope; this is the Aanderaa--Cohen modular-machine compiler with one extra commutation relation, whose insertion edge is a graph over `A_+ x C`.
  aanderaa-rope-layers-are-mf-safe: that concerns Rotman's Turing-machine rope with letters `tau_j, d, sigma`; this is Cohen's modular-machine rope with letters `p, a_i, k`, modified at the insertion step.
---

ESTABLISHED.  Fix a finitely generated recursive presentation `C = < c_1,
..., c_n | S >`, closed under inverses (`c_(n+i) = c_i^-1`), and a modular
machine `M` of modulus `m > 2n` with `w_alpha(c) in S iff (alpha, 0) in
H_0(M)` for the `m`-ary codes `alpha in I` of positive words (Cohen,
*Combinatorial group theory*, §9.6; Chiodo--Vyas, §4.3).  Let `K_M` be the
modular-machine group of [[modular-machine-boone-group-is-mf]], `U = {t,
r_i, l_j}`, `t_alpha = t(alpha, 0)`.  Define

```text
H_2^0 = < K_M * F(b_1..b_n) * <d>, p | p t_alpha p^-1 = t_alpha w_alpha(b) d (alpha in I) >,
A     = < t, x, d, b, p >,      A_i = < t_i, x^m, b_i d, b, p >   (1 <= i <= 2n),
A_+   = < U, d, b, p >  <= H_2^0,
Gamma_a = < H_2^0, a_1..a_(2n) | a_i g a_i^-1 = psi_i(g), g in A >,        (PC1)
```

with `psi_i : A -> A_i` Cohen's isomorphism (`t -> t_i, x -> x^m, d -> b_i d,
b -> b, p -> p`).  Let `tau : A_+ -> C` be the homomorphism killing `U, d,
p` and sending `b_j -> c_j` (it is a homomorphism because `p t_alpha p^-1 =
t_alpha w_alpha(b) d` maps to `w_alpha(c) = 1`, true exactly for halting
`alpha`, and `t_alpha in <U>` iff `alpha` halts).  Put

```text
H_3'' = < Gamma_a *_(A_+) (A_+ x C), k | k (a,1) k^-1 = (a, tau(a)), a in A_+ >.   (PC2)
```

Then:

1. `H_3''` is finitely presented, uniformly in the presentation of `C`,
   by the presentation with generators of `K_M, b, d, p, a_i, k, c_j` and
   relators: those of `K_M`; `p t p^-1 = t d`; the `psi_i` relations on the
   generators of `A`; `[c_j, g] = 1` for `g in {t, r_i, l_j, d, b, p}`;
   `k g k^-1 = g` for `g in {t, r_i, l_j, d, p}` and `k b_j k^-1 = b_j c_j`.
   No relator of `S` and no `p t_alpha p^-1` with `alpha != 0` is needed.
2. `C` embeds in `H_3''`.
3. `H_3''` is MF whenever `Gamma_a` is MF, `A_+` is closed in the
   finite-quotient topology of `Gamma_a`, and for every finite-index normal
   `C' <= C` some finite quotient of `Gamma_a` has `A_+ cap ker <= tau^-1(C')`
   (and `C` is residually finite).

## Proof

*1.*  Conjugating `p t_alpha p^-1 = t_alpha w_alpha(b) d` by `a_i` gives `p
t_(i + m alpha) p^-1 = t_(i + m alpha) w_alpha(b) b_i d`, and `w_(i+m alpha)
= w_alpha c_i` in Cohen's digit convention; starting from `alpha = 0` this
yields every `p`-relation.  For halting `alpha`, `t_alpha in <U>` is fixed by
`k`, as is `p`, so `k (p t_alpha p^-1) k^-1 = p t_alpha p^-1 = t_alpha
w_alpha(b) d`, while directly `k (t_alpha w_alpha(b) d) k^-1 = t_alpha
w_alpha(b) w_alpha(c) d` because the `c_j` commute with the `b_j`; hence
`w_alpha(c) = 1`, i.e. every relator of `S` follows.  So the finite
presentation defines `H_3''`.

*2.*  `psi_i` is an isomorphism between subgroups of `H_2^0` (Cohen's step
(15) is about `H_2`, and `H_2 = H_2^0 *_(F(b)) (F(b) x C)` contains `H_2^0`),
so `Gamma_a` is an HNN extension of `H_2^0`; `A_+ x C` is amalgamated with
`Gamma_a` along `A_+`; and `(a,1) -> (a, tau(a))` is an isomorphism `A_+ x 1
-> graph(tau)`.  Thus `(PC2)` is an HNN extension of an amalgam containing
`C`.

*3.*  `(PC2)` is `(AE1)` with `Gamma = Gamma_a`, `S = A_+`, `Q = C`; apply
[[twisted-edge-over-amalgamated-product-base-is-mf]].

## Consequence for the compiler

On the `INF` branch of the exact switch with the two-generator bridge,
`C = B2(1)` is residually finite, so the finite-presentation
`Pi^0_2`-completeness of MF reduces to the three conditions in 3 on the
`C`-free rope group `Gamma_a`, which depends on the machine but not on the
group structure of `C`: [[c-free-aanderaa-rope-is-mf-with-fine-quotients]].
On the `FIN` branch `E <= C <= H_3''`.

---
rg: 2
id: relator-width-over-nilpotent-by-locally-finite-groups-proof
kind: route
title: Fix the marked quotient, then run the nilpotent template inside its finite-index kernel with products of relator conjugates as relators
target: relator-width-over-nilpotent-by-locally-finite-groups
requires: [perfect-group-relator-width-over-nilpotent-groups]
---

`F = F(X)`, `N = <<R>>`, `G = F/N`. `Cons_K^Q(S)` denotes products of at most `K` `Q`-conjugates
of elements of `S^(+-1)`. Let `Q`, `P`, `a` be as in the theorem, with `P` nilpotent of class `c`
and `Q/P` in `V`.

## 1. Finitely many marked quotients

Let `alpha : F -> Q`, `x -> a_x`, and `pi : Q -> Q/P`. The image `B = pi alpha (F)` is an
`X`-generated group in `V`, so it is a quotient of `F_V(X)`, which is finite. So the kernel
`F_b = ker(pi alpha)` is one of the finitely many normal subgroups `M` of `F` containing the verbal
kernel of `F -> F_V(X)`. Every constant below depends on `M` only. Take `K(G, V)` to be the largest
of these finitely many constants.

Fix such `M = F_b`. It has finite index in `F`, so it is free of finite rank (Nielsen--Schreier).

## 2. The top identity

`B = F/M` is finite. The image of `N` in `B` is a normal subgroup, and `B/(NM/M)` is a finite
quotient of `G`, hence trivial. So `NM = F`. For each `x in X` fix a word
```text
P_x = prod_(i = 1..k_x) u_i r_i^(e_i) u_i^-1      (u_i in F, r_i in R, e_i = +-1)
```
with `y_x := P_x^-1 x in M`. Such a word exists because `x in NM`.

## 3. Relators inside the kernel

**Lemma.** `(N ∩ M) [M, M] = M`.

*Proof.* `NM = F`, so `M / (N ∩ M) ≅ MN/N = G`. So `M / ((N ∩ M)[M, M])` is an abelian quotient of
`G`. `G` is perfect, since an abelian quotient of a finitely generated group with no finite
quotient is finitely generated abelian with no finite quotient, hence trivial. So the quotient is
trivial.

`M/[M, M]` is free abelian of finite rank, so there is a finite set `S ⊂ N ∩ M` whose images span it.
Each `s in S` lies in `N`. So fix an expression `s = prod_(j = 1..l_s) v_j r_j^(+-1) v_j^-1` with
`v_j in F`, and put `L = max_s l_s`.

## 4. The nilpotent template inside `M`

Apply `perfect-group-relator-width-over-nilpotent-groups` (its stated form: a free group on a finite
set, and a finite subset whose exponent-sum vectors span the abelianization) to the free group `M`
and the finite set `S`. For every `y in M` there are `K_S(y)` and one sign-and-letter pattern such
that, for every `k >= 1`,
```text
y ∈ Cons_(K_S(y))^M (S) · gamma_(k+1)(M) ,
```
with conjugators in `M`. The theorem's proof also works with an arbitrary free basis of `M`, since
it uses only the Lie ring of `M`.

Each `M`-conjugate `d s^(+-1) d^-1` is a product of `l_s <= L` conjugates `(d v_j) r_j^(+-1) (d v_j)^-1`.
So
```text
y_x ∈ Cons_(L K_S(y_x))^F (R) · gamma_(k+1)(M)      for every k .
```

## 5. Evaluation

- `alpha(M) = alpha(F_b) <= P`, because `pi alpha` kills `M`. So
  `alpha(gamma_(c+1)(M)) <= gamma_(c+1)(P) = 1`.
- Take `k = c` in Section 4 and apply `alpha`. Conjugators go to `alpha(F) <= Q`, so
  `alpha(y_x) ∈ Cons_(L K_S(y_x))^Q (R(a))`.
- `alpha(P_x) ∈ Cons_(k_x)^Q (R(a))`.
- So `a_x = alpha(P_x) alpha(y_x) ∈ Cons_(k_x + L K_S(y_x))^Q (R(a))`.

The bound depends on `M`, `P_x`, `S` and the chosen expressions, and not on `Q`, `P`, `c` or `a`.
There are finitely many `M`. This proves the theorem.

## 6. The special cases

- **Fitting quotient.** The finitely many groups of order `<= N` generate a variety `V_N`. `V_N` is
  locally finite, because `F_(V_N)(X)` embeds in the product of the groups `H^(H^X)` over those
  finitely many `H`. Every `Q` with `|Q/F(Q)| <= N` has `Q/F(Q)` in `V_N`, and `F(Q)` is nilpotent.
- **Congruence towers.** The kernel of `GL_n(F_q[t]/(t^k)) -> GL_n(q)` consists of the matrices
  `1 + t A`. It has order a power of `p`, so it is nilpotent, and the quotient has order at most
  `|GL_n(q)|`. The same holds for `Z/p^k`. For a subgroup `Q`, intersect with the kernel.
- **`P = 1`.** Immediate.

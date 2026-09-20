---
rg: 2
id: leavitt-cone-cover-far-cross-relators-uniform-proof
kind: route
title: Average a generator-level commutator over one Kazhdan block, then over the opposite one, and derive the overlap and middle-index relators by fixed Steinberg identities through R_0
target: leavitt-cone-cover-far-cross-relators-are-uniformly-small
requires:
  - leavitt-cuntz-cone-halves-have-rf-amalgam-cover
  - ershov-jaikin-kassabov-steinberg-groups-have-property-t
  - property-t-implies-property-fa
---

Notation as in the target. `||.||_2` is the trace norm of `(M, tau)`. For unitaries `u, v`,

```text
||[u, v] - 1||_2 = ||u v u^* - v||_2 = ||u v - v u||_2 ,                                  (0)
```

and `||.||_2` is invariant under left and right multiplication by unitaries.

## Step 1. The blocks are Kazhdan, with generator sets that do not depend on the block

Fix `m` with `3 <= m <= 17` and let `S_m^+ = {x_ij(c) : i != j <= m, c in {1, s_1, s_2, q}}` in `St_m(R_+)`.

**`S_m^+` generates `St_m(R_+)`.** `R_+` is additively spanned by monomials in `s_1, s_2, q`. For a monomial
`c c'` with `c` a letter, take `k` distinct from `i` and `j`. Then `x_ij(c c') = [x_ik(c), x_kj(c')]`, so by
induction on length every `x_ij(monomial)` lies in `<S_m^+>`. Additivity `x_ij(a + b) = x_ij(a) x_ij(b)` does the
rest.

**`(T)`.** `R_+` is a finitely generated ring. By `ershov-jaikin-kassabov-steinberg-groups-have-property-t` (type
`A_(m-1)`, rank `>= 2`), `St_m(R_+)` has `(T)`. So `(St_m(R_+), S_m^+)` has a Kazhdan constant `kappa_m^+ > 0`. The
same holds for `R_-` with `S_m^- = {x_ij(c) : c in {1, t_1, t_2, q}}`.

Put `kappa = min_(m, +-) kappa_m^(+-) > 0`.

**Transfer to the blocks.** For `I ⊆ {1, ..., 20}` with `|I| = m`, relabel the indices by an order-preserving
bijection `{1, ..., m} -> I`. The corner embedding gives a homomorphism `St_m(R_+) -> Delta_+`. Its image is `G_I^+`,
and it sends `S_m^+` onto `S_I^+ = {x_ij(c) : i, j in I}`.

A unitary representation of `G_I^+` pulls back to one of `St_m(R_+)` with the same invariant vectors. So
`(G_I^+, S_I^+)` has Kazhdan constant `>= kappa`, and likewise `(G_J^-, S_J^-)`.

**Kazhdan estimate used below.** Let `pi` be a unitary representation of a group `G` with Kazhdan pair `(S, kappa)`
on a Hilbert space `H`. Let `P` be the projection onto `H^G`. For `v in H` put `w = v - P v`. The representation of
`G` on the orthogonal complement of `H^G` has no nonzero invariant vector, and `pi(s) w - w = pi(s) v - v`. Hence

```text
||v - P v|| <= kappa^(-1) max_(s in S) ||pi(s) v - v||,
||pi(g) v - v|| = ||pi(g) w - w|| <= 2 ||w||   for every g in G.                        (1)
```

## Step 2. Generator commutators are fixed words in the k_i

Let `I, J` be disjoint blocks, and take `s = x_ij(c) in S_I^+` and `t = x_kl(c') in S_J^-`. Then `{i,j} ∩ {k,l}` is
empty, so the Steinberg relation `[x_ij(c), x_kl(c')] = 1` holds in `Delta = St_20(R)`. Hence `[s, t] in K`.

`K` is the normal closure of `k_1, ..., k_r` in `Gamma`. So `[s, t]` is a product of `N(s,t)` conjugates of
`k_i^(+-1)`. There are finitely many triples `(I, J, s, t)`; let `N_0` be the maximum of `N(s,t)`. For every
homomorphism `rho`, the unitary invariance of `||.||_2` and the triangle inequality give

```text
||rho([s, t]) - 1||_2 <= N_0 delta.                                                      (2)
```

## Step 3. Double averaging: (U1)

Let `L^2(M, tau)` be the GNS space of the trace. `G_I^+` acts on it unitarily by `alpha(g) X = rho(g) X rho(g)^*`;
this is unitary because `tau` is tracial.

**First averaging.** Fix `t in S_J^-` and put `X = rho(t)`. By (0) and (2), for `s in S_I^+`,

```text
||alpha(s) X - X||_2 = ||[rho(s), rho(t)] - 1||_2 <= N_0 delta.
```

By (1) applied to `(G_I^+, S_I^+, kappa)`, `||alpha(g) X - X||_2 <= 2 N_0 delta / kappa` for every `g in G_I^+`. By
(0),

```text
||[rho(g), rho(t)] - 1||_2 <= 2 N_0 delta / kappa        (g in G_I^+, t in S_J^-).           (3)
```

**Second averaging.** Fix `g in G_I^+` and put `Y = rho(g)`. Let `G_J^-` act by `beta(h) Y = rho(h) Y rho(h)^*`.
For `t in S_J^-`, (0) and (3) give

```text
||beta(t) Y - Y||_2 = ||[rho(t), rho(g)] - 1||_2 = ||[rho(g), rho(t)] - 1||_2 <= 2 N_0 delta / kappa.
```

The middle equality holds because `[u, v]^(-1) = [v, u]` and `||w^(-1) - 1||_2 = ||w - 1||_2` for unitary `w`. By (1)
applied to `(G_J^-, S_J^-, kappa)`, `||beta(h) Y - Y||_2 <= 4 N_0 delta / kappa^2` for every `h in G_J^-`. With (0)
this gives `(U1)`, with `C_1 = 4 N_0 / kappa^2`:

```text
||[rho(g), rho(h)] - 1||_2 <= C_1 delta        (g in G_I^+, h in G_J^-).                     (U1)
```

## Step 4. All far cross relators: (U2)

Take `a in R_+`, `b in R_-`, and Steinberg-commuting pairs `(i,j)`, `(k,l)` with `j != k` and `i != l`.

**Lemma 4.0 (conjugation transfer).** Let `u, v, X` be unitaries. Suppose `||[u, X] - 1||_2 <= e_u` and
`||[v, X] - 1||_2 <= e_v`. Then `||[[u, v], X] - 1||_2 <= 2 e_u + 2 e_v`.

*Proof.* By (0), the quantity is `||c X c^* - X||_2` with `c = u v u^* v^*`. Conjugate `X` successively by `v^*`,
`u^*`, `v`, `u`. Each step moves it by at most `e_v`, `e_u`, `e_v`, `e_u` respectively, by (0) and unitary
invariance. ∎

If `u` commutes with `X` exactly, then `e_u = 0` and the bound is `2 e_v`.

**Case (a): disjoint pairs.** `{i,j} ∩ {k,l}` is empty. Since `n = 20`, there are indices `m` and `m'` giving
disjoint blocks `I = {i,j,m}` and `J = {k,l,m'}`. `(U1)` gives `C_1 delta`.

**Case (b): one shared row.** Here `i = k` and `j != l`. Choose `m ∉ {i,j,l}`.
- In `Delta_+`, `x_ij(a) = [x_im(1), x_mj(a)]`.
- `u = x_im(1) in Delta_0 ⊆ Delta_-` commutes exactly with `x_il(b)`. This is a Steinberg relation in `Delta_-`,
  valid since `m != i` and `i != l`.
- `v = x_mj(a)` and `x_il(b)` have disjoint index pairs, so case (a) applies.

Lemma 4.0 gives `2 C_1 delta`.

**Case (c): one shared column.** Here `j = l` and `i != k`. Choose `m ∉ {i,j,k}`.
- In `Delta_+`, `x_ij(a) = [x_im(a), x_mj(1)]`.
- `x_mj(1) in Delta_0` commutes exactly with `x_kj(b)` in `Delta_-`.
- `x_im(a)` and `x_kj(b)` have disjoint index pairs.

Lemma 4.0 gives `2 C_1 delta`.

**Case (d): same root.** Here `(k,l) = (i,j)`. Choose `m ∉ {i,j}`.
- In `Delta_+`, `x_ij(a) = [x_im(a), x_mj(1)]`.
- `x_mj(1)` commutes exactly with `x_ij(b)` in `Delta_-`, since `j != i` and `m != j`.
- `x_im(a)` and `x_ij(b)` share row `i`, so case (b) gives `2 C_1 delta`.

Lemma 4.0 gives `4 C_1 delta`.

These are all cases, since `j != k` and `i != l`. This proves `(U2)`.

The symmetric statement with `a in R_-` and `b in R_+` follows in the same way, by exchanging the roles of the
halves: `(U1)` is symmetric under exchanging `I` and `J`.

## Step 5. Middle-index coherence: (U3)

Take distinct `i, j, k, l`, `a in R_+` and `b in R_-`. In `Gamma` put

```text
A = x_ij(a) in Delta_+,   B = x_jl(1) in Delta_0,   C = x_lk(b) in Delta_-,
D = [A, B] = x_il(a)      (a Steinberg relation of Delta_+),
E = [B, C] = x_jk(b)      (a Steinberg relation of Delta_-).
```

The quantity in `(U3)` is `||rho([A, E]) - rho([D, C])||_2`. We write `A` for `rho(A)` and so on.

**Exact relations used.** `[x_pq(c), x_rs(c')] = 1` whenever `q != r` and `p != s`. So `DB = BD` holds in
`Delta_+` (pairs `(i,l)`, `(j,l)`: `l != j`, `i != l`), and `EC = CE` holds in `Delta_-` (pairs `(j,k)`, `(l,k)`:
`k != l`, `j != k`).

**Far pairs used.** `(A, C) = (x_ij(a), x_lk(b))` and `(D, E) = (x_il(a), x_jk(b))` have disjoint index pairs, so
case (a) of Step 4 gives `||[A, C] - 1||_2 <= C_1 delta` and `||[D, E] - 1||_2 <= C_1 delta`.

**Expansion.** Put `C' = A C A^(-1)`. From `A B A^(-1) = [A, B] B = D B` and `E = B C B^(-1) C^(-1)`,

```text
[A, E] = (A E A^(-1)) E^(-1) = D B C' B^(-1) D^(-1) C'^(-1) . C B C^(-1) B^(-1).        (5.1)
```

**First replacement, cost `2 C_1 delta`.** `||C' - C||_2 = ||[A, C] - 1||_2 <= C_1 delta`, and `C'` occurs twice in
(5.1). Replacing both occurrences by `C`, and using unitary invariance,

```text
[A, E] ≈ D (B C B^(-1)) D^(-1) (B C^(-1) B^(-1)) = [D, B C B^(-1)] = [D, E C].
```

(Since `D` commutes with `B`, this also equals `B [D, C] B^(-1)`.)

**Second replacement, cost `C_1 delta`.** `[D, E C] = D E C D^(-1) C^(-1) E^(-1)`. Replace `D E` by `E D`, at cost
`||[D, E] - 1||_2 <= C_1 delta`. The result is `E D C D^(-1) C^(-1) E^(-1) = E [D, C] E^(-1)`.

**Third replacement, cost `2 C_1 delta`.** Since `E` commutes with `C`,
`E [D, C] E^(-1) = [E D E^(-1), C]`. Now `||E D E^(-1) - D||_2 = ||[E, D] - 1||_2 <= C_1 delta`, and it occurs twice.
Replacing both gives `[D, C]`.

**Total.** `||rho([A, E]) - rho([D, C])||_2 <= (2 + 1 + 2) C_1 delta = 5 C_1 delta`, which is `(U3)`.

The case `a in R_-`, `b in R_+` is the same computation with the halves exchanged. `B = x_jl(1)` lies in `Delta_0`,
so it belongs to both halves.

## Step 6. Kazhdan subgroups of Gamma fix a vertex

`Gamma = Delta_+ *_(Delta_0) Delta_-` acts on its Bass--Serre tree `T` without inversions. The vertex stabilizers
are the conjugates of `Delta_+` and `Delta_-`.

If `H <= Gamma` has `(T)`, then by `property-t-implies-property-fa` it has Serre's property FA. So `H` fixes a vertex
of `T`, and it is conjugate into `Delta_+` or into `Delta_-`.

Let `I ⊇ {1, 2, 3}`. The elements `a = x_12(s_1)` and `b = x_12(t_1)` of `<G_I^+, G_I^->` lie in
`Delta_+ \ Delta_0` and `Delta_- \ Delta_0` respectively, because `s_1 ∉ R_0` and `t_1 ∉ R_0`. So `ab` is a
cyclically reduced word of length 2 in the amalgam. By Serre (*Trees*, I.1.3) it acts hyperbolically on `T` and fixes
no vertex. Hence `<G_I^+, G_I^->` fixes no vertex, and it does not have `(T)`.

This is exactly where double averaging stops. It needs a Kazhdan group that contains all of the moving elements. The
groups `G_I^+` and `G_J^-` supply this for far pairs, but no Kazhdan subgroup of `Gamma` contains mixed words
`g_1 h_1 ... g_m h_m` in a single block.

## Constants

`C_1 = 4 N_0 / kappa^2` depends only on the finite normal generating set `{k_i}` of `K` and on the Kazhdan constants
of the finitely many pairs `(St_m(R_+-), S_m^+-)`. It does not depend on `rho`, on `(M, tau)`, on the dimension, or
on the ring elements `a` and `b`. The argument uses only unitary invariance of `||.||_2` and the tracial GNS
representation, so it holds in any tracial von Neumann algebra. ∎

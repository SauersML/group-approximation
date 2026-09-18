---
rg: 2
id: lifts-add-no-unipotent-divisibility-proof
kind: route
title: Direct proof by a transfer lemma through Q-free normal subgroups with central quotients
target: lifts-add-no-unipotent-divisibility
requires: []
---

Direct proof. Not independently reviewed. Write `Q-free` for "contains no
subgroup isomorphic to `(Q,+)`". Subgroups of Q-free groups are Q-free.

## Step 1. Transfer lemma

Let `N <= K` be normal in `E`, with `N` Q-free and `K/N` central in `E/N`. Let
`H <= E` and `D <= H` with `D ~ (Q,+)`. Put `M = H ∩ N`, a Q-free normal
subgroup of `H`, and assume

- (i) `D ∩ M = 1`, and
- (ii) the image of `D` in `H/M` meets `Z(H/M)` trivially.

Then `D` embeds in `E/K`.

*Proof.* Let `pi : E -> E/N`. Then `pi(H) ~ H/M`, and by (i) `pi|_D` is
injective. Since `K/N` is central in `E/N`, the intersection `pi(H) ∩ K/N` lies
in `Z(pi(H))`. By (ii), `pi(D) ∩ Z(pi(H)) = 1`, so `pi(D) ∩ K/N = 1`. Hence
`D ~ pi(D)` embeds in `(E/N)/(K/N) ~ E/K`. ∎

## Step 2. The listed groups satisfy (i) and (ii) for every Q-free normal subgroup

Write `u(q) = I + q E_12`, and `e` for an elementary matrix `I + t E_ij`
(`i ≠ j`, `t ≠ 0`). Two facts are used throughout:

- a matrix commuting with every `E_ij` (`i ≠ j`) is scalar;
- if `g e g^-1 e^-1 = lambda I`, then `g e g^-1 = lambda e`. The left side is
  unipotent and `lambda e` has the single eigenvalue `lambda`, so `lambda = 1`.

**(a) `PSL_n(Q)`, `n >= 2`.** It is simple, which is classical (Jordan--Dickson;
see E. Artin, *Geometric Algebra*, Ch. IV). So its only Q-free normal subgroup
is `1`: `PSL_n(Q)` itself contains the image of `u(Q)`, which is `~ Q` because
`u(Q)` meets the scalars trivially. Its centre is trivial. Take `D` to be the
image of `u(Q)`.

**(b) `SL_n(Q)`.** Let `M` be normal and not central. Its image in `PSL_n(Q)` is
a nontrivial normal subgroup, hence everything, so `M Z = SL_n(Q)` with
`Z = Z(SL_n(Q))`. `SL_n(Q)` is perfect (classical, as in (a)), so
`SL_n(Q) = [MZ, MZ] = [M, M] <= M`. Then `M` contains `u(Q)` and is not Q-free.
So every Q-free normal `M` is central, `M <= {±I}`.
- (i) holds: `u(Q)` meets the scalars trivially.
- (ii): let `x = diag(2, 1/2, 1, ..., 1)`. Then `x u(t) x^-1 = u(4t)`, so
  `[u(q), x] = u(q) u(-4q) = u(-3q)`. For `q ≠ 0` this is not `±I`, so
  `u(q) M` is not central.

**(c) `GL_n(Q)`.** Let `M` be normal and not central, and pick `g in M` not
scalar. Some `e` does not commute with `g`. Then `c = [g, e]` lies in
`M ∩ SL_n(Q)` and `c ≠ I`, and by the eigenvalue fact `c` is not scalar. So
`M ∩ SL_n(Q)` is a noncentral normal subgroup of `SL_n(Q)`. By (b) it is all of
`SL_n(Q)`, so `M` contains `u(Q)`. Hence every Q-free normal `M` is scalar.
- (i) holds as in (b).
- (ii): with `x = diag(2, 1, ..., 1)`, `[u(q), x] = u(q) u(-2q) = u(-q)`, which
  is not scalar for `q ≠ 0`.

**(d) `PGL_n(Q)`.** Let `M` be Q-free normal, with preimage `M~` in
`GL_n(Q)`. If `M~` is not central then by (c) it contains `SL_n(Q)`, and `M`
contains the image of `u(Q)`, which is `~ Q`. That contradicts Q-freeness, so
`M~` is scalar and `M = 1`. The centre is trivial: if `g` is central modulo
scalars then every `[g, e]` is scalar, hence `I` by the eigenvalue fact, so `g`
commutes with every `E_ij` and is scalar. Take `D` to be the image of `u(Q)`.

**(e) `Aff(Q) = {x -> ax + b}`.** Take `D` to be the translations `tau_b`.
Conjugating `tau_b` by `x -> ax` gives `tau_(ab)`. So a normal `M` with
`M ∩ D ≠ 1` contains all of `D`. Hence a Q-free normal `M` has `M ∩ D = 1`.
- Then `[M, D] <= M ∩ D = 1`, so `M` centralizes `D`.
- The centralizer of `D` is `D`: `x -> ax + b` commutes with `tau_1` only if
  `a = 1`. So `M <= D ∩ M = 1`.
- The centre is trivial: a central element is a translation `tau_c`, and
  `tau_c` commutes with `x -> 2x` only if `c = 0`.

**(f) `B_2(Q)`, the invertible upper triangular 2x2 matrices.** Take
`D = u(Q)`. Conjugation by `diag(a,1)` sends `u(q)` to `u(aq)`, so a normal `M`
with `M ∩ D ≠ 1` contains `D`. Hence a Q-free normal `M` has `M ∩ D = 1` and
`[M, D] = 1`, so `M` lies in the centralizer of `D`, `{lambda u(t)}`.
- For `m = lambda u(t) in M` and `d = diag(2,1)`, `d m d^-1 m^-1 = u(t)`, which
  lies in `M ∩ D = 1`. So `t = 0`, and `M` is scalar.
- (ii): `[u(q), diag(2,1)] = u(-q)` is not scalar for `q ≠ 0`.

**(g) `U_3(Q)`, the upper unitriangular 3x3 matrices.** Write `x_ij(t)`, and
let `a(g)` and `c(g)` be the `(1,2)` and `(2,3)` entries. The commutator
`[g, h]` equals `x_13(a(g) c(h) - a(h) c(g))`. Take `D = x_12(Q)`.
- If a normal `M` has an element `g` with `a(g) ≠ 0`, then
  `[g, x_23(t)] = x_13(a(g) t) in M` for all `t in Q`, so `M ⊇ x_13(Q) ~ Q`.
  The same happens if `c(g) ≠ 0`.
- So a Q-free normal `M` lies in `Z(U_3(Q)) = x_13(Q)`, and (i) holds.
- (ii): `x_12(a) M` is central only if `x_13(at) = [x_12(a), x_23(t)]` lies in
  `M` for all `t`. For `a ≠ 0` that forces `M ⊇ x_13(Q)`, contradicting
  Q-freeness.

## Step 3. Conclusion

Suppose a group `H'` containing one of the listed groups `H` embeds in `E`. Then
`H` embeds in `E`. `M = H ∩ N` is a Q-free normal subgroup of `H`, so by Step 2
conditions (i) and (ii) hold for the subgroup `D` named there. By Step 1, `D ~ Q`
embeds in `E/K`, contradicting the hypothesis on `E/K`. ∎

## The special cases

- **Lifts to `R`.** Every lift `f` of an orientation-preserving circle
  homeomorphism satisfies `f(x + 1) = f(x) + 1`. The lifts of the identity are the
  translations `x -> x + k`, `k in Z`, which therefore form a central subgroup
  `Z` of `Homeo_Z(R)`. For the group `Gamma~` of all lifts of `Gamma`, the
  quotient `Gamma~/Z` is `Gamma`. Take `N = 1` and `K = Z`.
- **`T-bar`.** `T <= V` (survey arXiv:2306.16356v3, §4.1). `V` is Q-free by
  Higman (survey Theorem 4.4: "In particular, Q does not embed into V").
- **Coverings.** Take `N = K = Delta`, the deck group.

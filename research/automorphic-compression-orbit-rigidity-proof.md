---
rg: 2
id: automorphic-compression-orbit-rigidity-proof
kind: route
title: Proof that automorphic compressions are profinitely dense, so their finite orbits in approximable coset spaces are full orbits
target: automorphic-compressions-have-no-approximable-hilbert-hotel
requires: []
---

Notation is as in the target. Chabauty convergence `H_n -> H` means: for every `gamma in Gamma`,
`gamma in H_n` for all large `n` iff `gamma in H`. For `x in X` fix `gamma_x` with `x = gamma_x H`
and `gamma_(x_0) = 1`, and let `phi_n : X -> X_n = Gamma/H_n` be `phi_n(x) = gamma_x H_n`.

## Step 0: local agreement

This repeats Step 7 of `schreier-hilbert-hotel-ring-reduction-proof`. Let `F subset X` and
`E subset Gamma` be finite. For all large `n`:

- *Injectivity.* `phi_n` is injective on `F`. For `x != x'` in `F`, the element
  `gamma_(x')^(-1) gamma_x` is not in `H`, hence not in `H_n` for large `n`. There are finitely many pairs.
- *Equivariance.* `phi_n(e x) = e phi_n(x)` for `e in E` and `x in F`. The element
  `gamma_(ex)^(-1) e gamma_x` lies in `H`, hence in `H_n` for large `n`. There are finitely many pairs.

## Step 1: automorphic compressions satisfy (PE)

Let `Gamma` be finitely generated, `alpha in Aut(Gamma)`, and `A = alpha(Gamma_0) <= Gamma_0`.

1. *Characteristic subgroups.* For `m >= 1` let `K_m` be the intersection of all subgroups of index at
   most `m`. A finitely generated group has only finitely many subgroups of each finite index, since each
   one is determined by a transitive action on a finite set, given by images of the generators. So `K_m`
   has finite index. Automorphisms permute subgroups of a given index, so `alpha(K_m) = K_m`, and `K_m`
   is normal.
2. *Equal images.* Let `pi_m : Gamma -> Gamma/K_m`. Then `alpha` induces an automorphism `alpha_m` of
   `Gamma/K_m` with `pi_m o alpha = alpha_m o pi_m`. So
   `pi_m(A) = alpha_m(pi_m(Gamma_0))` has the same finite cardinality as `pi_m(Gamma_0)`, and it is
   contained in it because `A <= Gamma_0`. Hence `pi_m(A) = pi_m(Gamma_0)`, that is,
   `A K_m = Gamma_0 K_m`.
3. *All finite-index normal subgroups.* Let `N` be normal of index `m`. Then `K_m <= N`, so
   `A N = A K_m N = Gamma_0 K_m N = Gamma_0 N`.

This proves (PE). No property of `Gamma_0` beyond `alpha(Gamma_0) <= Gamma_0` is used.

## Step 2: the Lemma, in a slightly stronger form

Assume (PE), with `S_0` a finite generating set of `Gamma_0` and `S_A` a finite generating set of `A`.

**Lemma+.** Let `W subset X` be finite and `A`-invariant. Then `W` is `Gamma_0`-invariant, and `A` and
`Gamma_0` induce the same permutation group on `W`.

*Proof.* Apply Step 0 with `F = W u S_0^(+-1) W` and `E = S_0^(+-1) u S_A^(+-1)`, and fix one large
`n`. Put `W_n = phi_n(W)`.

1. *`W_n` is `A`-invariant.* For `a in S_A^(+-1)` and `x in W` we have `a phi_n(x) = phi_n(a x)`, and
   `a x in W`.
2. *`A` and `Gamma_0` act on `X_n` through the same permutations.* Let `N` be the kernel of the action
   of `Gamma` on the finite set `X_n` (the normal core of `H_n`). It is normal of finite index, so by
   (PE) every `gamma in Gamma_0` is `a nu` with `a in A` and `nu in N`. So `gamma` and `a` induce the
   same permutation of `X_n`.
3. *`W_n` is `Gamma_0`-invariant.* This follows from 1 and 2.
4. *Pull back.* For `s in S_0^(+-1)` and `x in W`, `phi_n(s x) = s phi_n(x) in W_n = phi_n(W)`. Both
   `s x` and `W` lie in `F`, where `phi_n` is injective. So `s x in W`, and `W` is `Gamma_0`-invariant.
5. *Same permutation group.* `phi_n : W -> W_n` is a bijection that intertwines the generators
   `S_0^(+-1)`, so it conjugates the homomorphism `Gamma_0 -> Sym(W)` to `Gamma_0 -> Sym(W_n)`. The
   same holds for `A <= Gamma_0`. By 2, `Gamma_0` and `A` have the same image in `Sym(W_n)`. Hence they
   have the same image in `Sym(W)`.

The Lemma of the target is the case `W = A x`, with `A x` finite.

## Step 3: the Theorem

By Step 1, (PE) holds. Suppose `g in Gamma_0` and `W = A q` is finite, where `q = g x_0`.

- By Step 2, `W` is `Gamma_0`-invariant.
- So `x_0 = g^(-1) q in W = A q`, which gives `q in A x_0`, that is, `g in A H`.

This contradicts the second clause of (HH). So (HH) has no witness. Only the following were used:

- `Gamma` and `Gamma_0` are finitely generated;
- `alpha in Aut(Gamma)` and `alpha(Gamma_0) <= Gamma_0`;
- `H` is a Chabauty limit of finite-index subgroups.

The `alpha`-invariance of `H`, (IS), profinite closedness and `t` play no role.

*Consistency check.* In `BS(1,2) = <s, tau | tau s tau^(-1) = s^2>` with `alpha = Ad(tau)` and
`Gamma_0 = <s>`, (PE) says that `s` and `s^2` generate the same cyclic group in every finite quotient.
This is the familiar fact that `s` has odd order there. So in approximable `BS(1,2)`-sets every finite
`s^2`-cycle is an `s`-cycle.

## Step 4: the Corollary (tensor-lamp template)

Hypotheses are as in the Corollary of the target. Write `B = M_d(k)^(tensor X)` and `B_Y` for the
tensors supported in `Y subset X`. Two standard facts about restricted tensor products of central simple
algebras over `k` are used:

- each `b in B` has a least finite support `supp(b)`, and `M_F meet M_(F') = M_(F meet F')`;
- the centralizer of `M_d(k)_(y)` in `M_F` is `M_(F \ {y})`, for `y in F`.

`R = B x| Gamma` is a free left `B`-module on the `u_gamma`.

1. *The sites of `R_0` form a `t`-stable union of finitely many orbits.* Let `P` be the finite set of
   sites of the generators of `R_0`, and put `Y_0 = Gamma_0 P`. Then `R_0` contains `M_d(k)` at every
   site of `Y_0`, by conjugating with the `u_gamma`, `gamma in Gamma_0`. Also
   `R_0 <= sum_(gamma in Gamma_0) B_(Y_0) u_gamma`, which is a subring.
   - For `p in P` and non-scalar `a`, `psi(a_(p)) = a_(t p)` lies in `R_0`. Comparing the coefficient at
     `u_1` gives `a_(t p) in B_(Y_0)`, so `t p in Y_0`.
   - Hence `t(Y_0) = A t(P) <= Gamma_0 Y_0 = Y_0`.
2. *The root lives on finite orbits off `Y_0`.* Put `Z = supp(z)`.
   - `z` commutes with `u_gamma` for `gamma in Gamma_0`, so `gamma . z = z` and `gamma Z = Z`. Thus `Z`
     is a finite union of finite `Gamma_0`-orbits.
   - `z` commutes with `M_d(k)_(y)` for every `y in Y_0`. If `y in Z`, the centralizer fact puts `z` in
     `M_(Z \ {y})`, contradicting minimality. So `Z meet Y_0 = {}`.
3. *`t` permutes finite orbits.* Let `O` be a finite `Gamma_0`-orbit. Then `t(O) = A t(y)` for any
   `y in O`, a finite `A`-orbit. By Step 2 it is a `Gamma_0`-orbit.
   - Let `Phi_0` be the finite set of finite `Gamma_0`-orbits contained in `Y_0`. By part 1,
     `t(Phi_0) <= Phi_0`.
   - `t` is injective on points, hence on orbits. So `t` permutes `Phi_0`.
   - Consequently a finite orbit `O` with `t(O) <= Y_0` lies in `Phi_0`. The orbits in `Z` are not in
     `Phi_0`, by part 2. So `W = t(Z)` is disjoint from `Y_0`.
4. *`psi(z)` centralizes `R_0`.* `psi(z)` is `z` transported along `t`, so `psi(z) in M_W`.
   - It commutes with `M_d(k)` at every site of `Y_0`, since `W meet Y_0 = {}`.
   - `W = t(Z)` is `A`-invariant. For `a = alpha(delta)` with `delta in Gamma_0`, we get
     `a . psi(z) = psi(delta . z) = psi(z)`.
   - By Step 2, every `gamma in Gamma_0` induces on `W` the same permutation as some `a in A`. The
     action on `M_W` depends only on that permutation. So `gamma . psi(z) = a . psi(z) = psi(z)`, and
     `u_gamma` commutes with `psi(z)`.

So `psi(z) p psi(z)^(-1) - p = 0` for every `p in R_0`, and the ideal of (R5) is `0`, not `R`.

Steps 1-3 prove the Theorem and refute `schreier-hilbert-hotel-compression-data-exist`. Step 4 proves
the Corollary. ∎

---
rg: 2
id: rank-weighted-head-kill-hypotheses-hold-in-a-sofic-group-proof
kind: route
title: Read the affine finitary linear group as a tracial countermodel, verify the rank-weighted hypotheses on its compression cell, and locate the failing step
target: rank-weighted-head-kill-hypotheses-hold-in-a-sofic-group
requires:
  - affine-finitary-linear-radical-is-the-whole-kernel
  - ascending-hnn-finitary-linear-family-is-sofic-non-mf
  - finitary-linear-extension-sofic-and-no-finite-normal-subgroup
  - affine-semidirect-sl3-source-has-property-t
  - binary-finitary-transvection-uniformly-controls-active-rank
  - uniform-finite-support-rank-gap-upgrades-compression-collapse
artifacts:
  - research/artifacts/compression-finitary-linear-action-theorem-2026-09-08.md
  - research/artifacts/rank-weighted-locally-finite-compression-2026-09-08.md
---

Notation as in the target. `T_pq = I + E_pq` over `F_2`, `[g,h] = g h g^-1 h^-1`, and `V` acts on
`F_2^(X)` by permuting the basis, so `g T_pq g^-1 = T_(gp,gq)`.

## Step 1. Finite generation, soficity, radical (items 3, 5, part of 6)

`affine-finitary-linear-radical-is-the-whole-kernel` (with `m = 2`) states:
- `G` is finitely generated, sofic, and has no nontrivial finite normal subgroup;
- the coset action of `V` on `X` is faithful;
- `D_G(L) = Rad_MF(G) = K`, and `K` is infinite, locally finite and simple.

`L` has property (T) by `affine-semidirect-sl3-source-has-property-t`. This gives item 5, and item 3 except
`C_G(K) = 1`.

## Step 2. The compression cell (items 1 and 2)

This is the cell of Theorem 1 in the finitary action artifact.
- Let `x = L` be the base coset and `x_i = u^i x`. Every `x_i` with `i <= 0` is `L`-fixed, the `x_i` are
  pairwise distinct, and `ux` is not `L`-fixed. Choose `l in L` with `l ux != ux`, that is, `l` not in
  `alpha(L)`. For example `l` is the translation by a standard basis vector.
- Put `a = x_-1`, `b = x_-3`, `p = (x_-1 x_-2)(x_-3 x_-4) in K`, and `v = u p`.
  - `p` centralizes `L`, so `v L v^-1 = u L u^-1 = alpha(L)`, of index `8` in `L`.
  - `v x = ux` and `v b = b`.
- Put `c = T_xb`. Since `x` and `b` are `L`-fixed, `c in C_G(L)`.

Then `v c v^-1 = T_(ux, b)`, and conjugating by `l` fixes the column `b` and moves the row to `l ux`. So

```text
d = [v c v^-1, l] = T_(ux,b) T_(l ux, b) = I + (e_ux + e_(l ux)) e_b^*,
```

where the cross term vanishes because `b != l ux`.
- `N = (e_ux + e_(l ux)) e_b^*` has rank one and satisfies `N^2 = 0`, because `b` is not in `{ux, l ux}`.
- So `d` is a transvection of `K`: `d != 1` and `d^2 = 1`.
- By definition `d` is a defect generator, so `d in D_G(L)`.

## Step 3. The uniform support bound (item 4)

For a finite set `S` of points, let `K_S = GL(F_2^S) = SL_|S|(F_2)`, embedded as the identity off `S`.
Take `S` to contain the support `{ux, l ux, b}` of `d`, so `|S| >= 3`.
- The `K_S` exhaust `K` along any increasing exhaustion of `X` by such sets.
- In `K_S`, `d` is a transvection. All transvections of `SL_m(F_2)` are conjugate to `e_12(1)`.
- Section 5 of the rank-weighted artifact, which is the claim
  `binary-finitary-transvection-uniformly-controls-active-rank`, gives
  `codim Fix sigma(K_S) <= (4 - 2^(3-m)) rank(sigma(d) - I)` for every finite-dimensional unitary
  representation `sigma`.

So the hypothesis `(1)` of `uniform-finite-support-rank-gap-upgrades-compression-collapse` holds with
`C = 4`. Its conclusion kills `d` in every norm-corona homomorphism, consistently with Step 1.

## Step 4. `C_G(K) = 1` (rest of item 3)

Write an element of `G` as `k q` with `k in K`, `q in V`. Let `B` be a finite block of points such that `k`
is the identity on `e_w` for `w` not in `B` and preserves the span of `e_B`. Then `k^-1` has the same
property, and for `p, r` outside `B` we have `k T_pr k^-1 = T_pr`.

**Every `q != 1` in `V` moves infinitely many points of `X`.** Write `V_0 = Z[1/2]^3 x| SL_3(Z)`, the
kernel of the exponent map `V -> Z`. Every point stabilizer is a conjugate of `L`, so it lies in `V_0`.
- If `q` is not in `V_0`, then `q` fixes no point.
- If `q = (w, I)` with `w != 0`, use the points `u^j x`, `j >= 0`, which are pairwise distinct. The
  stabilizer of `u^j x` is `alpha^j(L) = 2^j Z^3 x| SL_3(Z)`, and it does not contain `q` once `2^j`
  does not divide `w`.
- If `q = (w, g)` with `g != I`, choose `f in Z^3` with `(g - I) f != 0` and put `t_j = 2^-j f`. The points
  `tau_(t_j) x` are pairwise distinct, since their differences are not in `Z^3`. Also `q` fixes
  `tau_t x` iff `w + (g - I) t in Z^3`. For large `j`, the 2-adic denominator of `(g - I) t_j` exceeds
  that of `w`, so `q` moves `tau_(t_j) x`.

Now suppose `k q` centralizes `K`. Then for all `y != z`,

```text
T_yz = k q T_yz q^-1 k^-1 = k T_(qy,qz) k^-1 .
```

- **Case `q != 1`.** The set `F = B union q^-1 B` is finite. Take `y` outside `F` with `qy != y`, and take
  any `z` outside `F`, `z != y`. Then `qy` and `qz` lie outside `B`, so the right side equals
  `T_(qy,qz) != T_yz`. This is a contradiction.
- **Case `q = 1`.** Then `k` commutes with every `T_yz`, so `k E_yz = E_yz k` for all `y != z`. This forces
  `k` to be a scalar, and over `F_2` the only scalar is `I`.

Hence `C_G(K) = 1`. The same step gives `Z(K) = 1`.

## Step 5. The tracial embedding (item 6)

By Step 1, `G` is sofic. So there are maps `s_n : G -> Sym(k_n)` with:
- `|{i : s_n(g) s_n(h) i != s_n(gh) i}| / k_n -> 0`;
- `|{i : s_n(g) i = i}| / k_n -> delta_(g,1)`.

Embed each `M_(k_n)(C)` unitally and trace-preservingly into `R`. This gives a unital trace-preserving
embedding of the tracial ultraproduct of the `M_(k_n)(C)` into `R^omega`. The permutation matrices define a
homomorphism `pi : G -> U(R^omega)` with `tau(pi(g)) = delta_(g,1)`.

In particular `pi(d)` is a self-adjoint unitary with trace `0`. Its moving projection
`p_d = (1 - pi(d))/2` therefore has `tau(p_d) = 1/2`, and `pi` is injective. So no argument whose inputs
are only items 1 to 4 can conclude `pi(d) = 1` in every homomorphism `G -> U(R^omega)`. This proves the
Corollary's class kill.

## Step 6. Where the transcription dies: commutant transport

Run Sections 3 and 4 of the rank-weighted artifact with `V_n` replaced by the exact homomorphism `pi`, with
`Tr / r_n` replaced by `tau / tau(p_d)`, and with `|x|_2 = tau(x* x)^(1/2)`.

**(a) Cutoffs survive.**
- Choose the chains `K_0 <= ... <= K_N` of `(4)` inside the exhaustion of Step 3, and define
  `p_i`, `e_N` as in `(5)` using `pi`.
- The Section 5 count is still valid in the factor `R^omega`. There, the multiplicity of a character `chi`
  of a root group `U` becomes the trace of the spectral projection `avg_U conj(chi)(b) pi(b)`. Levi
  elements conjugate these projections by unitaries of `pi(K_S)`, so the traces are equal. This gives
  `tau(p_i) <= 4 tau(p_d)` and `tau(e_N) <= 4 tau(p_d) = 2`, together with `e_N p_d = p_d`.
- Since `pi` is exact, `epsilon_n = 0` in `(7)`, and `(8)` gives `||[pi(g), e_N]||_op <= 1/N`. The weight
  `tau(p_d) = 1/2` is fixed, so the conversion `(9)` is not even needed.

**(b) The null subgroup survives, and `d` is not in it.**
- The set `N_e = {g : |(pi(g) - 1) e_N|_2 -> 0}` is a normal subgroup, by the Section 4 computation with
  zero multiplicativity error.
- But `(pi(d) - 1) e_N = -2 p_d e_N = -2 p_d`, whose norm is `2 tau(p_d)^(1/2) = sqrt 2`. So `d` is not in
  `N_e`.

**(c) The first failing step is transport.**
- The vectors `x_N = pi(c) e_N` are bounded, with `|x_N|_2 <= sqrt 2`. They are asymptotically central for
  `L` in `L^2(R^omega)` under `Ad pi`, because `[pi(h), x_N] = pi(c)[pi(h), e_N]` for `h in L`.
- Put `w = v c v^-1`. The transported vectors are
  `y_N = Ad pi(v) x_N = pi(w) e_N + O(1/N)`.
- For `l` as in Step 2, `l w = d w l`, because `[l, w] = d^-1 = d`. Using the asymptotic centrality of
  `e_N` twice,

```text
|[pi(l), y_N]|_2 = |(pi(d) - 1) pi(w l) e_N|_2 + o(1) = |(pi(d) - 1) e_N|_2 + o(1) -> sqrt 2 .
```

So a bounded, asymptotically `L`-central sequence has an image under `Ad pi(v)` that is not asymptotically
`L`-central. In this setting, transport of `pi(c) e` along `v` is equivalent to `d in N_e`, which is the
conclusion.

**(d) Why the operator-norm proof does not transcribe.**
- Section 2 of the artifact gets transport from `Ad V(u)* P Ad V(u) <= P` for the Kazhdan projection `P`.
  Stable finiteness of the norm corona of the `d_n^2`-dimensional conjugation spaces then turns this
  inequality into equality.
- Here the corresponding operator is `P_L` on `L^2(R^omega)`, and it satisfies
  `Ad pi(v) P_L Ad pi(v)* = P_(vLv^-1) >= P_L` inside `B(L^2(R^omega))`, which is not finite.
- The vector in (c) witnesses that the inequality is strict.
- A finite-dimensional Hilbert-Schmidt model would still need `Ad V_n` to be asymptotically multiplicative
  in operator norm on the conjugation space, which `2`-norm asymptotic multiplicativity does not supply.

## Step 7. The index character and the separating invariant

- In `G`, `[L : vLv^-1] = [L : alpha(L)] = 8`. The map `g -> 8^(e(g))`, where `e : G -> Z` is the exponent of
  `u` (it kills `K` and `V_0`), restricts to the relative index on every compressor of `L` in `G`. So the
  index character extends to the whole ambient group.
- `ascending-hnn-finitary-linear-family-is-sofic-non-mf` proves soficity by passing through this extension:
  `G` is a split extension by `Z` of a locally residually finite group.
- In `EL_n(J)` with `n >= 3` we have `x_ij(r) = [x_ik(r), x_kj(1)]`, so the group is perfect and has no
  nonzero homomorphism to `Z`. The positive Fredholm index of the corner compressors
  (`jacobson-corner-compressor-hulls-carry-fredholm-index`) therefore does not extend.
- `G` surjects onto `Z`, so it does not have property (T). `EL_n(J)` is Kazhdan (Ershov and
  Jaikin-Zapirain, for finitely generated rings and `n >= 3`, as used in `affine-semidirect-sl3-source-has-property-t`
  and in the binary Jacobson claims).

Every argument that uses only items 1 to 4 applies to `G`, and `G` is hyperlinear with `pi(d) != 1`. So a
proof that the Jacobson head dies in every hyperlinear model must use some property that `G` lacks, such as
perfectness or ambient property (T).

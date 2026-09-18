---
rg: 2
id: infranormal-sources-never-saturate-sofic-mapping-tori-proof
kind: route
title: Roots have degree zero, so each defect generator owns a bead; the bead-residue intersections then form a central series
target: infranormal-sources-never-saturate-sofic-mapping-tori
requires:
  - infranormal-kernel-sources-die-in-sofic-mapping-tori
---

Notation is that of the claim. Commutators are `[a,b] = a b a^-1 b^-1`. For normal subgroups
`X, Y, Z` of `K`: `[X,Y]` is normal, `[X,Y] <= X ∩ Y`, and `[X, YZ] = [X,Y][X,Z]`, from
`[x, yz] = [x,y] . y [x,z] y^-1`. A product of finitely many normal subgroups of `K` is a normal
subgroup and does not depend on the order.

## Step 0: imported from `infranormal-kernel-sources-die-in-sofic-mapping-tori`

- **(B0)** For `h in G` of degree `d`: `h A_j h^-1 = A_(j+d)` and `h C_K(A_j) h^-1 = C_K(A_(j+d))`.
  Every `A_j` and every `C_K(A_j)` is normal in `K`.
- **(IS0)** `C_G(L) = C_G(N)`. This is the only use of soficity, through
  `sofic-groups-kill-rigid-compression-defects` applied to the infranormal pair `L <= K`.
- **(IS1)** A generator `[u c u^-1, l]` with `u` not strict is trivial. A strict `u` has degree
  `m != 0` and `A_m < N`.
- **(P)** After replacing `s` by `s^-1`, the strict degrees are positive. With `P` the semigroup
  they generate, `A_(j+p) <= A_j` for all `j` and all `p in P`.

Suppose `D_G(L) = K`. Since `K != 1`, some generator is nontrivial, so a strict compressor
exists. Let `g = gcd P`.

**Frobenius.** Some `F` has `ng in P` for all `n >= F`. With (P):

```text
A_(j+ng) <= A_j     and     C_K(A_j) <= C_K(A_(j+ng))      for all j and all n >= F.     (F)
```

So `W_rho = < A_j : j = rho mod g >` is a directed union: any finitely many of these `A_j` lie
in one of them, of small enough index. Hence `W_rho` is a normal subgroup of `K`, and every
element of `W_rho` lies in a single `A_j` with `j = rho (mod g)`.

## Step 1: (DZ) roots have degree zero

Let `c in C_G(L)`, of degree `d`. By (IS0), `c` centralizes `N`, so `c N c^-1 = N`. By (B0),
`A_d = N = A_0`.

Suppose `d != 0`. Conjugating `A_d = A_0` by powers of `s^d` gives `A_(kd) = A_0` for every
`k in Z`. Fix a strict degree `m`, so `A_m < A_0`. Conjugation by `s^((i-1)m)` preserves strict
inclusion, so `A_(im) < A_((i-1)m)` for every `i`. Chaining `|d|` of these gives
`A_(|d| m) < A_0`, strictly. But `|d| m` is a multiple of `d`, so `A_(|d| m) = A_0`. This is a
contradiction. Hence `d = 0`, and `C_G(L) <= K`.

Now let `u` be strict of degree `m`, let `c in C_G(L)` and `l in L`, and put `x = u c u^-1`.
- `c in C_G(N)` gives `x in C_G(u N u^-1) = C_G(A_m)`, and `x in K` since `c in K`.
- So `x in C_K(A_m)`. This is normal in `K` and contains `x`, so it contains `[x,l]`.
- `x in K` and `l in N`, with `N` normal in `K`. So `x l x^-1 in N`, and `[x,l] in N`.

So every nontrivial generator lies in `C_K(A_m) ∩ A_0` for some `m in P`. By (B0), the
`G`-conjugates of this normal subgroup of `K` are the groups `C_K(A_(e+m)) ∩ A_e`, `e in Z`. So

```text
K = D_G(L) <= < C_K(A_(e+m)) ∩ A_e : e in Z, m in P >.                        (DZ)
```

The point, compared with (C) of the parent node, is the factor `A_e`: the generator lies in the
bead of the residue whose deep bead it centralizes. This uses `x in K`, which is where (DZ) is
needed.

## Step 2: (BF)

- *Finite product.* The right side of (DZ) is the directed union of finite products of its
  generating normal subgroups. `K` is Kazhdan, hence finitely generated, so
  `K = F_1 F_2 ... F_r` with `F_k = C_K(A_(e_k + m_k)) ∩ A_(e_k)` and `m_k in P`.
- *Group by residue.* `m_k = 0 (mod g)`, so both indices of `F_k` have the residue of `e_k`. For
  each residue `rho` pick `a_rho = rho (mod g)` and `b_rho = rho (mod g)` with
  `a_rho <= e_k - Fg` and `b_rho >= e_k + m_k + Fg` for every `k` in that class. By (F),
  `F_k <= C_K(A_(b_rho)) ∩ A_(a_rho)`. So

  ```text
  K = product over rho of ( C_K(A_(b_rho)) ∩ A_(a_rho) ).
  ```

- *Shift and enlarge.* Let `(j_rho)` be any tuple with `j_rho = rho (mod g)`. Choose `n` so
  negative that `j_rho - b_rho - ng >= Fg` for every `rho`. Conjugation by `s^(ng)` fixes `K`
  and, by (B0), turns the display into the same one with `a_rho, b_rho` replaced by
  `a_rho + ng, b_rho + ng`. Now (F) gives `C_K(A_(b_rho + ng)) <= C_K(A_(j_rho))`, and
  `A_(a_rho + ng) <= W_rho` by definition. Each factor only grows, so

  ```text
  K = product over rho of Y_rho,      Y_rho = C_K(A_(j_rho)) ∩ W_rho.            (BF)
  ```

In particular `K = W_0 W_1 ... W_(g-1) = I_1`.

(A residue class containing no `e_k` gets any `a_rho, b_rho`; the extra factor only enlarges
the product.)

## Step 3: (NC)

Fix a set `S` of residues mod `g`, and let `x in W_S`.
- For each `rho in S`, `x in W_rho`, so `x in A_(j_rho)` for some `j_rho = rho (mod g)` (Step 0).
  For `rho notin S` choose `j_rho = rho`.
- Put `X = intersection_{rho in S} A_(j_rho)`. It is normal in `K`, contains `x`, and lies in
  `W_S`.
- Take the factorization (BF) for this tuple. For `rho in S`, `Y_rho <= C_K(A_(j_rho)) <= C_K(X)`,
  so `[X, Y_rho] = 1`. For `rho notin S`, `[X, Y_rho] <= X ∩ Y_rho <= W_S ∩ W_rho = W_(S u {rho})`.
- So `[X, K] = product over rho of [X, Y_rho] <= product over rho notin S of W_(S u {rho}) <= I_(|S|+1)`.

Hence `[x, k] in I_(|S|+1)` for every `x in W_S` and `k in K`, so `[W_S, K] <= I_(|S|+1)`.
For `|S| = g` the product is empty, and `W_S <= Z(K)`.

Every `W_S` is normal in `K`, and `I_(k+1) <= I_k` because `W_(S u {rho}) <= W_S`. Using
`[XY, K] = [X,K][Y,K]` for normal `X, Y`:

```text
[I_k, K] = product over |S| = k of [W_S, K] <= I_(k+1)     (1 <= k <= g),   I_(g+1) = 1.
```

With `I_1 = K` (Step 2), induction gives `gamma_k(K) <= I_k` for the lower central series, so
`gamma_(g+1)(K) = 1`. `K` is nilpotent of class at most `g`.

## Step 4: the kill

- A nilpotent group is amenable, and an amenable Kazhdan group is finite. So `K` is finite.
- Then `N` is finite, and `A_m = s^m N s^-m` has the same order as `N`. So `A_m < N` is
  impossible for the strict degree `m`.
- This contradicts the existence of a strict compressor. So `D_G(L) != K`.

## Checks

- **g = 1.** (BF) reads `K = C_K(A_j)` for every `j`, so every translate is central. This is
  (IS3) of the parent node.
- **g = 2.** `I_2 = W_0 ∩ W_1` is central, and `K/I_2` is abelian. This is stronger than
  (NB4), which needed the overlap `E_0` to be central.
- **Calibration** of `necklace-defects-need-deep-bead-overlaps`. There `K = H^3` with `H`
  infinite Kazhdan, so `K` is infinite and not nilpotent, and the theorem rules out
  `D_G(L) = K` directly. That node reached the same conclusion through the proper subgroup
  `(H^+)^3`.
- **Where soficity is used.** Only in (IS0), through Step 1 and the membership `x in C_K(A_m)`.
  Everything else is group theory, finite generation of `K`, and "nilpotent Kazhdan implies
  finite".
- **Where infranormality is used.** `N = <<L>>^K` must be normal in `K` and satisfy (IS0). For a
  source whose compressors in `K` generate a proper subgroup, (IS0) gives only
  `C_G(L) = C_G(<<L>>^M)` for Kazhdan `M` with `L` infranormal in `M`. That closure is not normal
  in `K`, so Steps 2 and 3 do not apply.

---
rg: 2
id: fpbs-burnside-positive-l2-betti-forces-simple-subgroup-proof
kind: route
title: Bound beta_1 of every finite-index subgroup by the common upper cost, take the smallest finite-index subgroup, and kill its normal subgroups with Gaboriau's Theorem 6.8 and cyclic centralizers
target: fpbs-burnside-positive-l2-betti-forces-simple-subgroup
requires:
  - fpbs-burnside-common-upper-cost
  - fpbs-burnside-embedding-input
  - fpbs-burnside-normal-closure-split
  - fpbs-amen2-betti-cost-input
  - fpbs-gaboriau-l2-betti-normal-subgroup-and-finite-index
  - fpbs-finite-cost-normal-subgroup-infimal-cost-one
---

Full written proof. This is not a formal verification.

**Inputs.**
- **[CU]** `fpbs-burnside-common-upper-cost`. Every infinite `K <= B(m,n)` has `C^*(K) = c_n <= 2 - 2/n`.
- **[Z]** `fpbs-burnside-embedding-input`. Centralizers of nontrivial elements are cyclic, hence finite, since the
  exponent is `n`.
- **[NC]** `fpbs-burnside-normal-closure-split`. For `m >= 3`, the normal closure of `x_1` is infinite with infinite
  quotient `B(m-1,n)`.
- **[BC]** `fpbs-amen2-betti-cost-input`. For a countably infinite group `K` and any free p.m.p. action `a` of `K`,
  `beta_1(K) <= C(a) - 1`.
- **[G6.8]** and **[IDX]** `fpbs-gaboriau-l2-betti-normal-subgroup-and-finite-index`, items (a) and (b).
- **[FC]** `fpbs-finite-cost-normal-subgroup-infimal-cost-one`, used only in item 3.

**Step 0 (uniform bound).** Let `K <= G` be infinite.
- `K` is countably infinite and has free p.m.p. actions, for instance its Bernoulli shift.
- Each of them has cost at most `C^*(K) = c_n` by [CU], so by [BC] `beta_1(K) <= c_n - 1 <= 1 - 2/n`.
- In particular `beta_1(K)` is finite.

**Step 1 (normal subgroups of infinite index).** Let `K <= G` be infinite, and let `M` be a normal subgroup of `K`
that is infinite and of infinite index.
- `M` is an infinite subgroup of `G`, so `beta_1(M)` is finite by Step 0.
- `K/M` is infinite, so [G6.8] gives `beta_1(K) = 0`.

**Item 1.** Let `m >= 3`. By [NC], `G` has an infinite normal subgroup of infinite index, so `beta_1(G) = 0` by
Step 1.

**Step 2 (finite normal subgroups).** Let `K <= G` be infinite, and let `F` be a finite normal subgroup of `K`. Then
`F = 1`.
- Suppose `F` is nontrivial.
- `K` acts on `F` by conjugation through the finite group `Aut(F)`, so the kernel `C_K(F)` has finite index in `K`
  and is infinite.
- Pick `f` in `F` other than `1`. Then `C_K(F) <= C_G(f)`, which is finite by [Z]. This is a contradiction.

**Item 2.** Let `H <= G` be infinite with `b = beta_1(H) > 0`.
- *Index bound.* Let `L <= H` have finite index. Then `L` is infinite, and [IDX] gives
  `beta_1(L) = [H : L] b`. Step 0 gives `beta_1(L) <= c_n - 1`. So `[H : L] <= (c_n - 1)/b`.
- *Smallest subgroup.* The indices of finite-index subgroups are bounded integers, so choose `H_0` of largest index.
  - Let `L` be any finite-index subgroup. Then `L cap H_0` has finite index, and its index is at least `[H : H_0]`;
    by maximality it is equal to `[H : H_0]`. So `L cap H_0 = H_0`, that is, `H_0 <= L`.
  - Every conjugate of `H_0` is a finite-index subgroup, so it contains `H_0`, and it has the same index as `H_0`,
    so it equals `H_0`. Hence `H_0` is normal in `H`.
  - `H_0` is infinite, and `beta_1(H_0) = [H : H_0] b > 0` by [IDX]. Also `beta_1(H_0) <= c_n - 1` by Step 0.
- *Simplicity.* Let `M` be a nontrivial normal subgroup of `H_0`.
  - If `M` is finite, Step 2 (with `K = H_0`) gives `M = 1`, a contradiction.
  - If `M` is infinite of infinite index in `H_0`, Step 1 gives `beta_1(H_0) = 0`, a contradiction.
  - Otherwise `M` has finite index in `H_0`, hence in `H`, so `H_0 <= M` and `M = H_0`.
  - So `H_0` is simple.

**Item 3.** Let `S <= G` be infinite with `beta_1(S) > 0`.
- *Bound on `c_n`.* Take any free action `a` of `S`. By [BC] and [CU], `1 + beta_1(S) <= C(a) <= c_n`.
- *Actions of different cost.* Let `m >= 3`, and let `N` be the normal closure from [NC].
  - Every free action of `N` has cost at most `c_n`, so the infimal cost of `N` is finite.
  - By [FC], `B(m,n)` has free actions of cost arbitrarily close to `1`.
  - By the definition of `C^*`, it also has free actions of cost arbitrarily close to `c_n > 1`.

**Why this kills the route as recorded.**
- `fpbs-burnside-positive-upper-cost` recorded the L2 route as dead because a positive `beta_1` "would raise both
  costs together".
- By item 3, that is not the right obstruction: a positive `beta_1` of any infinite subgroup `S` would give `c_n > 1`
  directly, because [CU] makes `C^*` common to all infinite subgroups, and `beta_1` bounds every action from below.
- The true obstruction is items 1 and 2. `beta_1` vanishes on `B(m,n)` for `m >= 3` and on every infinite subgroup
  that is not virtually an infinite simple group. What survives is a question about infinite simple subgroups of
  large odd Burnside groups, with `beta_1` in `(0, 1 - 2/n]`.

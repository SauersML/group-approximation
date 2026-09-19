---
rg: 2
id: leavitt-mf-null-root-corner-is-equivalent-to-the-goal-proof
kind: route
title: The centralizer of the Leavitt root carries a copy of the whole group, so the root corner is MF-null iff the radical is full
target: leavitt-mf-null-root-corner-is-equivalent-to-the-goal
requires:
  - mf-null-corner-criterion-needs-faithful-ce-trace
  - leavitt-steinberg-map-iso-from-rank-three
  - binary-leavitt-all-ranks-full-mf-radical
  - full-leavitt-idempotent-defect-saturation
---

Notation is as in the target. `[g,h] = g h g^(-1) h^(-1)`. The Steinberg relations in `St_n(A)`, for distinct indices,
are:

```text
x_ij(a) x_ij(b) = x_ij(a+b),
[x_ij(a), x_jk(b)] = x_ik(ab)                (i, j, k distinct),
[x_ij(a), x_kl(b)] = 1                       (j != k, i != l).
```

**Use of the requirements.**
- `binary-leavitt-all-ranks-full-mf-radical` is used in step 4 only for its T-free part, the ring isomorphisms `Theta_n`,
  and in step 7 for its Property (T) conclusion.
- Steps 1 to 6 use no Property (T).

## Step 1. A corner representation restricts to the centralizer (proves the first implication of (S))

Let `z` in `G` have order `m`. Put `S = sum_(j<m) z^j`, so `zS = S` and `S^2 = mS`. Then `q = q_z = 1 - S/m` is a
self-adjoint idempotent, and `S q = S - S^2/m = 0`.

Let `phi : q C[G] q -> Q_k` be a unital star homomorphism, so `phi(q) = 1`. For `g` in `C_G(z)`, `g` commutes with `S`
and hence with `q`, so `g q = q g q` lies in the corner. Define `rho(g) = phi(g q)`.

- **Multiplicative.** `g q h q = g h q^2 = g h q`, so `rho(gh) = rho(g) rho(h)`, and `rho(1) = phi(q) = 1`.
- **Unitary.** `rho(g)^* = phi(q g^(-1)) = phi(g^(-1) q) = rho(g^(-1))`.

So `rho : C_G(z) -> U(Q_k)` is a group homomorphism. Moreover,

```text
sum_(j<m) rho(z)^j = phi(S q) = 0.
```

Since `Q_k != 0` and `m >= 1`, this forces `rho(z) != 1`. So `z` is not in `Rad_MF(C_G(z))`. Contrapositive: if `z` lies
in `Rad_MF(C_G(z))`, no such `phi` exists, and the corner is MF-null.

The second implication of (S) is part (A) of `mf-null-corner-criterion-needs-faithful-ce-trace`, applied with `B` the
corner and `Phi` the identity.

For `Delta`, `m = 2`, `q_z = P_z`, and `rho(z) = phi(z P_z) = phi(-P_z) = -1`.

## Step 2. The centralizer of `x_13(a)` (for (R))

Let `n >= 4` and `J = {1, ..., n} \ {1, 3}`, which has at least two elements. By the third Steinberg relation,
`z = x_13(a)` commutes with:

- `x_kl(r)` for `k, l` in `J` (since `3 != k` and `1 != l`);
- `x_1l(b)` for `l` in `J` (since `3 != 1` and `1 != l`);
- `x_l3(b)` for `l` in `J` (since `3 != l` and `1 != 3`).

Let `iota : St_(n-2)(A) -> St_n(A)` relabel the indices `1, ..., n-2` increasingly onto `J`. It respects the defining
relations, so it is a homomorphism, and by the first item its image `M` lies in `C(z) = C_(St_n(A))(z)`.

## Step 3. The commutator chain (proves (R))

Let `l = iota(1)` and `m = iota(2)`, which are distinct elements of `J`. By the second Steinberg relation,

```text
x_1m(a) = [x_1l(a), x_lm(1)],        z = x_13(a) = [x_1m(a), x_m3(1)].
```

All five elements lie in `C(z)`, by Step 2. Let `rho : C(z) -> U(Q_k)` be any homomorphism.

- `rho o iota` is a corona homomorphism of `St_(n-2)(A)`, so it kills `Rad_MF(St_(n-2)(A))`, which contains `x_12(1)` by
  hypothesis. So `rho(x_lm(1)) = 1`.
- Then `rho(x_1m(a)) = [rho(x_1l(a)), 1] = 1`.
- Then `rho(z) = [1, rho(x_m3(1))] = 1`.

As `rho` was arbitrary, `z` lies in `Rad_MF(C(z))`. By Step 1, the corner `q_z C[St_n(A)] q_z` is MF-null.

The identities of Steps 2 and 3 are sanity-checked, as images in `EL_20(M_3(F_2))` with the index bookkeeping of
`n = 20`, by `experiments/leavitt-corner-centralizer-2026-09-17/check_centralizer_chain.py`. It checks 667 identities,
and a control confirms that `x_31(1)` does not commute with `z`. The proof itself uses only the Steinberg relations.

## Step 4. `St_18(R)` and `Delta` are isomorphic, without (T)

- By (KH2) of `leavitt-steinberg-map-iso-from-rank-three` (Khanh, Theorem 5.4, a purely algebraic comparison of presentations, imported from the literature),
  `St_18(R) -> GL_18(R)` and `St_20(R) -> GL_20(R)` are isomorphisms.
- The prefix-code maps `Theta_n : M_n(R) -> R` of `binary-leavitt-all-ranks-full-mf-radical-proof` are unital ring
  isomorphisms. They induce group isomorphisms `GL_18(R) = R^x = GL_20(R)`.
- Hence `St_18(R)` is isomorphic to `Delta`.
- `Rad_MF` is invariant under group isomorphism. So if `Rad_MF(Delta) = Delta`, then `Rad_MF(St_18(R)) = St_18(R)`, and
  in particular `x_12(1)` lies in it.

## Step 5. Implications 1 ⇒ 3 ⇒ 2 of (E)

Assume item 1. By Step 4, `x_12(1)` lies in `Rad_MF(St_18(R))`. Apply Step 3 with `A = R`, `n = 20` and `a = q`. In
characteristic two, `z` is an involution, so it has finite order. This gives item 3, and Step 1 then gives item 2.

## Step 6. Implication 2 ⇒ 1 of (E)

This is the route `leavitt-mf-null-root-corner-closes-full-radical`, which is sound as an implication.

- Part (A) of `mf-null-corner-criterion-needs-faithful-ce-trace` gives `z` in `Rad_MF(Delta)`.
- `z` normally generates `Delta` (`full-leavitt-idempotent-defect-saturation`).
- `Rad_MF(Delta)` is normal, so `Rad_MF(Delta) = Delta`.

Steps 1 to 6 use no Property (T), so (E) is proved without (T).

## Step 7. Property (T) corollary

`binary-leavitt-all-ranks-full-mf-radical` shows that every homomorphism from `GL_20(R)`, and hence from `Delta`, to an
MF group is trivial. The image of `Delta` under a homomorphism to `U(Q_k)` is a countable subgroup of `U(Q_k)`, hence MF.
So item 1 holds, and by Step 5 so do items 2 and 3.

This uses Property (T), through the rank-twelve compressor. It is recorded only to show that the literal hole
`leavitt-root-corner-algebra-is-mf-null` is true, and that its open content is the T-free proof alone.

## Remark: why the equivalence is not formal

`z in Rad_MF(Delta)` alone does not obviously make the corner MF-null. A unital corner representation into `Q_k` need not
come from a representation of `C[Delta]`, and there is no norm-corona induction from the corner. Step 1 replaces
induction with a restriction to the centralizer.

This is what makes the equivalence specific: the centralizer of the Leavitt root contains a rank-18 Steinberg group,
which by Morita and (KH2) is the whole group again.

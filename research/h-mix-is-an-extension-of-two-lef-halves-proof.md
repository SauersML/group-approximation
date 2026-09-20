---
rg: 2
id: h-mix-is-an-extension-of-two-lef-halves-proof
kind: route
title: Right S is locally nilpotent on the finitary row windows and transcendental on symbols, so the S-oriented double parabolic splits into two LEF halves
target: h-mix-is-an-extension-of-two-lef-halves
requires:
  - jacobson-rank-three-parabolics-are-lef
  - binary-jacobson-el2-is-lef
  - p22-double-parabolic-is-not-lef
artifacts:
  - experiments/h-mix-dihedral-window-2026-09-17/check_dihedral_window.py
---

Notation is as in the target. `J` has `F`-basis `S^i T^j`, with
`(S^a T^b)(S^c T^d) = S^a T^(b-c+d)` if `b >= c`, and `S^(a+c-b) T^d`
otherwise. LEF is meant in the finite-subset sense of
`jacobson-rank-three-parabolics-lef-proof`.

## Step 0. Imports

- (I1) `G_1 = J^2 x| EL_2(J)` (column parabolic) is LEF.
  From `jacobson-rank-three-parabolics-are-lef`.
- (I2) `EL_2(J)` is LEF. From `binary-jacobson-el2-is-lef`.
- (I3) The certificate `(u, g, e, r1, r2)` and Theorem (a) of
  `p22-double-parabolic-is-not-lef`. There, over `F_2`, `r1 = x_34(1)` and
  `r2 = x_43(S) x_34(1)`.

Standard facts, each with a one-line proof:
- (F1) A linear group over a field is LEF. A finite subset lies in `GL_n(R)`
  for a finitely generated domain `R`, and reduction modulo a maximal ideal
  avoiding finitely many nonzero differences is a homomorphism to a finite
  group that is injective on that subset.
- (F2) LEF is closed under subgroups, finite direct products, and increasing
  unions.
- (F3) If `N` is normal of finite index in `G` and `N` is LEF, then `G` is
  LEF. By Kaloujnine-Krasner, `G <= N wr (G/N) = N^k x| (G/N)`. Given a
  partial embedding `phi : N -> Fin` on a finite set, the map `phi^k` on
  `N^k` commutes exactly with the coordinate permutation. So
  `phi^k x id` is a partial embedding into `Fin^k x| (G/N)`.

## Step 1. Row-module identities (checked in the artifact, part 1)

- `QS = 0`, `TQ = 0` and `Q^2 = Q`.
- `1 - S^k T^k = Q_k := sum_(i<k) S^i Q T^i`. This telescopes, because
  `S^i Q T^i = S^i T^i - S^(i+1) T^(i+1)`.
- `Q_k S^k = 0`, since `Q T^i S^k = Q S^(k-i) = 0` for `i < k`.

On the right module `QJ = span{Q T^b}`:
- right `T` is the shift `Q T^b -> Q T^(b+1)`;
- right `S` is `Q T^b -> Q T^(b-1)`, with `Q -> 0`.

So right `S` is locally nilpotent there. Consequently:
- `R_d = span{Q T^b : b <= d}` is stable under right `F[S]`;
- `I_{<=d} = V R_d`, with `V = JQ = span{S^a Q}`, is a left ideal of `J`
  stable under right `F[S]`;
- `I = union of the I_{<=d}`, since `I = J Q J = span{S^a Q T^b}`;
- the map `V (x)_F R_d -> I_{<=d}`, `x (x) r -> x r`, is an isomorphism. It is
  onto because `S^a Q . Q T^b = S^a Q T^b`. It is injective because these
  elements have distinct leading monomials `S^(a+1) T^(b+1)`.

**Kernel of right `S^k` on `J`.**
- If `r S^k = 0`, then `r = r(1 - S^k T^k) = r Q_k`.
- Conversely, `r Q_k S^k = 0`.
- So the kernel is `J Q_k = I_{<k}`. The artifact confirms its dimension on
  a `9 x 9` monomial box for `k <= 4`.

## Step 2. Statement (A): dihedral splitting and index two

**The generators and c.**
- `r_a^2 = x_34(2) = 1` and `r_b^2 = x_43(2S) = 1`.
- On the right Levi block, `c = r_a r_b = [[1,1],[0,1]] [[1,0],[S,1]] = [[1+S, 1], [S, 1]]`.
  Its determinant is `(1+S) + S = 1` and its trace is `S`.

**c has infinite order.**
- Suppose `c^n = 1`. Every eigenvalue `lambda` of `c`, in an algebraic
  closure of `F(S)`, is a root of unity, so it is algebraic over `F`.
- Then `S = lambda + lambda^-1` is algebraic over `F`. But `F[S]` is a
  polynomial ring, since the `S^i` are basis elements of `J`.
- Hence `D = <r_a, r_b>` is `C_2 * C_2`, the infinite dihedral group, and
  `<c>` is its index-two subgroup, isomorphic to `Z`.

**The splitting.**
- The left and right Levi blocks commute, so `H_mix = N x| D` with
  `N = M_2(J) x| L`.
- `H' = N x| <c> = M_2(J) x| (L x <c>)` has index 2.

**The MF radical.**
- `Rad_MF(H')` contains `Rad_MF(H_mix) ∩ H'`, by restriction of models.
- Conversely, let `sigma : H' -> U(Qc)` with `Qc = prod M_(k_n) / sum M_(k_n)`.
  Then `Ind sigma : H_mix -> U(M_2(Qc))`, and `M_2(Qc)` is again of the
  form `prod M_(2 k_n) / sum M_(2 k_n)`.
- On `H'`, `Ind sigma` is `diag(sigma, sigma o Ad r_a)`.
- So `h` outside `Rad_MF(H')` implies `h` outside `Rad_MF(H_mix)`, and
  `ker(Ind sigma) = ker sigma ∩ r_a (ker sigma) r_a^-1`.
- Faithful `sigma` gives faithful `Ind sigma`, and restriction of a faithful
  model to `H'` is faithful.

Both equivalences in (A) follow.

## Step 3. Statement (B): the finitary half is LEF

Put `B = EL_2(F[S])`.

**Invariance.**
- `M_2(I_{<=d})` is stable under `X -> g X` for `g` in `L`, because
  `I_{<=d}` is a left ideal.
- It is stable under `X -> X b` for `b` in `B`, because entries of `b` lie
  in `F[S]` and Step 1 applies.
- So `G_d = M_2(I_{<=d}) x| (L x B)` is a subgroup, and `K` is the
  increasing union of the `G_d`.
- `h = (1, Q E_11, 1)` lies in `G_0`, since `Q = Q . Q` is in `I_{<=0}`.

**Tensor form.** By Step 1, `M_2(I_{<=d})` is isomorphic to
`V^2 (x) R_d^2` via `v (x) r -> v r` (column times row), with:
- `g (v r) = (g v) r`;
- `(v r) b = v (r b)`.

Let `rho_d : B -> GL(R_d^2)` be the right action. `R_d^2` is a
`2(d+1)`-dimensional space over `F`, so `K_d = rho_d(B)` is finite. Fix a
basis of `R_d^2`, with `m = 2(d+1)`.

**The embedding.** The map

```text
G_d -> [ (V^2)^m x| (L x K_d) ] x B,    (X, g, b) -> ((X, g, rho_d(b)), b)
```

is an injective homomorphism.
- It is a homomorphism because `b` acts on `M_2(I_{<=d})` only through
  `rho_d(b)`.
- It is injective because of the second coordinate and the first
  component.

**LEF.**
- `N_d = (V^2)^m x| L` is normal of index `|K_d|` in the bracket.
- `N_d <= (V^2 x| L)^m`, via `(v_1, ..., v_m, g) -> ((v_1, g), ..., (v_m, g))`.
- `V^2 x| L <= G_1`, since `V^2 = (JQ)^2` is an `L`-stable subgroup of `J^2`.
- So `N_d` is LEF by (I1) and (F2), the bracket is LEF by (F3), and `B` is
  linear, so LEF by (F1).
- Hence `G_d` is LEF by (F2), and `K` is LEF as their union.

## Step 4. Statement (C): the symbol half is LEF

- Let `Lbar` and `Bbar` be the images of `L` and `B` in `SL_2(A)`. Then
  `M_2(A) x| (Lbar x Bbar)` is the block-triangular subgroup
  `[[l, X], [0, b]]` of `GL_4(A)`.
- `A` is a domain, so this subgroup is linear over `Frac A` and is LEF by (F1).
- The map `Gbar -> [M_2(A) x| (Lbar x Bbar)] x L x B` is an injective
  homomorphism. Its first coordinate is reduction, and the second and third
  are the projections to the Levi factors.
- By (I2), (F1) and (F2), `Gbar` is LEF.
- The head maps to `x_13(0) = 1` in `Gbar`.

## Step 5. Statement (D): H_mix and P^S are not LEF

- Over `F_2`, the certificate of (I3) is `u = x_13(1)`, `g = diag(wK, 1)`,
  `e = x_12(1)`, `r1 = r_a` and `r2 = r_b r_a`. It lies in `H_mix`, and so
  does `h = [e, g^-1 u g]^-1`.
- Suppose `H_mix` were LEF. Take a partial embedding `phi` into a finite
  group on a finite ball that contains all subwords of the relators P1-P3
  and of `[e, g^-1 u g]`. Then `phi` defines a homomorphism `Gamma_pig -> Fin`.
- Its group `A` is finite, so Theorem (a) of (I3) gives
  `phi([e, g^-1 u g]) = 1`. That contradicts the injectivity of `phi` on the
  ball, since `h != 1`.
- `P^S` contains `H_mix`, so it is not LEF by (F2).

The relation (P2) uses `u = x_13(1)`, whose row `(1, 0)` is not finitary. By
Step 6, the `D`-span of `(1, 0)` in `J^2` is infinite-dimensional and meets
every nonzero finite-dimensional `c`-stable subspace only inside `I^2`. That
row is where the extension class enters the witness.

## Step 6. Statement (E): window rigidity

Let `M` be a right `J`-module. `M^2` carries a right action of
`M_2(F[S])`, since `F[S]` is commutative.

**The kernel lies in `M[delta]`.**
- Let `W` be finite-dimensional with `W c <= W`, and let `p != 0` be the
  minimal polynomial of right `c` on `W`. Then `W p(c) = 0`.
- Over the commutative ring `F[S]`, `p(c) adj(p(c)) = delta . 1`, with
  `delta = det p(c)`. So `w delta = 0` for every `w` in `W`, and
  `W <= (M[delta])^2`.

**`delta` is nonzero.**
- `delta = p(lambda) p(lambda^-1)`, where `lambda^(+-1)` are the eigenvalues
  of `c` over an algebraic closure of `F(S)`.
- `lambda` is transcendental over `F`, by Step 2, so `delta != 0`.
- The artifact checks `det p(c) != 0` for every `p != 0` with `deg p <= 12`.

**For `M = A`.** `delta(z) != 0`, and `A` is a domain, so `A[delta] = 0` and
`W = 0`.

**For `M = J`.** Write `delta = S^k eps(S)`, with `eps(0) = 1`.
- Right `eps(S)` is injective on `J`. Suppose `r eps(S) = 0`. Its symbol
  gives `rbar eps(z) = 0`, so `r` lies in `I`, hence in some `I_{<=d}`.
- On `I_{<=d} = V (x) R_d`, right `S` is `1 (x) (nilpotent)`. So `eps(S)` is
  unipotent there, and `r = 0`.
- Hence `r delta = (r S^k) eps(S) = 0` forces `r S^k = 0`, so `r` lies in
  `I_{<k}` by Step 1.

**The union is `I^2`.**
- Each `w` in `I^2` is a finite sum of `v (x) r` inside some
  `(V (x) R_d)^2`.
- The span of the corresponding `v (x) R_d^2` is finite-dimensional and
  stable under `EL_2(F[S])`.
- So the union of the finite-dimensional stable subspaces is exactly `I^2`,
  whether "stable" means under `<c>`, under `D`, or under `EL_2(F[S])`.

## Step 7. The class kill

Suppose an argument derives `pi(h) = 1` for every MF model `pi` of some
`G <= EL_5(J)`, using only:
- relations holding in `K`, together with asymptotic multiplicativity of
  `pi`; or
- passage to the symbol quotient.

The first kind fails because `K` is LEF by Step 3. Its partial embeddings,
composed with regular representations of the finite targets along growing
balls, give an MF
model of `K`, exact modulo `sum M_k`, in which `||pi(h) - 1|| = 2`.
The second kind proves nothing about `h`, which is trivial in `Gbar`.

The pigeonhole of (I3) is an argument of neither kind. Its relation (P2)
involves the non-finitary `u`, which is what makes `H_mix` non-LEF even
though `K` and `Gbar` are LEF.

## Step 8. Numerical confirmation

`python3 experiments/h-mix-dihedral-window-2026-09-17/check_dihedral_window.py`
exits 0. It checks exactly, in the normal form of `J`:
- `TS = 1`, `QS = 0`, `TQ = 0`;
- the telescoping of `Q_k` and `Q_k S^k = 0`, for `k <= 6`;
- `dim ker(right S^k) = 8k` on the `9 x 9` monomial box, for `k <= 4`;
- the form of `c`, its trace and determinant, and `c^n != 1` for `n <= 300`;
- `det p(c) != 0` for all `p != 0` with `deg p <= 12`;
- stability of `I_{<=d}` under right `S`, for `d <= 3`, together with the
  failure of stability under right `T`.

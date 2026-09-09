---
rg: 2
id: integral-jacobson-mf-radical-is-all-or-nothing-proof
kind: route
title: Extract a transvection from any kernel element by two commutators, conjugate it onto the central defect element, and let the trivial-or-infinite-order principle finish
target: integral-jacobson-mf-radical-is-all-or-nothing
requires:
  - integral-jacobson-symbol-kernel-is-finitary-general-linear
  - integral-jacobson-sign-quotient-is-residually-finite
  - central-defect-element-mf-image-is-trivial-or-infinite
artifacts:
  - research/artifacts/jacobson-exact-torsion-radical-and-integral-dichotomy-2026-09-09.md
  - non_mf_groups_exist.tex
---

## Why sufficient

**The integral central defect element.**  The manuscript's proof of
`prop:torsion-defect-ring` is a list of ring identities in
`Z<s,t | ts = 1>` (rechecked exactly): in `EL_4(J)` with
`L = EL_3(J)` on the first three coordinates, which is Kazhdan
(Ershov--Jaikin-Zapirain, Theorem 1.1, for the finitely generated ring
`J`), the compressor `v = u D(w_14 w_25)`, the centralizing `c =
D(1 + f_02)`, `y = e_42(f_10)`, `l = e_21(1)` give `v L v^-1 <= L`,
`c in C(L)`, `[y, [v c v^-1, l]] = z^-1` with `z = D(1 + f_12)`, and `z`
central in `B = <L, v, c, y>`.  So `zeta = z` satisfies `(TI1)` in
`Delta = B`, and over `J` it has infinite order.  Write `T_(pq)(r)` for
the finitary transvection adding `r` times basis vector `q` to basis
vector `p` on the internal basis `{1,..,4} x N_0`; `zeta = T_((4,1),(4,2))(1)`.

**Extraction.**  Let `phi : G_n -> M` be MF-valued and suppose
`1 != g in ker(phi) cap N_n`.  Choose a finite block `F` of the internal
basis outside which `g` is the identity (so `g^-1` also), an index
`a in F` with `v = (g - I) e_a != 0`, and `b not in F`.  Then
`e_b^T g^-1 = e_b^T`, so `g E_(ab) g^-1 = (g e_a) e_b^T = E_(ab) + v e_b^T`
and

```text
[g, T_(ab)(1)] = (I + E_(ab) + v e_b^T)(I - E_(ab)) = I + v e_b^T in ker(phi),
```

using `E_(ab)^2 = 0` and `e_b^T E_(ab) = 0`.  Choose `i in F` with
`v_i = r != 0` and `c not in F cup {b}`.  With `X = E_(ci)`, `Y = v e_b^T`:
`XY = r E_(cb)`, `YX = 0`, `X^2 = Y^2 = 0`, so

```text
[T_(ci)(1), I + v e_b^T] = I + XY = T_(cb)(r) in ker(phi).
```

**Transport to `zeta`.**  A finitary signed permutation matrix `P` with
`P e_b = +-e_((4,2))`, `P e_c = +-e_((4,1))`, and determinant one (fix
the determinant on an unused basis vector) lies in `N_n <= G_n`, and
`P T_(cb)(r) P^-1 = zeta^(+-r)`.  So `phi(zeta)^r = 1`: `phi(zeta)` has
finite order, and the third prerequisite gives `phi(zeta) = 1`.  The
signed-permutation conjugates of `zeta` are all `T_(pq)(1)`, which
generate `N_n`; hence `phi(N_n) = 1`.  This is `(AN1)`.

**The alternative.**  If some MF-valued `phi` has `ker(phi) cap N_n = 1`,
then `phi x q : G_n -> M x T_n`, with `q` the quotient by `N_n`, has
kernel `ker(phi) cap N_n = 1`; `T_n` is residually finite hence MF by
the second prerequisite, products of MF groups are MF (block sums), and
subgroups of MF groups are MF, so `G_n` is MF.  Otherwise every
MF-valued homomorphism kills `N_n`, so `N_n <= Rad_MF(G_n)`, and the
second prerequisite gives equality.  This is `(AN2)`; an MF radical
strictly between `1` and `N_n` would be the kernel of a homomorphism
violating `(AN1)`.

---
rg: 2
id: orthogonal-kazhdan-powers-have-quadratic-depth-loss
kind: claim
title: Orthogonal Kazhdan projection pushes the flat-tower enemy to inverse-square depth, and its depth loss is sharp
distinct_from:
  homogeneous-quotient-near-genuine-microstates-are-deep: that uses a linear total-variation estimate for an intertwiner close to a unitary; this uses that the Kazhdan average is the orthogonal Hilbert--Schmidt projection and controls overlap deficit by the SQUARE of that distance.
  lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible: that gives an inverse-defect lower bound on the surviving p-depth; this strengthens the same Atkin--Lehner count to inverse-square depth.
  weyl-kernel-joins-descend-two-levels-without-mass-contraction: that squares the loss for one fixed-depth Schur support and then iterates only a fixed number of times; this proves the exact all-depth power inequality and identifies its sharp obstruction.
  fixed-shift-invariance-does-not-force-flat-profile: that fences scalar profile rigidity; this fences the stronger global orthogonal-projection route even before any scalar profile is chosen.
---

Let `sigma_1,sigma_2` be finite-image unitary representations on `C^d`,
let `H` be unitary, and let `T` be the orthogonal projection of `H` in
normalized Hilbert--Schmidt space onto

```text
I(sigma_1,sigma_2)={X : X sigma_1(g)=sigma_2(g)X for every g}.           (QK1)
```

Write `w_1,w_2` for the normalized-dimensional isotypic weight measures and

```text
Delta(w_1,w_2)=1-sum_pi min(w_1(pi),w_2(pi))
                  =(1/2) sum_pi |w_1(pi)-w_2(pi)|.                      (QK2)
```

Then, with `delta=||H-T||_2`,

```text
Delta(w_1,w_2) <= delta^2.                                               (QK3)
```

More generally, whenever `T^k` is an exact intertwiner between two
representations `alpha_k,beta_k` (as in the congruence-depth applications),

```text
Delta(w(alpha_k),w(beta_k))
 <= 1-||T^k||_2^2
 <= k(1-||T||_2^2)
 = k delta^2.                                                            (QK4)
```

Consequently the two arithmetic tower estimates sharpen as follows.

1. In `lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible`, let
   `delta_0` be the distance of `H` from the exact `C_0`-intertwiner space.
   The Atkin--Lehner missing-mass count gives

   ```text
   c_p(1-nu_0) <= D delta_0^2 <= D epsilon^2/kappa_0^2.                  (QK5)
   ```

   Here the last inequality uses the Kazhdan-constant convention of
   `lambda-exact-p-divisible-ultra-deep-proof`; with a different normalization
   only the absolute constant changes.

2. In `homogeneous-quotient-near-genuine-microstates-are-deep`, the same
   proof, including its fixed signed-permutation normal-closure step, gives
   an absolute `C_square` such that

   ```text
   F(p^(a-k)m') >= 1-C_square k epsilon^2/kappa_0^2,                     (QK6)

   a >= j + (kappa_0^2/(C_square epsilon^2))
       . (1/(8|Y_(j+1)|)-C_2|Y_(j+1)|epsilon/kappa).                    (QK7)
   ```

Thus a positive-mass `p`-divisible exact-face sector, and likewise a
near-genuine homogeneous-quotient microstate, has depth
`Omega(epsilon^(-2))`, not merely `Omega(epsilon^(-1))`.  Its top `k`
congruence levels have average weight `O(epsilon^2)`.

This still does **not** exclude arbitrarily deep flat towers.  The factor
`k` in `(QK4)` is sharp for orthogonal projection onto an intertwiner space.
For every `D`, on `C^D` let `H` be the cyclic shift and let `T` be the
truncated shift obtained by deleting its wrap edge.  Then `T` is the
orthogonal projection of `H` onto the intertwiner space of two
finite-cyclic-group representations, while

```text
||H-T||_2^2=1/D,        1-||T^k||_2^2=k/D  (0<=k<=D),        T^D=0.      (QK8)
```

Therefore a global projection or square-function argument using only this
one Kazhdan intertwiner cannot replace `D epsilon^2` by a depth-independent
error.  Excluding the residual depth-`Theta(epsilon^(-2))` (or deeper)
enemy requires an additional arithmetic assertion which makes different
depth exits overlap destructively or charges them through one fixed global
building/branch projection.  Orthogonality alone gives the sharp square
function `(QK4)` and no contradiction.

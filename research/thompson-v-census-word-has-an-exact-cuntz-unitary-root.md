---
rg: 2
id: thompson-v-census-word-has-an-exact-cuntz-unitary-root
kind: claim
title: The census word c t a t a t^-1 over Thompson's V has an explicit root in U(O_2), a real orthogonal involution lifted along a leaf Cuntz family, although it has none in any Higman--Thompson group or in Homeo of the Cantor set
distinct_from:
  higman-thompson-roots-miss-a-kl-word-over-thompson-v: that proves no root of w0 = c t a t a t^-1 exists in any V_{n,1} (or Sym(X_n)) after any homomorphism of V; this exhibits a root of the same w0 in the first non-spatial ambient, U(O_2) with the canonical copy of V, so the internal-root kill there is exactly the spatial one.
  cantor-homeomorphisms-miss-a-unimodular-root: that is the orbit-type obstruction for S_3-actions with orbits of size 1 or 3 inside Sym(Omega); this shows the obstruction does not survive linearization, because the root is a reflection of the standard S_3-plane that is not a permutation.
  cone-diagonal-roots-miss-a-kl-word-over-thompson-v: that proves Kervaire--Laudenbach for w0 abstractly and kills cone-diagonal internal roots; this gives a concrete root inside a unitary group that contains V itself, with entries in the cubic field Q(cos 2 pi/9).
  kl-failure-localizes-to-the-coefficient-subgroup: that says a failure is already a failure over the coefficient subgroup, here the finite F = S_3, so KL for w0 was never in doubt; this is about where a root can live, not whether one exists.
artifacts:
  - experiments/kl-cuntz-linearization-2026-09-17/exact_root_check.py
  - experiments/kl-cuntz-linearization-2026-09-17/out_exact_root_check.txt
  - experiments/kl-cuntz-linearization-2026-09-17/ctatat_cuntz_root.py
  - experiments/kl-cuntz-linearization-2026-09-17/out_ctatat_cuntz_root.json
  - experiments/kl-cuntz-linearization-2026-09-17/gl3_fp_roots.py
  - experiments/kl-cuntz-linearization-2026-09-17/out_gl3_fp_roots.txt
---

**ESTABLISHED** by `thompson-v-census-word-cuntz-root-proof`.

**Setting.** As in `higman-thompson-roots-miss-a-kl-word-over-thompson-v`:
- `V` acts on `C = {0,1}^N`;
- `a = (00 01)` and `c = (1 00)`, so `F = <a, c> ≅ S_3`;
- `w0 = c t a t a t^(-1)`, census form `ctataT`.

Let `O_2 = C*(s_0, s_1)` and `s_u = s_(u_1) ... s_(u_k)`. The **canonical copy** of `V` in `U(O_2)` sends the element that maps
the cone `u_i` onto the cone `v_i` (for complete prefix codes `(u_i)`, `(v_i)`) to `U_g = sum_i s_(v_i) s_(u_i)^*`.

## Statement

1. **The root.** Put the leaves in the order `l = (00, 01, 1)` and define `X in O(3)` by

   ```text
   X_ij = 1/3 + (2/3) cos(2 pi/9 + 2 pi (2 - i - j)/3),     i, j in {0, 1, 2}.
   ```

   Then `T = sum_(i,j) X_ij s_(l_i) s_(l_j)^*` is a self-adjoint unitary in `O_2` with

   ```text
   U_c T U_a T U_a T^(-1) = 1     in O_2.
   ```

   `X`, `P_a` and `P_c` are real symmetric. So transposing shows `X` is also a root of the reversed word, and the root
   does not depend on whether `V` composes on the left or on the right.
   `T` lies in the Leavitt algebra `L_K(1,2) ⊂ O_2` over the real cubic field `K = Q(cos 2 pi/9)`. So `w0` also has a
   root inside the unit group `L_K(1,2)^x`, which contains the canonical copy of `V`.
2. **Every unital C\*-ambient.** More generally, let `B` be a unital C\*-algebra and `rho : V -> U(B)` any homomorphism.
   Then for every finite subgroup `F' <= V`, every `w in F' * <t>` with nonzero `t`-exponent sum has a root
   `T in U(C*(rho(F')))`.
   This covers `w0`, the equation of `cantor-homeomorphisms-miss-a-unimodular-root`, and every other equation whose
   coefficients generate a finite subgroup of `V`.
3. **No small modular root.** With the same permutation constants, `GL_3(F_p)` contains no root of `w0` for `p = 2, 3, 5`
   (exhaustive count, `gl3_fp_roots.py`). This says nothing about larger sizes `3k`.

## What it shows

**The dictionary.** The cone isometries `s_u` turn V's action on the Cantor set into unitaries of `O_2`. Under this
dictionary:
- a permutation of the leaves of a complete prefix code `l` becomes `Phi_l(P)`, where `Phi_l : M_n -> O_2`,
  `Phi_l(M) = sum M_ij s_(l_i) s_(l_j)^*`, is a unital `*`-homomorphism;
- a candidate root may be any `Phi_l(X)` with `X` unitary, not only a permutation matrix.

**The orbit-type invariant does not survive.** Every root in `Sym(Omega)`, `Homeo(C)` or `V_{n,1}` fails because the
`F`-orbits have size `1` or `3`. In the linearization the root is `1 ⊕ r`, where `r` is a reflection of the standard
`S_3`-plane whose axis sits at angle `pi/9` from a transposition axis. Such a reflection is never a permutation.

**The spatial class kill is sharp.** `higman-thompson-roots-miss-a-kl-word-over-thompson-v` left open one survivor:
internal roots in ambients whose homomorphisms from `V` are not spatial. The first such ambient, `U(O_2)`, already has an
internal root for `w0`.

**What it does not do.** It does not reach the frontier census words, whose coefficients generate all of `V`. For those,
the open question is `thompson-v-equations-have-approximate-cuntz-unitary-roots`.

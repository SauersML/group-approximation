---
rg: 2
id: binary-jacobson-rank-two-elementary-group-is-lef
kind: claim
title: Rank-two Jacobson elementary groups and their SL_2 symbol preimages are LEF, hence MF, over Z and every finite cyclic ring
distinct_from:
  jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group: that pairs E with an untwisted mirror copy in a fibre product for n >= 3 and leaves E itself as a quotient by a simple kernel; this folds one copy onto itself through the inverse-transpose automorphism, which exists only because inverse-transpose is inner on SL_2, and proves the rank-two group itself LEF.
  binary-jacobson-mark-dichotomy-holds-from-rank-two: that proves Rad_MF(EL_n(J)) is 1 or L_n with no intermediate value for n >= 2 and decides neither side; this decides the side at n = 2, namely Rad_MF = 1.
  jacobson-one-sided-symbol-preimages-are-lef: that proves the preimages of the one-sided symbol groups SL_n(F_2[z]) and SL_n(F_2[z^(-1)]) LEF; this handles the full two-sided Laurent symbol group at rank two, where both boundary conventions occur.
  cohn-elementary-group-is-not-lef: that proves EL_n(J) is not LEF for n >= 4; this proves EL_2(J) is LEF, and the invariant below explains why the method stops at n = 3.
  binary-jacobson-finitary-whitehead-shift-is-marked-lef: that is a marked LEF statement for a Whitehead-shift subgroup; this is LEF for the whole symbol preimage of SL_2.
  rank-two-jacobson-groups-have-no-infinite-kazhdan-subgroup: that excludes Kazhdan subgroups in rank two; this gives the stronger positive approximation statement, finite exact local models.
  binary-jacobson-el3-is-sofic: that asks soficity at rank three, where no form-preserving mirror exists; this settles rank two.
  jacobson-literal-column-normalizer-is-lef: that proves one explicit subgroup <GL_2(F_2), [[Q,S],[T,0]]> semidirect (J,+)^2 LEF by even cycles; the GL_2 part of that group lies in the SL_2 symbol preimage treated here.
  jacobson-image-of-five-transvection-group-is-sofic: that asks soficity of one subgroup of GL_2(F_3<S,T|TS=1>); this proves LEF for a group containing it (route five-transvection-image-sofic-via-rank-two-lef).
  integral-jacobson-elementary-group-is-not-mf: that asserts EL_n(J_Z) is not MF for every n >= 2, or at least for large n; this proves EL_2(J_Z) is MF, so the rank-two reading of that claim is false and only the large-rank version survives.
artifacts:
  - experiments/jacobson-rank-two-2026-09-17/mirror_lef.py
  - experiments/jacobson-rank-two-2026-09-17/five_transvection_f3_fold.py
---

**ESTABLISHED.**  Let `C = Z` or `C = Z/mZ` (`m >= 2`), `J_C = C<S,T | TS = 1>`,
`Q = 1 - ST`, `A_C = C[z,z^(-1)]` and `π : M_n(J_C) -> M_n(A_C)` the symbol map
`S -> z`, `T -> z^(-1)`. Put

```text
T_C = { g in GL_2(J_C) : det π(g) = 1 }  =  π^(-1) SL_2(A_C).            (R2)
```

1. **`T_C` is LEF.** For `C` finite the models are exact partial homomorphisms
   into `GL_(2N)(C)`; for `C = Z` compose with reduction modulo a large `m`.
2. **Hence** `EL_2(J_C) <= T_C` is LEF, so it is sofic, hyperlinear and operator MF
   (`lef-implies-operator-mf`). For `C = F_2`, `Rad_MF(EL_2(J)) = 1`: the first branch
   of `(JR3)` in `binary-jacobson-mark-dichotomy-holds-from-rank-two` holds at `n = 2`.
   The head `x_12(Q)` goes to `I + E_12 (x) (E_(0,0) + E_(N-1,N-1))`, a rank-two
   perturbation of the identity. It is not killed.
3. **Constant-form generalization.** Fix any `n >= 1` and any `c in GL_n(C)`. Put
   `O_c(A_C) = { a in GL_n(A_C) : a^T c a = c }`. Then `π^(-1) O_c(A_C) <= GL_n(J_C)`
   is LEF. Item 1 is the case `n = 2`, `c = [[0,1],[-1,0]]`, where
   `a^T c a = det(a) c`.

**Mechanism: the twisted mirror fold.** `φ(g) = c^(-1) (g^T)^(-1) c` is an
automorphism of `GL_n(J_C)`. Here `g^T` is the operator transpose, meaning block
transpose with `S <-> T` on entries. Its symbol is entrywise `z -> z^(-1)` exactly
on `π^(-1) O_c`. The window model on `C^([0,N) x {1..n})` is

```text
θ_N(g)[i,j] = g[i,j]                 if i + j <= N - 1,
θ_N(g)[i,j] = φ(g)[N-1-i, N-1-j]     if i + j >= N.                     (FOLD)
```

It is exactly multiplicative on any finite set once `N >= 8r + 2`, where `r`
bounds propagation and boundary support. The full proof is in
`binary-jacobson-rank-two-lef-proof`. The artifact checks it by computer on
200 random words over 26 generators, with `N = 64`. It also checks the negative
control: the untwisted fold, `φ = id`, which is the "boundary compression" of
the five-transvection attempts, fails multiplicativity on 65 of the 200 words.

**Invariant and the class it kills.** Let `H <= GL_n(J_C)`, with `C` finite, be
a subgroup whose symbol group preserves a constant nondegenerate bilinear form,
`π(H) <= O_c(A_C)`. Then `H` is LEF and retains every nonidentity element,
heads included. So no head-collapse argument can conclude using only relations
that hold in such an `H`. This covers every relation of `EL_2(J)`, of `T_C`,
and of the one-boundary pieces that previous attempts compressed. A
head-collapse proof must use a configuration whose symbol group preserves no
constant form.

For `n >= 3` the constant subgroup `SL_n(C) <= EL_n(A_C)` already has this
property, because the natural module is not self-dual. This is exactly where
the rank-three path-permutation criterion died ("the constants detect the
orientation of the turn at index 0"). It is consistent with
`cohn-elementary-group-is-not-lef` at `n >= 4`. Rank three stays open.

DERIVATION
binary-jacobson-rank-two-lef-proof

---
rg: 2
id: binary-jacobson-el2-is-lef
kind: claim
title: The rank-two binary Jacobson elementary group EL_2(J) is LEF, hence MF with trivial MF radical, because transpose-inverse is inner in SL_2 and lifts the symbol inversion to the mirror end
distinct_from:
  binary-jacobson-mark-dichotomy-holds-from-rank-two: that proves Rad_MF(EL_n(J)) is 1 or L_n for every n >= 2 and decides neither side; this decides n = 2, with Rad_MF(EL_2(J)) = 1.
  jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group: that writes EL_n(J), n >= 3, as the LEF mirror fibre product modulo L_-; this shows that at n = 2 the quotient map has a homomorphic section g -> (g, theta(g)), so the group itself is LEF.
  jacobson-one-sided-symbol-preimages-are-lef: that proves the two one-sided halves H_+ and H_- of EL_3(J) are LEF and says head loss needs mixed S/T relations; here the whole rank-two group, with every mixed S/T relation, is LEF, so head loss needs three matrix indices.
  cohn-elementary-group-is-not-lef: that proves EL_n(J) is not LEF for n >= 4 using Steinberg relations in three indices; this shows rank two is LEF, so the threshold for non-LEF lies at rank three or four.
  rank-two-jacobson-groups-have-no-infinite-kazhdan-subgroup: that excludes Kazhdan subgroups of GL_2(J_k) and states it does not say the rank-two groups are MF; this proves that they are LEF and MF.
artifacts:
  - experiments/rank-two-jacobson-lef-2026-09-17/check_el2_lef.py
---

**ESTABLISHED (unreviewed)** by route `binary-jacobson-el2-lef-proof`.

**Setting.**
- `F` is a finite field, `J = F<S,T | TS = 1>`, `Q = 1 - ST`, `A = F[z, z^(-1)]`.
- `sigma : J -> A` is the symbol map `S -> z`, `T -> z^(-1)`.
- `G = EL_2(J)`, and `L_2 = ker(sigma) ∩ G` is the finitary kernel.
- The head is `h = e_12(Q)`. In `EL_n(J)` with `n >= 3` it is conjugate by a
  constant Weyl element to `x_13(Q)`.

**Theorem.**
1. **Mirror lift.** Let `tau` be the anti-automorphism of `J` with `S <-> T`,
   and let `K = [[0,1],[-1,0]]`, which lies in `EL_2(F)`. Then
   `psi(g) = K tau(g)^(-t) K^(-1)` is an automorphism of `G` with
   `psi(e_ij(a)) = e_ij(tau(a))` and `sigma(psi(g)) = iota(sigma(g))`, where
   `iota(z) = z^(-1)`.
2. **LEF.** For every finite `B ⊂ G`, some `M` gives a map
   `Phi_M : B -> GL_(2(M+1))(F)` that is injective and multiplicative on `B`.
   Columns near `0` come from the Toeplitz action of `g`. Columns near `M`
   come from the mirror action of `psi(g)`. So `G` is LEF.
3. **Consequences.**
   - `G` is sofic and hyperlinear.
   - `G` is MF: it embeds in the norm corona `prod M_n / (+) M_n` through the
     regular representations of the finite groups `GL_(2(M+1))(F)`.
   - `Rad_MF(EL_2(J)) = 1`, so in the dichotomy (JR3) the case `n = 2` is
     "operator-MF".
   - The head `e_12(Q)` survives in an injective asymptotic representation.

**Why rank two only.** Item 1 uses the identity `K m^(-t) K^(-1) = m` for
`m in SL_2(A)`.
- For `n >= 3`, transpose-inverse is outer on `SL_n(A)`, so the `tau` and
  `beta` twists no longer combine to a symbol-preserving lift.
- This is consistent with `cohn-elementary-group-is-not-lef`, which proves
  `EL_n(J)` is not LEF for `n >= 4`.

**Class killed (obstruction for `property-t-free-jacobson-head-collapse`).**
- **Class.** Any argument that derives the death of the head in norm-corona
  representations from relations and structure *inside one rank-two block*
  `<x_ij(J), x_ji(J)>` of `St_5(J)`. This includes:
  - the Whitehead involution `w = e_12(S) e_21(T) e_12(S) = [[Q,S],[T,0]]`, with
    `w^2 = 1` and the braid identity `w = e_21(T) e_12(S) e_21(T)`;
  - the Toeplitz symbol extension `1 -> L_2 -> G -> SL_2(A) -> 1`, with its
    non-amenable quotient and its cocycle;
  - Fredholm index, direct-finiteness bookkeeping, and every mixed S/T relation
    in two indices.
- **Invariant.** The mirror lift `psi`. It exists exactly because
  transpose-inverse is inner in `SL_2`.
- **Step where every member dies.** Each such argument would kill `e_12(Q)` in
  every asymptotic representation of the LEF group `EL_2(J)`. That is false.
- **What a (T)-free proof must use.** A relation with three distinct indices,
  i.e. a Steinberg commutator `[x_ij(a), x_jk(b)] = x_ik(ab)`. The finite-image
  argument of `cohn-elementary-group-is-not-lef` uses exactly this, through the
  chain `x_13 -> x_12 -> x_32`.
- **What it sharpens.** This strengthens "mixed relations are required" in
  `jacobson-one-sided-symbol-preimages-are-lef` to "mixed relations in three
  indices are required". It is the first calibration with non-amenable symbol
  image, going beyond the amenable calibration `SL_fin ⋊ <u>`.

**Numerical check.** `experiments/rank-two-jacobson-lef-2026-09-17/check_el2_lef.py`
- **Setup.** `M = 90`, 400 random words of length up to 7, 24 coefficient types.
- **Main check.** For each word, the product of the glued generator matrices
  equals the glued matrix computed from the exact group element and its
  inverse. There were 0 failures.
- **Injectivity.** The words gave 344 distinct group elements and 344 distinct
  images.
- **Head and involution.** The head is nontrivial, and `Phi(w)^2 = 1`.
- **Controls.** Gluing without the `tau` twist, or with hard truncation, fails
  the same test 141 and 95 times.

DERIVATION
binary-jacobson-el2-lef-proof

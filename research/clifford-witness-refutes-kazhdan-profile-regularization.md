---
rg: 2
id: clifford-witness-refutes-kazhdan-profile-regularization
kind: claim
title: The sofic Clifford witness admits no sofic representation satisfying any sufficient condition for Kazhdan centralizer normalization, so every profile-regularization route to killing compression defects is false, and its chain-envelope form is summit-strength
distinct_from:
  sofic-normalization-fails-for-finite-index-kazhdan-pairs: that is the calibration (F1)-(F4) of the pair Gamma' <= Gamma inside W; this turns (F3) into a no-go for every regularization statement "sofic G with Kazhdan L has a representation with property P", for every P that forces normalization, and computes the strength of the chain-envelope variant.
  ckn-forces-nonsofic-incompressible-affine-coset-wreath: that proves CKN implies nonsoficity of W_aff,p; this proves that every chain-envelope regularization statement, together with a normalization theorem for its property, implies CKN, so it inherits that strength.
  bounded-period-compressors-carry-no-sofic-defect: that says any defect needs a wild compressor, in an unspecified witness; this exhibits a sofic group (W, Gamma, t) whose compressor is wild in every sofic representation, conditional only on the same (KT*) input, so the survivor shape is realized.
  finite-scale-compressors-preserve-kazhdan-fixed-algebras: that is a fixed-algebra preservation theorem under a scale hypothesis; this is a statement about which sofic representations exist, and concerns centralizer normalization, not fixed algebras.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that is the open construction problem; this closes the regularization lanes aimed at killing it and leaves only a kernel-specific form.
artifacts:
  - research/clifford-witness-refutes-kazhdan-profile-regularization-proof.md
  - research/sofic-normalization-fails-for-finite-index-kazhdan-pairs.md
  - research/sofic-normalization-fails-for-finite-index-kazhdan-pairs-proof.md
  - research/ckn-forces-nonsofic-incompressible-affine-coset-wreath.md
  - research/bounded-period-compressors-carry-no-sofic-defect.md
  - research/sofic-non-mf-witness.md
---

**ESTABLISHED** (proof: `clifford-witness-refutes-kazhdan-profile-regularization-proof`).
The items below are either unconditional, or implications whose hypotheses are named.

## Setting

- `S_U = prod_U Sym(Y_n)` is the universal sofic group, for any nonprincipal ultrafilter `U`.
- A **sofic representation** of a countable group `G` is a homomorphism `sigma : G -> S_U` with
  `tr sigma(g) = 0` for `g != 1`. Such a `sigma` is injective.
- `Comp_G(L) = {u : u L u^-1 <= L}` and `D_G(L)` are as in
  `compression-defect-dies-in-finite-dimensions`.
- A **representation property** `P` is any predicate on triples `(sigma, L, u)`, where `sigma` is a
  sofic representation of `G`, `L <= G` and `u in Comp_G(L)`. Examples:
  - properties of `sigma|_L` alone, such as the finite-scale profile of the session-branch node
    `finite-scale-sofic-profiles-kill-compression-defects`;
  - properties of the compressor, such as the bounded cluster period `BP_p` of
    `bounded-period-compressors-carry-no-sofic-defect`.
- `P` is **normalizing** if the following holds for every sofic `G`, every Kazhdan `L <= G`,
  every `u in Comp_G(L)` and every sofic representation `sigma` of `G` with `P(sigma, L, u)`:
  `sigma(u)` normalizes `C_(S_U)(sigma(L))`.
- `W = Cl(X) ⋊ V`, `Gamma = Z^3 ⋊ SL_3(Z)`, `Gamma' = 2Z^3 ⋊ SL_3(Z)`, the stable letter `t`, the
  root coset `x_0 = Gamma` and `a = (e_1, I)` are as in
  `sofic-normalization-fails-for-finite-index-kazhdan-pairs`. `W` is finitely generated and
  sofic, `Gamma` is Kazhdan, and `t Gamma t^-1 = Gamma'`, so `t in Comp_W(Gamma)`.

## Statement

1. **(R0: a nontrivial defect and an explicit generator.)** `c_(x_0) in C_W(Gamma)`, and
   `[t c_(x_0) t^-1, a] != 1`. So `D_W(Gamma) != 1`.
2. **(R1: normalization fails in every sofic representation.)** Let `sigma` be any sofic
   representation of `W`, for any `U`, and put `C = C_(S_U)(sigma Gamma)`. Then
   `sigma(t) C sigma(t)^-1 = C_(S_U)(sigma Gamma')`, and this strictly contains `C`. So `sigma(t)`
   does not normalize `C`.
3. **(R2: no-go for regularization.)** Let `P` be normalizing. Then `W` has no sofic
   representation `sigma` with `P(sigma, Gamma, t)`. Hence the regularization statement

   ```text
   (Reg_P)  every sofic G containing a Kazhdan L, with a compressor u in Comp_G(L),
            has a sofic representation sigma with P(sigma, L, u)
   ```

   is false. It fails already for a finitely generated `G` in which `L` has a compressor `u`
   with `[L : u L u^-1] = 8` and `<<u L u^-1>>^L = L`.
4. **(R3: the instances.)**
   - (a) If `P` depends only on `sigma|_L` (a *profile* property) and is normalizing, then no
     sofic representation of `W` restricts to a `P`-representation of `Gamma`. The finite-scale
     profile is such a `P`: normalizing is exactly item FSK1 of the session-branch node
     `finite-scale-sofic-profiles-kill-compression-defects`, which is ESTABLISHED there. Given
     FSK1, **its open reduction (PR) is false**, and every sofic representation of `W` is
     multi-scale on `Gamma`. So the survivor shape named in FSK3 (all sofic representations
     are towers) occurs in an actual sofic group. It is not vacuous.
   - (b) Suppose (KT\*) of `ambient-decomposition-kun-thom-normalization` holds. Then item 1 of
     `bounded-period-compressors-carry-no-sofic-defect` says a tame compressor carries no defect
     generator. By (R0), `t` carries one, so `t` is wild in `W`: for every sofic representation
     of `W`, every cluster frame of `Gamma` and every `p`, `BP_p` fails for `t`. The
     wild-compressor survivor shape of that node is therefore realized too. Without (KT\*),
     (R1) still shows that every sofic representation of `W` violates the conclusion that
     (KT\*) would draw from `BP_p`.
5. **(R4: the chain-envelope form is summit-strength.)** Let `P` be normalizing, and consider

   ```text
   (Reg_P^env)  if G is sofic, L <= G is Kazhdan, u in Comp_G(L), and union_n u^-n L u^n lies
                in a Kazhdan subgroup of G, then G has a sofic representation sigma with
                P(sigma, L, u).
   ```

   Then `(Reg_P^env)` implies (CKN) of `sofic-normalization-fails-for-finite-index-kazhdan-pairs`.
   Hence, by `ckn-forces-nonsofic-incompressible-affine-coset-wreath`, it implies that the
   affine coset wreath `W_aff,p` is nonsofic. `W` does not refute `(Reg_P^env)`, since
   (F4) says no Kazhdan subgroup of `W` contains the chain of `t`.

## What this kills

- **Class.** Every route to killing (EK1) of `torsion-free-sofic-extrinsic-kazhdan-defect-kernel`
  that has this form: first produce a well-behaved sofic representation (finite-scale, tame,
  bounded period, finite-dimensional fixed algebra, a regularized profile), then apply a
  normalization theorem to it. The hypothesis may be "sofic ambient group plus Kazhdan source",
  even with a finite-index, normally generating compressed pair.
- **Invariant.** The nontrivial Kazhdan compression defect of `W`, carried by the lamp
  `c_(t x_0)`. Injectivity turns it into the non-normalization (R1) in every sofic
  representation.
- **Step where every member dies.** The regularization step. By (R1), `W` has no
  representation of the kind the step promises, whatever normalizing property it names.

## What survives

Only a kernel-specific regularization can still kill (EK1):

```text
(Reg_P^K)  if G = K ⋊_phi Z is sofic, K is Kazhdan and has no nontrivial finite quotient, and
           L <= K is Kazhdan, then G has a sofic representation sigma with P(sigma, L, u)
           for every u in Comp_G(L).
```

With a normalizing `P`, `(Reg_P^K)` gives `D_G(L) = 1` by injectivity, and so kills (EK1). By
(R2) its proof must use that the chain lies in the Kazhdan kernel. By (R4), a proof that uses
only a Kazhdan envelope of the chain also proves that `W_aff,p` is nonsofic. So, unless the
summit is resolved, the proof must use that `K` is normal and Kazhdan in `G` with quotient `Z`,
or that `K` has no finite quotient. The affine counter-wreath fails the second condition.
`(Reg_P^K)` is OPEN.

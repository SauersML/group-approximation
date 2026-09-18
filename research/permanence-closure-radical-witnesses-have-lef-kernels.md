---
rg: 2
id: permanence-closure-radical-witnesses-have-lef-kernels
kind: claim
title: An exact Kazhdan MF-radical witness over Z lies in the sofic permanence closure exactly when its kernel is LEF, and then it refutes EKL1
distinct_from:
  kazhdan-groups-in-sofic-permanence-closure-are-lef: that proves LEF for Kazhdan subgroups of the closure; this applies it to the mapping-torus witnesses of the flagship, splits them by membership in the closure, and computes what each side still needs.
  exact-kazhdan-radical-kernel-cannot-be-lef: that states (EKL1) as an open obstruction; this proves that (EKL1) is exactly the statement that no flagship witness lies in the permanence closure.
  mapping-torus-mf-radical-descends-through-kernel-radical: that splits witnesses into intrinsic (DI) and extrinsic (DX) kernels; this proves that every witness in the closure is extrinsic with Q = K itself LEF, so (DI) witnesses all lie outside it.
  titz-witzel-kernel-not-elementary-sofic: that excludes one kernel from Cornulier's elementary sofic class; this excludes every intrinsically full-radical kernel, finitely presented or not, from the larger permanence closure.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that asks for a sofic kernel saturated by an extrinsic defect; this shows that if its soficity is certified by permanence the kernel is LEF and the construction refutes (EKL1).
  torsion-free-kazhdan-alternating-mother-limit-gate: that studies LEF marked limits of alternating quotients as kernels; this proves that such a kernel lies in the closure and gives the exact extra condition it must meet.
artifacts:
  - research/kazhdan-groups-in-sofic-permanence-closure-are-lef.md
  - research/exact-kazhdan-radical-kernel-cannot-be-lef.md
  - research/mapping-torus-mf-radical-descends-through-kernel-radical.md
---

**ESTABLISHED.** Let `𝒫` be the sofic permanence closure of
`kazhdan-groups-in-sofic-permanence-closure-are-lef`. It is the smallest class that contains the amenable
and LEF groups and is closed under:
- subgroups and directed unions;
- finite products and amenable-quotient extensions;
- graphs of groups;
- marked limits.

Call `(G,K)` an **exact witness** if all of the following hold:
- `G = K ⋊_φ Z`;
- `K` is a nontrivial finitely generated Kazhdan group;
- `Rad_MF(G) = K × {0}`.

Every witness of `torsion-free-sofic-exact-mf-radical-over-z` is an exact witness, after choosing a lift of
`1 ∈ Z`.

## Statement

For every exact witness `(G,K)`:

```text
(PW1)  G ∈ 𝒫   iff   K ≤ H for some H ∈ 𝒫   iff   K is LEF.
```

When these conditions hold, all of the following are true.

```text
(PW2)  K is operator-MF and Rad_MF(K) = 1: the witness is of extrinsic type (DX)
       with Q = K, and [φ] has infinite order in Out(K);
(PW3)  K has no nontrivial finite quotient and K is not finitely presented;
       if G is finitely presented, then G is not LEF, and φ gives a finite
       automorphic presentation of the non-finitely-presented kernel K;
(PW4)  (K,φ) is a counterexample to (EKL1) of exact-kazhdan-radical-kernel-cannot-be-lef.
```

When they fail, `K` is a non-LEF Kazhdan group and no member of `𝒫` contains `K`. It is sofic when `G`
is, as in the flagship. In that case soficity of `G` cannot be certified by any composite of the permanence theorems that `𝒫` encodes,
starting from amenable and LEF groups:
- Elek–Szabó amalgams and HNN extensions over amenable groups;
- graph products and wreath products with amenable top group;
- sofic-by-amenable extensions;
- marked limits.

## Consequences

1. **(EKL1) is equivalent to "no exact witness lies in `𝒫`".** If (EKL1) holds, then every witness of the
   flagship is sofic for reasons outside `𝒫`. Conversely, a witness in `𝒫` refutes (EKL1) by (PW4).
2. **Class kill for intrinsic kernels.** Suppose a construction has `Rad_MF(K) = K` with `K ≠ 1`. This is
   branch (DI), and it covers:
   - (P1) of `automorphic-sofic-kazhdan-kernel-with-full-mf-radical` (swarm branch);
   - the arithmetic single-defect saturated group of the defect-core route;
   - a non-MF Titz–Witzel kernel.

   No such construction can obtain soficity of `K`, or of `G`, from `𝒫`. The named invariant is LEF of
   finitely generated Kazhdan subgroups, which every member of `𝒫` has. Every member dies at the step
   "LEF ⇒ operator-MF", which gives `Rad_MF(K) = 1 ≠ K`. For finitely presented `K` this was already
   implied by consequence 1 of the permanence node (LEF + fp ⇒ residually finite). The new cases are the
   finitely generated, non-finitely-presented kernels allowed by (P1).
3. **The only route with free soficity.** The branch `G ∈ 𝒫` is the unique branch where soficity costs
   nothing, since LEF ⇒ sofic and sofic-by-`Z` is sofic. It is exactly the OPEN claim
   `torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical`, which feeds the route
   `torsion-free-sofic-exact-mf-radical-via-lef-kernel`. That claim needs three things, each of which
   can fail independently of the others:
   - a torsion-free LEF Kazhdan group with no nontrivial finite quotient (L1);
   - the failure of (EKL1) for it (L2);
   - a finite automorphic presentation of a non-finitely-presented kernel (L3).
4. **The flagship splits cleanly.**

   ```text
   goal  <=>  (W_lef)  torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical
          or  (W_out)  a witness with K sofic, non-LEF, contained in no member of 𝒫.
   ```

   Every known sofic certificate for a non-LEF Kazhdan group lives outside `𝒫`, for example orbit full
   groups, amenable-by-sofic extensions, and new Hamming models. This holds because a finitely generated
   non-LEF Kazhdan group lies in no member of `𝒫` (PW1). The hosts of this kind in Cairn are elementary
   groups over rings, which are torsion-generated by `steinberg-images-die-in-torsion-free-groups`. So
   (W_out) needs a torsion-free Kazhdan subgroup of such a host, or a new sofic mechanism.

## Model test

- `EL_3(LC(X,F_q) ⋊ Z)` from `lef-kazhdan-group-without-finite-quotients-exists` lies in `𝒫`. It is LEF,
  Kazhdan, quotientless and MF, as (PW2)–(PW3) predict. It fails (L1), because it is generated by
  `p`-torsion.
- `torsion-free-lef-kazhdan-non-rf-seed` is torsion-free, LEF and Kazhdan, and it lies in `𝒫`. It fails
  (L1), because it has finite quotients. Accordingly (FRB4) bounds its mapping-torus radicals by the
  proper centre.
- `SL_3(Z) × Z` lies in `𝒫`. Its radical is trivial, which is consistent with (PW2), since `SL_3(Z)` is
  residually finite.

Route: `permanence-closure-radical-witnesses-have-lef-kernels-proof`.

# un-open-3 plan: simple Kazhdan groups whose simplicity depends on the characteristic

Lane `un-open-3` (UN swarm, open-ended; lens: exotic objects), 2026-09-13.

## Target

The reviewed uniform simplicity theorem `steinberg-elementary-groups-are-simple-mod-centre` assumes a
**Hausdorff** groupoid. Its load-bearing ring input, `steinberg-algebras-have-local-annihilation`
(review PASS), uses no Hausdorffness, and neither does the Lean criterion
`Pestov91.isSimpleGroup_elementaryGroup_quotient_center`, which needs only `IsSimpleRing R` and
`LocalAnnihilation R`. For non-Hausdorff ample groupoids, simplicity of `A_k(𝒢)` is governed by the
**singular ideal**, and it can depend on the characteristic of `k`. Clark–Exel–Pardo–Sims–Starling
(arXiv:1806.04362) show this for the groupoid of germs of the Grigorchuk group.

Goals:
1. **Theorem NH.** Let `𝒢` be an ample (not necessarily Hausdorff) groupoid with compact infinite unit space and
   `R = A_k(𝒢)` simple. Then for `n ≥ 3`, `EL_n(R)/Z` is simple. Paired with the CEPSS criterion
   (minimal, effective, singular ideal zero), this gives an explicit non-Hausdorff simplicity theorem.
2. **The exotic object.** Take `R_q = A_(F_q)(𝒢_Grig)`, the Nekrashevych algebra of the Grigorchuk group over `F_q`, and
   `n ≥ 3`:
   - `EL_n(R_q)` is finitely generated and Kazhdan (EJZ);
   - it contains a unital binary Cuntz family, so it is nonsofic (established node
     `d-ary-leavitt-groups-nonsofic-over-finite-fields`) and has no nontrivial MF quotient (tex Thm l.918);
   - if `q` is odd, `R_q` is simple, so `EL_n(R_q)/Z` is an infinite f.g. simple Kazhdan group;
   - if `q` is even, `R_q` has a nonzero proper ideal, and the relative elementary subgroup is a noncentral
     proper normal subgroup.
   So one groupoid produces simple Kazhdan nonsofic groups exactly in odd characteristic.
3. **Firewalls.** Record exactly which CEPSS statements are used, verbatim, and whether the even
   characteristic quotient `R_q/(singular ideal)` still gives a simple Kazhdan group.

## Why it matters

- It is the first family in the program where group simplicity reads off the characteristic, not the
  dynamics.
- It removes the Hausdorff hypothesis from the reviewed simplicity theorem, which self-similar groups need.
- It places the amenable residually finite Grigorchuk group inside units of a ring whose elementary groups are
  nonsofic and have no MF quotient: an amenable group sitting inside the paradox side.

## Not duplicated

- **un-simplicity (finished):** Hausdorff only. The review notes that the non-Hausdorff half is not relied on.
- **un-paradox / un-boundary-families:** they list (F2) Nekrashevych algebras for "no MF quotient", with simplicity
  only through the Hausdorff theorem. The characteristic dependence and the non-Hausdorff simplicity proof are
  not treated.
- **un-hyperlinear-paradox:** soficity in general. Here nonsoficity is imported from the established node for
  algebras with a unital Cuntz family, not re-proved.
- **bh-leavitt-path-steinberg-hosts** only *recalls* the CEPSS characteristic-two phenomenon, "not verified here".

## Method

Quote CEPSS and Nekrashevych verbatim (arXiv sources on MSI); land the imports; then write Theorem NH and the Grigorchuk
corollary with complete routes; wire into the UN root `kazhdan-elementary-approximation-type-mirrors-ring-type`.

---
rg: 2
id: free-group-cantor-elementary-group-lef-iff-invariant-measure
kind: claim
title: UN flagship — for a minimal topologically free free-group Cantor system with finitely generated crossed product, EL_N/Z is an infinite simple Kazhdan group that is LEF in every rank iff an invariant probability measure exists, and otherwise has no nontrivial MF quotient from rank 2n
distinct_from:
  free-group-crossed-product-matricial-iff-invariant-measure: that is the ring-level equivalence of invariant measure, residual finiteness and matricial models for these crossed products; this is the group-level dichotomy for their Kazhdan elementary groups, including simplicity and the MF failure end.
  boundary-action-elementary-simple-kazhdan-not-mf: that is one paradoxical instance, F_d acting on its boundary; this is the dichotomy over every minimal topologically free free-group Cantor system with finitely generated crossed product.
---

**ESTABLISHED** by route `free-group-cantor-el-lef-iff-invariant-measure-proof`.
- Every input passed independent review: 171f0f7525, f15928d5c9, 10083fd646.
- The assembly is unreviewed.
- **Scope:** finite coefficient field `F_q`; finitely generated crossed product; LEF for all `N >= 3` iff an
  invariant probability measure exists; otherwise every MF quotient is trivial for `N >= 2n`. The band
  `3 <= N < 2n` is open.

**Setting.**
- `F_r`, with `2 <= r < ∞`, acts minimally and topologically freely on the Cantor set `X`. `q` is a prime
  power.
- `R = LC(X, F_q) ⋊ F_r` is finitely generated as a ring, as for expansive actions.
- For `N >= 3`, put `S_N = EL_N(R)/Z(EL_N(R))`.

**Claim.** Every `S_N` is an infinite, finitely generated, simple group with property (T), and:
1. if `X` carries an `F_r`-invariant Borel probability measure, then `S_N` is LEF for every `N >= 3`;
2. if not, there is `n >= 1` such that every homomorphism from `S_N` to an MF group is trivial for all
   `N >= 2n`. So `S_N` is neither MF nor LEF for those `N`.

Hence `S_N` is LEF for every `N >= 3` iff `X` carries an invariant probability measure. This is the Pestov
9.1 witness and the non-MF obstruction, now as the two sides of one dynamical dichotomy inside one family of
Kazhdan groups. Root: `kazhdan-elementary-approximation-type-mirrors-ring-type`.

**Open band.** In case 2, the ranks `3 <= N < 2n` are not covered
(`el-n-mf-quotient-below-twice-paradoxical-level-exists`).

## Notes

**Assembly.** The complete derivation is in the route. Summary:
- **Dictionary and simplicity.**
  - `R = A_(F_q)(X ⋊ F_r)` (`crossed-products-are-transformation-steinberg-algebras`). The groupoid is
    Hausdorff and ample; it is minimal, and effective because the action is topologically free. Its unit
    space is compact and infinite.
  - So `S_N` is infinite and simple (`steinberg-elementary-groups-are-simple-mod-centre`).
  - `R` is finitely generated, so `EL_N(R)` has (T) (`elementary-groups-over-fg-rings-have-property-t`), and
    is finitely generated (`elementary-group-fg-from-fg-coefficient-ring`).
- **Case 1.**
  - Invariant measure ⇒ `R` embeds `F_q`-linearly and unitally in `prod_omega M_(N_n)(F_q)`
    (`free-group-crossed-product-matricial-iff-invariant-measure`, (i)⇒(iii), with the explicit map of
    `residually-finite-actions-give-matricial-crossed-products`). So `GL_N(R)` is LEF
    (`exactly-matricial-rings-have-lef-general-linear-groups`).
  - `Z(EL_N(R)) <= F_q^x I` (`minimal-effective-steinberg-algebras-have-scalar-centre`). The embedding sends
    scalars to scalars, so `S_N` embeds in an ultraproduct of the finite groups `GL_(N N_n)(F_q)/F_q^x I`,
    by the argument of the Pestov artifact §3.3. Hence `S_N` is LEF.
- **Case 2.**
  - No invariant measure ⇒ `2n[1] <= n[1]` in `V(R)`, and every homomorphism from `EL_N(R)` to an MF group
    is trivial for `N >= 2n` (`no-invariant-measure-steinberg-elementary-no-mf-quotient`, with `F_q`
    countable and `X` second countable).
  - Homomorphisms from `S_N` pull back to `EL_N(R)`, so they are trivial too.
  - `S_N` is nontrivial, so it is not MF, hence not LEF (`lef-implies-operator-mf`).

**Firewalls.**
- **Kaplansky.** Measure ⇒ stable finiteness in general contains char-`p` Kaplansky stable finiteness
  (`measure-side-stable-finiteness-contains-char-p-kaplansky`). For free groups this is bypassed, because
  measure ⟺ residually finite action (Kerr–Nowak, via Ma), which supplies towers directly. Other groups need
  their own tower theorem.
- **Finite generation.** It is needed for (T). Odometer-type towers give LEF but not Kazhdan groups
  (`odometer-crossed-product-elementary-groups-not-kazhdan`).

**Review (un-verify-3, 2026-09-13): PASS (assembly).** Every required node has a PASS review line or is an established import. Re-derived: Step 0 (minimal effective groupoid, simple `S_N` with scalar centre, (T)); Step 1 (with `Λ = F_q^x` finite, the kernel of `∏_ω GL → ∏_ω GL/ΛI` is `[ΛI]` and `EL_N(R) ∩ ΛI = Z`, so `S_N` embeds in an ultraproduct of finite groups); Step 2 (trivial MF quotients from rank `2n`, so not MF, not LEF). Requires note: the route asserts finite generation of `S_N` but does not require `elementary-group-fg-from-fg-coefficient-ring` (established), which this body cites. `research/artifacts/un-review3-2026-09-13-part3.md` §1.

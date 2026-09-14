---
rg: 2
id: crossed-product-el-kazhdan-iff-finite-field-and-subshift
kind: claim
title: For a zero-dimensional system (X,T) and a field k, EL_n(LC(X,k) ⋊ Z) with n ≥ 3 is Kazhdan iff it is finitely generated iff k is finite and X is a subshift
distinct_from:
  odometer-crossed-product-elementary-groups-not-kazhdan: that is one non-expansive example, the dyadic odometer over a finite field; this is the equivalence for every zero-dimensional system and every field.
---

**ESTABLISHED (unreviewed)** by `crossed-product-el-kazhdan-iff-finite-field-and-subshift-proof`.

**Statement.** Let `X` be a nonempty compact metrizable zero-dimensional space, `T` a homeomorphism of `X`, `k` a field, `R = LC(X,k) ⋊_T Z` (finite sums `Σ f_j u^j`, `u f u^(-1) = f∘T^(-1)`), and `n ≥ 3`. The following are equivalent:
1. `R` is finitely generated as a ring.
2. `EL_n(R)` is finitely generated.
3. `EL_n(R)` has property (T).
4. `k` is finite and `(X,T)` is topologically conjugate to a subshift over a finite alphabet.

**Use for the note** (`simple_kazhdan_sofic_group.tex`, lane sk-hypotheses-sharp): among zero-dimensional systems and coefficient fields, the hypotheses "subshift over a finite alphabet" and "`F_2`" are the ones that give finite generation and property (T). For an infinite minimal system that is not expansive (e.g. an odometer), or for an infinite field, `EL_n(R)/Z` is still simple (`steinberg-elementary-groups-are-simple-mod-centre`), but it is not finitely generated and has no property (T).

The infinite-field half was derived independently in `research/artifacts/sk-coefficients-proposal-2026-09-13.md` §5.

**Review (sk-verify-5, 2026-09-13): PASS.** All five implications re-derived:
- (4 ⇒ 1): `u^{±1}`, the letter indicators and the constants generate `R`.
- (1 ⇒ 3): Ershov–Jaikin-Zapirain for `n ≥ 3`.
- (3 ⇒ 2): a group with (T) is compactly generated. This is Bekka–de la Harpe–Valette, Theorem 1.3.1 (recalled, not re-read).
- (2 ⇒ 1): the entries of a finite generating set and their inverses generate `R`, because every `e_12(r)` has entry `r`.
- (1 ⇒ 4): the values of finitely many coefficient functions generate `k` as a ring, so `k` is finite. The subring of `𝒫`-orbit-measurable sums is all of `R`, so the itinerary map to `𝒫^Z` is an injective continuous equivariant map.

See `research/artifacts/sk-review-5-2026-09-13-part1.md` §1.

**Review (sk-verify-23, 2026-09-14).**
- **Import (3 ⇒ 2) verified at source.** Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, authors' draft of February 23, 2007, §1.3, p.41, Theorem 1.3.1: "Let G be a locally compact group with Property (T). Then G is compactly generated. In particular, a discrete group Γ with Property (T) is finitely generated." The draft attributes the result to Kazhdan. The printed 2008 edition (doi:10.1017/CBO9780511542749) was not opened.
- **Note wording.** The F_2, n = 3 wording of this claim proposed for the note (sk-usefulness P2) is PASS-WITH-FIXES. Its W1: say only that the subshift hypothesis cannot be dropped. See `research/artifacts/sk-verify-23-2026-09-14.md` §2.

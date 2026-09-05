---
rg: 2
id: full-complementary-idempotent-elementary-full-mf-radical
kind: claim
title: Elementary groups over a ring with a full complementary idempotent have full MF radical in every rank at least four
distinct_from:
  generic-leavitt-self-compression-full-mf-radical: that assumes a full binary Leavitt family, rank at least sixteen, and property (T) of `E_4(R)` and `E_n(R)`; this assumes one one-sided inverse whose complementary idempotent generates the unit ideal, works from rank four, and derives the Kazhdan input from Ershov--Jaikin-Zapirain on finitely generated subrings.
  binary-leavitt-all-ranks-full-mf-radical: that is one algebra, `L_{F_2}(1,2)`, at every rank including one to three, through the rank-twelve headline and prefix-code self-similarity; this is a criterion on the coefficient ring, valid for every countable ring satisfying it, and says nothing below rank four.
  rank-twelve-leavitt-simple-non-mf: that is the printed headline group with simplicity; this drops simplicity, the sandwich theorem and every `K_1` input from the non-MF argument and recovers that group's non-MF clause as one instance.
  property-t-free-leavitt-full-mf-radical: that asks for the binary-Leavitt collapse with no Kazhdan hypothesis; this still consumes property (T) of `EL_3` and `EL_n` over finitely generated rings, so it does not touch that goal.
artifacts:
  - research/artifacts/full-complementary-idempotent-check-2026-09-05.md
  - non_mf_groups_exist.tex
---

Let `R` be a countable unital ring with `s, t ∈ R` such that

```text
ts = 1,        R (1 - st) R = R,
```

the second being an equality of two-sided ideals.  Then for every `n ≥ 4`
every homomorphism from `EL_n(R)` to an MF group is trivial; in the
repository's language, `Rad_MF(EL_n(R)) = EL_n(R)`.  No finite generation of
`R` is assumed.

The hypothesis holds for every countable simple unital ring that is not
directly finite (`e = 1 - st ≠ 0` generates a nonzero ideal), for every
Leavitt algebra `L_k(1,m)` with `k` a countable field and `m ≥ 2`
(`t_2 (1 - s_1 t_1) s_2 = 1`), and for finitely many pairs `t_ν s_ν = 1` whose
complementary idempotents jointly generate the unit ideal (one compressor and
one centralizer per pair, same source `EL_3`).

For `R ≠ 0` satisfying the hypothesis, `C*_r(EL_n(R))` is separable, stably
finite, and not MF (faithful canonical trace; an MF embedding would embed the
canonical unitaries).  Printed as `thm:full-defect-ring` and
`cor:simple-infinite-ring` in `non_mf_groups_exist.tex`.

# Slide-group screen for the (C2) pair (2026-09-18)

Node: `c2-slide-route-passes-every-relation-module-test`.

Each **slide group** here is `Γ'' = ⟨x,y,t | f(u_0), f(u_1)⟩` with `f(z) = Π_z^{-1} φ_0(z)` and
`[Π_z] = m_z[t]`, where `m = d` is the certificate of `verify_unimodular.py` (w11), so `c·m = 1`.
- By (S1), every variant has `Qκ` unitriangular, so its relation module equals that of `G`.
- A homomorphism to a finite group with `t ≠ 1` therefore proves `Λ = ⟨⟨t⟩⟩ ≠ 1`. Such a
  homomorphism must be onto a group with a perfect subgroup containing `t`.
- Counts are homomorphisms `Γ'' → P` with `t ≠ 1`, with `x` taken up to conjugacy.
  `groups.py` supplies the permutation groups `A_5, PSL(2,7), A_6, PSL(2,8), PSL(2,11), PSL(2,13)`.

## Reproduce

```
export PYTHONPATH=../c2-free-by-cyclic-2026-09-18 SCREEN_CACHE=/some/dir
SURVIVORS=surv.jsonl bash run_screen.sh        # stage 1: A_5, PSL(2,7)
python3 retest.py surv.jsonl A6,PSL28,PSL211,PSL213   # stage 2
python3 pair_invariant.py                      # (P1) identity
python3 gap_li.py surv.jsonl 5                 # low-index counts and TzGoGo (needs GAP)
```

`run_screen.sh` runs `screen.py A5,PSL27 60 <mode> 11` for each of the modes `perm`, `wins`,
`pair` and `perm+wins+pair`. Each mode produces 60 variants and two signs (`t ↦ t^{±1}`), plus
the base datum.

## Base datum (variant 0, `Π_z` as in w11)

- The relator lengths are 391 and 350.
- It has 18 homomorphisms to `A_5` and 16 to `PSL(2,7)` with `t ≠ 1`, for both signs. So `Λ ≠ 1`.
- GAP `LowIndexSubgroupsFpGroup` counts subgroups of index at most 2, 3, 4, 5 as
  `[4, 8, 16, 31]`, against `[4, 8, 16, 24]` for `G = ⟨x,y|w⟩`.
- `TzGoGo` keeps 3 generators, with relator lengths `[350, 391]`. So there is no Tietze collapse.

## Stage 1: A_5 and PSL(2,7) (480 variants)

The mutations keep every coefficient `m_z ∈ ZG`, so `κ` is unchanged:
- `perm` permutes the factors of `Π_z`;
- `wins` appends a conjugate of `w^{±1}` to some conjugators;
- `pair` inserts a cancelling pair `(u t u^{-1})(u w' t^{-1} w'^{-1} u^{-1})`.

| mode | variants | A_5 = 0 | PSL(2,7) = 0 | both 0 | total relator length |
|---|---|---|---|---|---|
| perm | 120 | 43 | 43 | 13 | 645–775 |
| wins | 120 | 32 | 22 | 5 | 1029–2329 |
| pair | 120 | 34 | 25 | 8 | 741–1613 |
| perm+wins+pair | 120 | 33 | 29 | 9 | 1267–2887 |

That gives 35 survivors of both groups. They are the JSON lines of `surv.jsonl`, with fields
mode, seed, var, sgn, D, R0, R1.

## Stage 2: survivors in A_6, PSL(2,8), PSL(2,11), PSL(2,13)

`retest.py` stops at the first group with a nonzero count. The columns are mode, seed, variant,
sign, the two relator lengths, and the counts.

```
perm 11 7 1 405 352 A6:0 PSL28:66
perm 11 17 -1 403 358 A6:20
perm 11 20 -1 409 364 A6:0 PSL28:0 PSL211:12
perm 11 21 1 405 350 A6:0 PSL28:24
perm 11 22 1 391 342 A6:0 PSL28:0 PSL211:20
perm 11 23 1 391 348 A6:36
perm 11 25 1 401 362 A6:20
perm 11 26 -1 365 362 A6:0 PSL28:54
perm 11 38 -1 383 344 A6:0 PSL28:27
perm 11 41 1 413 358 A6:20
perm 11 44 1 395 342 A6:0 PSL28:27
perm 11 51 -1 399 358 A6:20
perm 11 52 -1 409 364 A6:0 PSL28:21
wins 11 2 -1 1091 682 A6:36
wins 11 19 1 889 626 A6:0 PSL28:21
wins 11 24 1 875 646 A6:0 PSL28:54
wins 11 35 1 959 692 A6:0 PSL28:27
wins 11 43 1 711 486 A6:20
pair 11 12 1 433 434 A6:0 PSL28:54
pair 11 13 1 553 528 A6:16
pair 11 20 -1 603 608 A6:40
pair 11 22 -1 827 786 A6:20
pair 11 25 -1 553 674 A6:36
pair 11 31 1 763 692 A6:56
pair 11 34 1 511 590 A6:20
pair 11 35 1 595 530 A6:0 PSL28:0 PSL211:10
perm+wins+pair 11 10 1 1151 1132 A6:0 PSL28:24
perm+wins+pair 11 13 -1 1269 886 A6:36
perm+wins+pair 11 15 1 905 1008 A6:20
perm+wins+pair 11 16 -1 1393 876 A6:16
perm+wins+pair 11 29 -1 863 706 A6:32
perm+wins+pair 11 31 1 1309 1088 A6:20
perm+wins+pair 11 47 1 1511 1048 A6:40
perm+wins+pair 11 49 1 1255 952 A6:0 PSL28:27
perm+wins+pair 11 49 -1 1569 1032 A6:0 PSL28:21
```

Every one of the 35 survivors is killed:
- `A_6` kills 19;
- `PSL(2,8)` kills 13;
- `PSL(2,11)` kills 3;
- `PSL(2,13)` is never reached.

## Conclusion

None of the slide groups tested is isomorphic to `G`. They are the base datum (both signs of `t`)
and 480 randomized variants (240 data, each with both signs). Each has a homomorphism onto a perfect group in
`{A_5, PSL(2,7), A_6, PSL(2,8), PSL(2,11)}` with `t ≠ 1`, so `Λ ≠ 1` for all of them.

This is consistent with (S1): the module is blind, and finite simple quotients see `Λ` easily.
It proves `Λ ≠ 1` only for the variants that are killed. It says nothing about slide data outside
this random family, such as data with other coefficient vectors `m`, `c·m = ±h`, or data that are
not built from the certificate `d`.

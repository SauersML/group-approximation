---
rg: 2
id: malnormal-free-doubles-surface-certificates
kind: claim
title: Finite certificates give closed surface subgroups in 32 of 40 random doubles of F_2 along malnormal rank-two subgroups, 25 of them certified one-ended
distinct_from:
  one-ended-hyperbolic-groups-contain-surface-subgroups: that asks for every one-ended hyperbolic group; this gives finite surface and one-endedness certificates for doubles F_2 *_C F_2 along a finitely generated edge group C, and applies them to 40 random rank-two malnormal C
  cyclic-graphs-of-free-groups-contain-surface-subgroups: that is Wilton's theorem for cyclic edge groups; here the edge group C has rank two, and Wilton is used only after passing to a vertex subgroup A whose intersection with C is cyclic
  carpet-boundary-hyperbolic-groups-have-surface-subgroups: that concerns groups with Sierpinski-carpet boundary; this is a finite fibre-product certificate in free doubles, with no boundary hypothesis
artifacts:
  - research/malnormal-free-doubles-surface-certificates-proof.md
  - experiments/malnormal-doubles-surfaces-2026-09-17/stallings.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/search_genus1.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/search_cores.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/verify_certificates.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/verify.log
  - experiments/malnormal-doubles-surfaces-2026-09-17/out_small.txt
  - experiments/malnormal-doubles-surfaces-2026-09-17/out_ex_genus1.txt
  - experiments/malnormal-doubles-surfaces-2026-09-17/out_cores_cal.txt
  - experiments/malnormal-doubles-surfaces-2026-09-17/search_quotients.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/search_filling.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/out_q_ex1_d2.txt
  - experiments/malnormal-doubles-surfaces-2026-09-17/out_q_ex1_d3.txt
  - experiments/malnormal-doubles-surfaces-2026-09-17/search_fatgraphs.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/search_pairs.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/out_pairs_r2.txt
  - experiments/malnormal-doubles-surfaces-2026-09-17/out_pairs_r3.txt
  - experiments/malnormal-doubles-surfaces-2026-09-17/verify_lemma6.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/verify_lemma6.log
  - experiments/malnormal-doubles-surfaces-2026-09-17/one_ended_certificate.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/out_one_ended.txt
---

Notation: `F_2 = F(a,b)`, with `A = a^-1` and `B = b^-1` in words, and `D(F_2,C) = F_2 *_C F_2` is
the double along `C`.

## Statement

1. **Criterion. ESTABLISHED, proof in `malnormal-free-doubles-surface-certificates-proof`.** Let
   `A <= F_2` be finitely generated with `A ∩ gCg^-1 = <w>` for some `g`.
   - **Surface case.** If `A = pi_1(Y)` for a folded one-boundary ribbon graph `Y` of genus `g`
     with boundary word `w`, then `D(F_2,C)` contains the closed orientable surface group of genus
     `2g`.
   - **Wilton case.** If `C` is malnormal, `rank A >= 2`, and `w` is filling in `A`, then
     `D(F_2,C)` contains a quasiconvex closed surface subgroup of `A *_<w> Abar`.
   - **Finite check.** `A ∩ gCg^-1` is read off one component of the fibre product
     `Gamma_A x Gamma_C`.
2. **Bounded segments. ESTABLISHED, same proof file.** Let `C` be malnormal, and let `K(C)` be the
   longest reduced path in the off-diagonal part of `Gamma_C x Gamma_C`.
   - Every unbranched segment of a cyclic core `Gamma_A` in either case has length at most `K(C)`.
   - So the genus-1 certificate search is finite and complete.
   - Along a fixed `w`, the admissible cores are exactly the rank-1-preserving quotients of the
     circle graph of `w`, which `search_cores.py` enumerates completely.
3. **Four genus-2 surface subgroups. ESTABLISHED (computer-certified), `verify.log`.** For each `C`
   below, `C` has rank 2, has infinite index and is malnormal, and `D(F_2,C)` contains the closed
   genus-2 surface group `<A, Abar>`, where `A = pi_1(theta(x,y,z))` and `w = x Y z X y Z`:

   | `C` | theta edges `x, y, z` | `w` |
   |---|---|---|
   | `<abaBa, AbbAABB>` | `b, AB, a` | `bbaaBABA` |
   | `<bbABBA, aaBBAAbb>` | `B, b, aa` | `BBaabbAA` |
   | `<aaBBBBA, AbbabbA>` | `A, BB, abb` | `AbbabbaBBBBA` |
   | `<AAAbbb, AAAbba>` | `B, a, Ab` | `BAAbbaBa` |

   `verify_certificates.py` checks every hypothesis from scratch. As an independent sanity check, it
   also enumerates all `A`-words of length at most 7 and finds that only `w^{±1}` land in `C`.
4. **Exact genus-1 negatives. Computation, exhaustive by item 2.** The batch in `out_small.txt`
   draws 40 random malnormal rank-2 `C` of infinite index, generator lengths 4--8, seed 20260917.
   - 4 of the 40 have a genus-1 certificate.
   - For each of the other 36, no folded genus-1 one-boundary ribbon graph `Y` has
     `pi_1(Y) ∩ gCg^-1 = pi_1(∂Y)` for any `g`.
   - The same holds for `C = <abaBB, BABaBBa>` (`out_ex_genus1.txt`).
   - This rules out only genus-1 certificates of the surface kind. It says nothing about higher
     genus or the Wilton case.
5. **Multi-boundary certificates, genus 2 and 3. ESTABLISHED (computer-certified), Lemma 6 of the
   proof file, `verify_lemma6.log`.** A folded ribbon graph `Y` of rank `r >= 2` whose boundary words
   each close up in `Gamma_C`, in pairwise distinct rank-1 components of `Y x Gamma_C`, gives the
   closed orientable surface group of genus `r` in `D(F_2,C)`. On the same 40 groups:
   - `search_pairs.py` at rank 2 certifies 6 of the 40 (`out_pairs_r2.txt`), and at rank 3 it
     certifies 32 of the 40 (`out_pairs_r3.txt`). The 6 lie among the 32.
   - `verify_lemma6.py` shares no code with the search. It re-folds `Gamma_C`, rebuilds `Y`,
     re-finds a rotation system and the vertices `c_j`, rechecks every hypothesis of Lemma 6 and
     brute-forces short loops. It confirms all 38 certificates (`verified 38 / 38`).
   - So 32 of the 40 random malnormal rank-2 `C` give a double containing a closed surface group of
     genus at most 3.
   - The rank-3 search reports no certificate for the other 8: batch indices 2, 3, 4, 5, 9, 19, 28,
     29. The search is complete by the bounded-segment lemma, but those negatives were not checked
     independently.
6. **One-endedness. ESTABLISHED (computer-certified), Lemma 7 of the proof file,
   `out_one_ended.txt`.** Start from `H_0 = A = pi_1(Y)` for a certificate `Y`, and set
   `H_{k+1} = <H_k, u : H_k ∩ uH_ku^{-1} != 1>`. For 25 of the 32 certified `C` some `H_k` is all of
   `F_2`, so `D(F_2,C)` is one-ended.
   - For the other 7 the test is undecided: `<AABa, aaba>`, `<aaBBBBA, AbbabbA>`, `<BAbA, ABAAAA>`,
     `<babABaa, AbaBBAA>`, `<ABBB, BAbabb>`, `<BBBBBaBA, BBaa>`, `<BAABaaa, AbAA>`.
   - Of the four genus-2 examples of item 3, all but `<aaBBBBA, AbbabbA>` are certified one-ended.

## Status of the ambient groups

- **Hyperbolicity.** `D(F_2,C)` is hyperbolic when `C` is malnormal and finitely generated, by the
  combination theorem for amalgams along a malnormal quasiconvex subgroup (Bestvina--Feighn;
  Kharlampovich--Myasnikov, *Hyperbolic groups and free constructions*). That is cited here, not
  source-checked.
- **One-endedness.** Item 6 proves it for 25 groups. It does not use hyperbolicity.
- **Cyclic splittings. Not checked.** If one of these groups splits over a cyclic subgroup, Wilton's
  reduction to the rigid case applies to it. That reduction is not coverage. The surface subgroups
  of items 3 and 5 exist either way.
- **Known classes. Not checked beyond the list in the flagship node.** The edge group has rank 2, so
  Wilton's cyclic-edge theorem does not apply to the splitting itself, and the groups are specific,
  not random in the Calegari--Walker sense.

So items 3, 5 and 6 give 25 explicit one-ended hyperbolic groups (hyperbolicity cited) with closed
surface subgroups of genus 2 or 3, outside the cyclic-edge class as presented.

## Paradigm answers

- **Why this works where the dead approaches failed.**
  - Wilton, Kim--Oum and Calegari--Wilton need cyclic edge groups. Calegari--Walker needs random or
    one-relator structure.
  - The edge group of a double along a rank-2 `C` is neither cyclic nor random. Its surfaces are not
    visible to scl or to cyclic-edge pattern arguments.
  - We change the object. Instead of the edge group we look at a vertex subgroup `A` that meets `C`
    in a cyclic group. Lemma 1 of the proof file turns `<A, Abar>` into an amalgam over a cyclic
    group, which is either a surface group directly or in Wilton's class.
  - Everything is decided by finite fibre products of Stallings graphs, and malnormality bounds the
    search (item 2).
- **First falsifiable step.** The exhaustive genus-1 search on random malnormal `C`, done. It could
  have returned no certificate at all. It returned 4 of 40, and the rank-3 multi-boundary search
  returned 32 of 40.
- **Calibration.**
  - `C = F_2`: no certificate.
  - `C = <abAB>` (Wilton / Kim--Oum case): the rose `b, a` certifies, and `search_cores.py`
    recertifies it.
  - `C = <aa, bb>` (not malnormal): no genus-1 certificate.
  - `search_cores.py` on `<AAAbbb, AAAbba>` independently rediscovers the theta certificate at
    `|w| = 8` (`out_cores_cal.txt`).

## Attempts

- **Depth-limited quotient search** (`search_quotients.py`) on `C = <abaBB, BABaBBa>`: no filling
  core with `|w| <= 16` at depth 2, or with `|w| <= 10` at depth 3. It is superseded by the complete
  enumeration `search_cores.py`.
- **Rank-2 `A = <u,v>` with `|u|, |v| <= 4`** (`search_filling.py`) on the same `C`: no filling
  core in 12720 pairs.

---
rg: 2
id: fake-surface-census-misses-acyclic-classes
kind: claim
title: The published census of acyclic cellular fake surfaces misses one class of complexity 3, 58 of complexity 4, and 3 of complexity 5 without small disks
artifacts:
  - research/artifacts/hl-andrews-curtis-fake-surfaces-2026-09-14.md
---

**ESTABLISHED** through `fake-surface-census-recount-proof` (exhaustive exact
computation). Unreviewed.

L. Fagan, Y. Qiu and Z. Wang, *Classification of Cellular Fake Surfaces*,
arXiv:2406.09439v3, list acyclic cellular fake surfaces in `fakesurfaces.csv` of
github.com/lucasfagan/Fake-Surfaces (commit 7bcff60). The file has:
- 2, 17, 238 and 4618 surfaces of complexity 1, 2, 3 and 4;
- 514 surfaces of complexity 5 without small disks (disks of boundary length 1 or 2).

Up to PL homeomorphism the true counts are 2, 17, **239**, **4676** and **517**.
Every listed surface is one of these classes, and no two listed surfaces are
homeomorphic. So the list misses exactly 1, 58 and 3 classes.

**Cause.** The duplicate test `are_same` in `fakesurfaces_cla_6.py` accepts
relabelings of signed edge letters that do not respect inverses. The artifact gives
two non-homeomorphic complexity-3 surfaces that it merges.

**What it affects.**
1. The main theorem of Fagan–Qiu–Wang, *Stable Andrews–Curtis conjecture via fake
   surfaces and Zeeman conjecture*, arXiv:2412.12293v2, reduces contractible fake
   surfaces of complexity at most 5 by checking its Complexity Reduction Lemma
   against this list (`main.tex` l.2075: "Using the classification of contractible
   fake surfaces up to complexity 5 from \cite{fagan2024classification}, it is easy
   to check that all satisfy one of the conditions of Lemma~\ref{lem:crl}.").
   The 62 missing classes are not covered by that check.
2. The corollary of arXiv:2406.09439v3 that acyclic cellular fake surfaces of
   complexity at most 4 are contractible was verified on the listed surfaces only.

Neither statement is refuted here: only the printed verification has a hole.

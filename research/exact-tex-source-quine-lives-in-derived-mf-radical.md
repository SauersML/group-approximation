---
rg: 2
id: exact-tex-source-quine-lives-in-derived-mf-radical
kind: claim
title: An exact TeX source quine is encoded by identity inside the derived MF radical of one fixed finitely presented non-MF group
artifacts:
  - f1746067c:mf_radical_tex_quine.tex
  - GroupApproximation/Computability/MFRadicalQuine.lean
  - GroupApproximation/Computability/MFRadicalQuineSource.lean
  - scripts/build_mf_radical_tex_quine.py
  - scripts/check_mf_radical_tex_quine.py
  - research/artifacts/exact-mf-radical-tex-quine-audit-2026-08-25.md
distinct_from:
  single-finitely-presented-mf-radical-computer: that supplies a universal halting-bit family in the fixed carrier; this adds output-sensitive equality words and binds them to every literal byte of a source quine.
  reverse-kleene-support-profile-nonmf: that makes a presentation branch depend on proof search about itself; here an executable syntactic fixed point is recovered exactly from identity queries in the derived MF residual.
  mf-radical-godel-word: that internalizes proof-system incompleteness; this internalizes a complete executable manuscript source stream, with independent byte custody.
---

**ESTABLISHED (2026-08-25).**  Let `U_MF = E * B` be Cairn's fixed
finitely presented MF-radical computer.  The repository now contains an exact
TeX source quine `M` and a partial-recursive code `q_M` computing the literal
byte stream of `M`, followed by the sentinel `256`.  For every position `i`
and proposed cell `b`, there is a word

```text
W(i,b) in [Rad_MF(U_MF), U_MF]
```

such that

```text
W(i,b) = 1  iff  q_M(i) returns b.
```

Thus the unique identity answer among `b = 0,...,256` recovers every source
cell and the sentinel.  Wrong guesses are nonidentity MF-invisible words, so
the encoding has internal contrast and does not collapse all queries.

The embedded Python program reads no file and outputs the complete TeX source
byte-for-byte.  The independent checker compares its stdout with the TeX,
regenerates the fixed point from the canonical template, and compares the
generated Lean natural-number ledger with the same bytes.  Lean proves the
output filter partial recursive, every query word MF-invisible and in the
commutator residual, and identity equivalent to exact output equality.

This is not claimed to be a seed-free analytic proof of non-MF.  The literal
non-MF group `E` remains the analytic seed.  The new content is that exact
self-reproducing source, including the manuscript proving what is encoded,
is compiled through the Boone factor and faithfully mixed with the nontrivial
invisible mark by a free-product commutator gate.

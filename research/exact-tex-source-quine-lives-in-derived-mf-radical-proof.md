---
rg: 2
id: exact-tex-source-quine-lives-in-derived-mf-radical-proof
kind: route
title: Compile exact source-cell equality tests and gate them through the invisible mark
target: exact-tex-source-quine-lives-in-derived-mf-radical
requires:
  - single-finitely-presented-mf-radical-computer
  - faithful-radical-commutator-gate
artifacts:
  - GroupApproximation/Computability/MFRadicalQuine.lean
  - GroupApproximation/Computability/MFRadicalQuineSource.lean
  - f1746067c:mf_radical_tex_quine.tex
  - scripts/check_mf_radical_tex_quine.py
---

For a partial-recursive code `q`, position `i`, and candidate value `b`, compose
the evaluator with the partial equality acceptor which returns `0` exactly
when `q(i)=b` and is undefined otherwise.  Compile that closed test into the
fixed Boone controller, then apply the faithful commutator gate with the
literal nonidentity MF-invisible mark.  The Boone theorem converts test-domain
membership into identity; the gate preserves identity exactly and places the
word in `[Rad_MF(U_MF),U_MF]`.

The final TeX source is a deterministic chunked fixed point: its embedded
program carries a bounded-line representation of a template and inserts that
same representation at the unique code position.  Define `manuscriptCell` by
looking up the generated literal byte list and returning `256` outside it.
Lean proves this total stream computable, chooses a universal code computing
it, and instantiates the output-query theorem.  The external checker closes
the custody boundary that Lean does not parse: generator output, embedded
program stdout, checked-in TeX bytes, and the Lean ledger must all agree
exactly.

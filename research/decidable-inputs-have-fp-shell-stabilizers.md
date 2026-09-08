---
rg: 2
id: decidable-inputs-have-fp-shell-stabilizers
kind: claim
title: A decidable infinite finite presentation admits an enumeration with three finitely presented shell stabilizers
distinct_from:
  infinite-shift-higman-compiler: that asks for finite presentation of a permutation group on N obtained by adjoining E_2; this asks for three stabilizers in a Cantor group obtained by adjoining V to shell permutations. No equivalence between these hypotheses is asserted.
artifacts:
  - research/artifacts/boone-higman-finite-state-and-shell-germ-limits-2026-09-08.md
---

For every infinite finitely presented group P with decidable word
problem, there is a bijection nu:P->N for which the following three
subgroups of E_nu=<V,hat(P)> are finitely presented. Use the exact
shell construction in `shell-cantor-embeddings-are-finite-germ-extensions`,
and fix p=0^infinity and q=1*0^infinity. Singularities are relative
to V.

1. A_1={e: sing(e) subset {p}, e(p)=p}.
2. A_12={e: sing(e) subset {p}, e(p)=p, e(q)=q}.
3. A_2={e: sing(e) subset {p,q}, e(p)=p, e(q)=q}.

This is an OPEN construction problem. Finite generation of P and
E_nu, decidability of P's word problem, and a description of the
isotropy germ group do not prove these finite-presentation clauses.
The route `boone-higman-via-shell-germ-stabilizers` proves that the
three clauses would suffice for the full conjecture.

No uniformity or computability of nu is included in the assertion.
An effective choice with a proof of the three clauses would suffice,
but finite tables of values of nu are not a certificate of them.

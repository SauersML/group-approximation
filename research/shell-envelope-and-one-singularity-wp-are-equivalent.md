---
rg: 2
id: shell-envelope-and-one-singularity-wp-are-equivalent
kind: claim
title: Recursive presentability and word-problem decidability coincide for the shell envelope and its one-singularity stabilizer
artifacts:
  - research/artifacts/boone-higman-arithmetic-shell-benchmark-2026-09-08.md
---

For every infinite finitely generated P and every enumeration nu,
write E=E_nu and A_1={e in E: sing(e) subset {p}, e(p)=p}.
The following four conditions are equivalent:

1. E admits a recursive presentation.
2. E has decidable word problem.
3. A_1 admits a recursive presentation.
4. A_1 has decidable word problem.

Each condition implies computability of nu and recursive presentability
of the isotropy germ quotient Q. The reduction from the word problem
of A_1 to that of E uses finitely many commutators to decide whether
a local representative is identity on a specified cone. It does not
assume that triviality of germs in Q is decidable.

These are statements about recursive presentations. No equivalence
between finite presentation of E and of A_1 is asserted, and no
finite presentation or word-problem algorithm for Q follows.

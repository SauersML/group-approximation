---
rg: 2
id: atiyah-passes-to-torsion-free-elementary-amenable-extensions
kind: claim
title: Strong Atiyah passes from a normal subgroup to extensions with torsion-free elementary amenable quotient
distinct_from:
  elementary-amenable-torsion-free-strong-atiyah: that is Linnell's theorem for torsion-free elementary amenable groups themselves; this is the extension step over an arbitrary normal subgroup that already satisfies the conjecture.
---

**ESTABLISHED (literature import).** Let `K` be a subfield of `C` closed under complex
conjugation. Suppose `H` is torsion-free and satisfies the Strong Atiyah conjecture over `K[H]`.
If `G` is an extension of `H` with torsion-free elementary amenable quotient `G/H`, then `G`
satisfies the Strong Atiyah conjecture over `K[G]`.

## Source

T. Schick, *Integrality of L^2-Betti numbers*, arXiv:math/0001101v3 (15 October 2001), the
corrected version of the Math. Ann. paper of the same title. The text was extracted on MSI from
the arXiv PDF and read on 2026-09-12.

* **Corollary 3.2**, verbatim: "Suppose H is torsion-free and fulfills the strong Atiyah
  conjecture over KH with K = K̄. If G is an extension of H with elementary amenable torsion-free
  quotient then G fulfills the strong Atiyah conjecture."
* It follows from Proposition 3.1, which Schick says "is implicit in Linnell's work", referring to
  Linnell, *Division rings and group von Neumann algebras*, Forum Math. 5 (1993).
* The infinite cyclic step is Case 1 of that proof. Lemma 3.5 shows each `1 + q_1 t + ... + q_k t^k`
  with `q_i in U(H)` is invertible in `U(G)`. The Ore completion of `D(H) * G/H` is then a skew
  field inside `U(G)` that equals `D(G)`.
* Lemma 3.4: for torsion-free `G`, Strong Atiyah over `K` holds iff the division closure `D(G)`
  of `K[G]` in `U(G)` is a skew field.

## Trust surface

* **Removed results.** Remark 1.1 of v3 says an earlier version had a gap pointed out by Pere Ara
  and that everything based on it was removed. Corollary 3.2 and Proposition 3.1 appear in v3.
* **Field hypothesis.** `K = K̄` is closure under complex conjugation, which Lemma 3.6 uses.
* **Depth of reading.** Only the statements and Case 1 of the proof were read in detail. The
  elementary amenable induction (Case 3) was not re-derived.

---
rg: 2
id: cocf-group-torsion-order-bounded-by-word-length-citation
kind: route
title: "Import: Bishop-Bodart-Issini-Perego Thm 2.7(a), explicit Nerode-class bound n*ord(g) <= 2^((mn^2+1)^2)"
target: cocf-group-torsion-order-bounded-by-word-length
requires: []
---

Literature import, not a reproof.

A. Bishop, C. Bodart, L. Issini, D. Perego, *Period growth and co-context-free groups*, arXiv:2601.13058v1
(19 Jan 2026). PDF read 2026-09-17, §2.2, pp. 11–12.

Definition (p. 1, verbatim): "Let G be a group and S a finite generating set. ... We define the period growth as
p^D_(G,S)(n) = max {ord(g) | g ∈ G and ∥g∥_S ⩽ n} ∩ D."

Theorem 2.7 (verbatim): "Let G be a co-context-free group. (a) The period growth satisfies p_G(n) ⪯ exp(n^4).
(b) If D ⊆ D_k for some integer k, then p^D_G(n) ⪯ exp(n^2)."

Proof of (a) (verbatim excerpt): "We fix a generating set S. By Theorem 2.2, we may assume that the context-free
language coWP(G,S) is given by a grammar in Chomsky normal form, and let m be the number of variables in this grammar.
Consider g∈G and fix w∈S* a word representing it of length n=∥g∥_S. Due to Theorem 2.6 the language
coWP(G,S)∩{w}* is context-free, produced by a grammar in Chomsky normal form with mn^2 + 1 variables. ... (a) By [43,
Theorem 6], the language L_g is recognised by a deterministic finite-state automaton with |Q| ⩽ 2^((mn^2+1)^2)
states. If g has finite order, then the language L_g defines n·ord(g) Nerode congruences classes. We conclude that
n·ord(g) ⩽ |Q| ⩽ 2^((mn^2+1)^2)".

Reading. Their "Theorem 2.2" is their Lemma 2.2 (Chomsky normal form, [31, §7.1.5]). The argument uses only that
`coWP(G,S)` is context-free for the fixed finite generating set `S`, so the explicit inequality holds for any such `S`.
That is the statement of the target claim.

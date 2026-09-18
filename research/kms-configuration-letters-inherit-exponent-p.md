---
rg: 2
id: kms-configuration-letters-inherit-exponent-p
kind: claim
title: In the Kharlampovich-Myasnikov-Sapir presentation the exponent-p law on the A-letters forces x_u^p = 1 for every configuration letter x_u with u != q_j, so dropping the base exponent law does not give a torsion-free base
distinct_from:
  kms-minsky-groups-contain-no-z-localized: that excludes the groups G(M) themselves, using their exponent-p base; this shows the base exponent law is redundant for almost all generators, so the naive characteristic-0 variant, which drops only that law, keeps the whole machine in p-torsion.
  z-localized-embeds-in-fp-rf-group: that is the bottleneck; this is a calibration result for the proposed characteristic-0 variant of the KMS construction.
artifacts:
  - research/artifacts/gq-gq-infinite-primes-kms-reading.md
---

**ESTABLISHED** through `kms-configuration-letters-inherit-exponent-p-proof`. Lane proof, not
independently reviewed. It uses only the relations G1, G5 a), G5 c) and G7 of the KMS
presentation, as read from the arXiv:1204.6506v5 source.

**Setting.** Let `G^0(M)` be the group given by the KMS generators and relations G1–G8 of §4.1, except
that the law "`H_0` has exponent `p`" in G1 is omitted. `G^0(M)` still has these laws:
- `H_0 = <x_u>` abelian;
- `H_1 = <A_0,...,A_K>` abelian of exponent `p`;
- `H_2` abelian.

**Statement.** In `G^0(M)`, let `u in U` and `0 <= i <= K` with `A_i` not occurring in `u`. Then
`x_(uA_i)^p = 1`, and more precisely `x_u^(A_i^n) = x_u x_(uA_i)^n` for all `n >= 0`.
- So every configuration letter `x_v` whose word `v` contains some `A_i` has order dividing `p`.
  Only `x_(q_0), ..., x_(q_N)` can have infinite order.
- Every machine relation G8 is an equality between words in conjugates of the letters `x_(q_i A_0)`,
  each of order dividing `p`. KMS Lemma 4.5 shows that `T = <<x_u>>` is abelian, and its argument
  (G2, G5, G6, G7 and the Baumslag--Remeslennikov lemma) does not use the base exponent law; this was
  not re-derived here. Granting it, both sides of G8 have order dividing `p`, and the simulation of
  `M` takes place inside the `p`-torsion of `T`.

**Reading for the characteristic-0 program.** "Relations G1–G8 with the base declared
torsion-free" is not a consistent variant. The law that kills torsion-freeness is the exponent-`p`
law on `H_1` in G1, transported to the base by G5 a). A characteristic-0 variant must make the
A-letters torsion-free too. What happens then is recorded in §4 of the artifact:
- residual finiteness is plausibly not the obstruction;
- the Minsky relations give a base with no divisibility.

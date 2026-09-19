---
rg: 2
id: full-mf-radical-has-fp-cover-same-generators
kind: claim
title: Every finitely generated group with full MF radical is covered by a finitely presented one with the same property
distinct_from:
  full-mf-radical-finite-challenge-cylinder: that packages the presentation of the already finitely presented saturated group as a marked certificate; this produces a finite presentation for an arbitrary finitely generated group with full MF radical, which need not itself be finitely presented.
  fp-quotient-iff-kernel-finitely-normally-generated: that characterizes when a quotient of a finitely presented group stays finitely presented; this constructs a finitely presented cover and says nothing about which quotients of it are finitely presented.
  defect-saturation-full-mf-radical: that constructs one finitely presented example; this covers every example, including ones with no finite presentation.
artifacts:
  - research/artifacts/mf-radical-linear-certificate-2026-09-07.md
  - non_mf_groups_exist.tex
---

Let `G=<g_1,...,g_m>` be finitely generated with `Res_MF(G)=G`, and let
`r_1,...,r_s` be the relators of `full-mf-radical-linear-relator-inequality`.
Put

```text
P = <x_1,...,x_m | r_1,...,r_s>.
```

Then `P` is finitely presented on `m` generators, `P` surjects onto `G`, and

```text
Res_MF(P) = P.
```

The property transported to the cover is the one about every homomorphism to
an MF group, which is stronger than producing a finitely presented cover that
merely fails to be MF.  Applied to `H=EL_4(L_(F_2)(1,2))`, whose finite
presentability is not known, this gives a finitely presented group on the
same generating set with full MF radical.

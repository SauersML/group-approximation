---
rg: 2
id: kms-minsky-groups-contain-no-z-localized
kind: claim
title: Every torsion-free subgroup of a Kharlampovich-Myasnikov-Sapir Minsky-machine group G(M) is free abelian of finite rank, so none contains Z[1/q], Z_(l) or the Euler lamplighter G_l
distinct_from:
  z-localized-embeds-in-fp-rf-group: that asks for some finitely presented residually finite group containing Z_(l); this excludes the finitely presented residually finite groups of Kharlampovich-Myasnikov-Sapir as witnesses.
  fg-metabelian-groups-have-roots-at-finitely-many-primes: that excludes finitely generated metabelian hosts; the KMS groups are soluble of class 3 but torsion-by-abelian, which excludes them for a different reason.
  z-localized-embeds-in-fg-rf-soluble-group: that host G_l is abelian-by-metabelian with torsion-free base, the same shape as the KMS groups but with the exponent-p base replaced by a Z_(l)-module; this shows the KMS groups themselves cannot contain it.
artifacts:
  - research/artifacts/gq-gq-infinite-primes-kms-reading.md
---

**ESTABLISHED** through `kms-minsky-groups-contain-no-z-localized-proof`. Lane proof, not
independently reviewed. Elementary once the structure theorem is imported.

**Source.** O. Kharlampovich, A. Myasnikov, M. Sapir, *Algorithmically complex residually
finite groups*, arXiv:1204.6506v5. Read from the arXiv e-print source (KMS-322.tex) on
2026-09-18; theorem numbers are from its counters.
- For a Minsky machine `M` with `K` glasses and a prime `p`, §4.1 defines a finitely
  presented group `G(M)` with generators `x_u` (`u in U`), `A_0..A_K` and
  `a_i, a_i', ã_i, ã_i'` (`i = 1..K`), and relations G1–G8.
- **Theorem 4.3(a), verbatim:** "The group `G(M)` belongs to
  `𝒜_p^2 𝒜 ∩ 𝒵𝒩_(K+1) 𝒜`." Here `𝒜_p` is the variety of abelian groups of exponent `p`,
  and products of varieties are classes of extensions (§4, first paragraph).
- **Theorem 4.17:** if `M` is sym-universally halting, then `G(M)` is residually finite.
  Theorems 4.18 and 4.19 (4.19 is cited as 4.20 in the introduction) derive the
  finitely presented residually finite groups with large Dehn and depth functions from
  these `G(M)`.

**Statement.** Let `M` be a Minsky machine and `p` a prime. Every torsion-free subgroup
of `G(M)` is free abelian of finite rank. In particular, for every prime `q`, no group
`G(M)` contains `Z[1/q]`, and no group `G(M)` contains `Z_(l)`, any `Z[1/P]` with `P`
nonempty, `(Q,+)`, or the Euler lamplighter `G_l` of
`z-localized-embeds-in-fg-rf-soluble-group`.

**Reading for the bottleneck.** The Kharlampovich--Myasnikov--Sapir paper proves no
embedding theorem. Its §1.1.7 ("What next?") only poses the residually finite Higman
question, in its unrestricted form. Its finitely presented residually finite groups are
torsion-by-abelian, so they cannot witness `z-localized-embeds-in-fp-rf-group`.

Their proof of residual finiteness (Theorem 4.17) uses that the base
`T = <<x_u>>` has finite exponent `p`: "because `T` is an Abelian group of finite
exponent `p`". A variant with a torsion-free base, the shape `G_l` has, would need a new
residual-finiteness argument. See the artifact.

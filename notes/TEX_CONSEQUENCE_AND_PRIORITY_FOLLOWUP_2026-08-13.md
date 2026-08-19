# TeX consequence and priority follow-up — 2026-08-13

This note records the final origin-based follow-up to
`TEX_LITERATURE_AND_SHAPE_AUDIT_2026-08-13.md`. It is repository
documentation, not part of the manuscript.

## Current presentation status

- Verification links are compact margin annotations. The authoritative TeX
  has seven annotations, each adjacent to a statement with the same
  mathematical shape as its target declaration. No verification-status prose
  remains in the mathematical body.
- Group MF is defined primarily using the quotient of unitary sequences by
  the operator-norm-null normal subgroup. A polar-lifting lemma identifies
  that group canonically with the unitary group of the associated C-star
  corona. This keeps the group definition exact while retaining the analytic
  C-star formulation used in the proof.
- The increasing-dimension reduction uses an identity block followed by the
  current model. This increases the dimensions and leaves that model's
  multiplicative defects and distances from the identity unchanged.

## Primary-source checks

- Conder--Liversidge--Vsemirnov, *J. Algebra* 662 (2025), 123--137,
  DOI 10.1016/j.jalgebra.2024.08.008, records both the
  Conder--Robertson--Williams relation list and the manuscript's matrix
  labels. The manuscript separately proves the affine semidirect-product
  presentation by normal form.
- The freely available BHV text gives property (T) for
  `Z^3 semidirect SL_3(Z)` in Example 1.7.4(i), via Corollary 1.4.16 and
  Theorem 1.7.1.
- Shulman's arXiv:2603.13564 introduction states both that MF of either the
  full or reduced group C-star algebra implies group MF and that, in March
  2026, no group was known whose full or reduced group C-star algebra was not
  MF. Bachner--Dogon--Lubotzky's publisher abstract calls the all-groups-MF
  problem longstanding.
- Kun--Thom arXiv:2608.06222 describes the OpenAI example as the first
  nonsofic group. Fournier-Facio arXiv:2608.02025, Theorem 1.3, states the
  existence of a finitely presented torsion-free nonsofic group.
- Chatterji--Kassabov arXiv:2601.22907, Theorem 3, has exactly the embedding,
  finite-presentation, property-(T), and normal-generation hypotheses used by
  the Kazhdan-envelope consequences.
- Goryushkin's primary abstract states that every countable group embeds in a
  two-generator simple group.

## Consequence audit

- Korchagin, Propositions 5 and 7, gives the uniform local MF criterion with
  separation constant sqrt(2). The manuscript's constant 1 is a valid
  weakening, and the finite marked-ball pullback proves closedness of the MF
  locus. The literal bounds are 16 for `w`, 32 for `w^2`, and 34 for
  `[w,g]`.
- The Adian--Rabin applications use the effective construction in the needed
  direction: a trivial group for a trivial test word, and a group containing
  the forbidden finitely presented witness otherwise. This proves both
  undecidability and non-recursive-enumerability of negative instances. The
  four group-C-star variants inherit the argument because full and reduced
  group C-star inclusions induced by subgroup inclusions are injective, while
  MF, finiteness, and stable finiteness pass to unital subalgebras.
- The authoritative manuscript currently contains neither the proposed
  free-product simple/exact/unique-trace consequences nor a universal-Horn
  theorem. Those claims therefore must not be described as manuscript results
  unless they are added and separately checked.

## Priority-language repair

Absolute phrases asserting that a mechanism was new or was not an adaptation
of prior work were replaced by objective descriptions of the proved mechanism
and verifiable structural comparisons. This preserves the mathematical claim
without asserting priority beyond the source record.

## Access limits

The original CRW article and some publisher-hosted books remained blocked to
non-browser clients during this pass. The accessible CLV paper supplies the
needed matrix-labelled CRW presentation. BHV was checked from its freely
available full text. Chatterji--Kassabov is publicly available only as arXiv
version 1, submitted January 30, 2026.

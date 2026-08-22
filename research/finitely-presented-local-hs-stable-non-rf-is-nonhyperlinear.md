---
rg: 2
id: finitely-presented-local-hs-stable-non-rf-is-nonhyperlinear
kind: claim
title: Finite presentation upgrades local HS stability, so a non-RF example would already be nonhyperlinear
artifacts:
  - research/artifacts/normalized-hs-stable-non-rf-literature-boundary-2026-08-21.md
distinct_from:
  hyperlinear-hs-stable-is-residually-finite: that starts with global same-dimension HS stability; this imports the primary local-to-global theorem, including flexible variants, and eliminates the published non-RF locally stable examples from the finitely presented search.
  finitely-presented-hs-stable-nontrivial-fd-residual: that asks for an explicit global stable witness; this proves that a locally stable witness would be equivalent once finite presentation is verified.
  infinite-hyperlinear-kazhdan-group-is-not-hs-stable: that is a property-T obstruction to stability; this criterion has no Kazhdan assumption and uses only non-residual finiteness.
---

Let `Gamma` be finitely presented and locally stable for finite-dimensional
unitary groups in normalized Hilbert--Schmidt norm.  Then `Gamma` is globally
HS-stable.  The same implication holds for the flexible and very flexible
versions.

This is exactly Fournier-Facio--Gerasimova--Spaas,
arXiv:2307.13155v2, Lemma 3.11.  Their theorem is stated for every sequence
of metric groups: finite presentation turns every partial homomorphism into
a sequence of genuine homomorphisms, so local and global stability coincide.

Consequently,

```text
Gamma finitely presented,
Gamma locally (flexibly) normalized-HS stable,
Gamma not residually finite
        ==> Gamma not hyperlinear.                         (LNR1)
```

Indeed local stability first upgrades to global stability.  If `Gamma` were
hyperlinear, correction of canonical microstates would make its
finite-dimensional unitary representations separate points.  Malcev residual
finiteness of finitely generated linear groups would then make `Gamma`
residually finite, contradicting the third hypothesis.  Equivalently, apply
`hyperlinear-hs-stable-is-residually-finite` after the local-to-global upgrade.

This closes a possible loophole in the published-example search.  The same
paper constructs non-residually-finite groups which are locally HS-stable but
not HS-stable.  Lemma 3.11 implies immediately that none of those examples is
finitely presented.  Their local stability cannot be combined with a finite
presentation taken from another construction: any such combination would
already be the desired nonhyperlinear theorem `(LNR1)`.

The other current normalized-HS-stable families do not meet the algebraic
side.  The lamplighter group in Dogon--Vidick, arXiv:2607.20135v1, is
residually finite and infinitely presented.  Spaas's chordal graph products
of abelian groups, arXiv:2603.02058v1, are residually finite in the finitely
generated cases relevant here.  The non-residually-finite stable groups of
De Chiffre--Glebsky--Lubotzky--Thom, arXiv:1711.10238, are stable for the
unnormalized Frobenius norm, whose correction theorem does not apply to
normalized-HS microstates.

Thus the immediate criterion is rigorous but presently conditional.  The
sharp missing published hypothesis is now either:

1. finite presentation of a non-RF **locally** normalized-HS-stable group
   (which automatically upgrades to global stability); or
2. a marked/canonical-microstate correction theorem for one known
   finite-dimensionally invisible word.

No checked primary theorem supplies either item.

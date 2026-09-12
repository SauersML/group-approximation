# Thom, arXiv:0810.2180 — source-verified statement record

Andreas Thom, *Examples of hyperlinear groups without factorization
property*, arXiv:0810.2180 (Groups Geom. Dyn. 4 (2010)).

Provenance: the PDF was fetched on **2026-08-14** from
`https://export.arxiv.org/pdf/0810.2180` (the `arxiv.org/pdf/...` route
returns an HTML interstitial, not the PDF) and read with `pdftotext`, not
from an HTML render.  Quotations below are verbatim from that extraction,
with mathematical notation transliterated where the extraction mangles it.

**Numbering correction.**  The statements are **Lemma 3.3** and **Remark
3.4**, as `notes/PERFECT_CORE_KUN_THOM_WREATH.md` already records.  A
circulating reference to "Lemma 3.4 / Remark 3.5" is off by one.

## Abstract (verbatim)

> In this note we give an example of a group which is locally embeddable into
> finite groups (in particular it is initially subamenable, sofic and hence
> hyperlinear) but does not have Kirchberg's factorization property. This
> group provides also an example of a sofic Kazhdan group which is not
> residually finite, answering a question of Elek and Szabo. We also give an
> example of a group which is not initially subamenable but hyperlinear.
> Finally, we point out a mistake in an assertion of Kirchberg and provide an
> example of a group which does not have the factorization property and is
> still a subgroup of a connected finite-dimensional Lie group.

## Lemma 3.3 (verbatim)

> **Lemma 3.3.** Let G be a group and let C be a central subgroup. The group
> G is hyperlinear if and only if the twisted group von Neumann algebra
> L_{beta o alpha}[G/C] embeds into R^omega for every character beta in
> hat(C).

Here `alpha` is the 2-cocycle on `G/C` classifying the central extension
`0 -> C -> G -> G/C -> 0`, obtained from a set-theoretic lift, and
`L_{beta o alpha}[G/C]` is the corresponding twisted group von Neumann
algebra.  The proof identifies `LG` with the field of algebras
`L_{beta o alpha}[G/C]` over the compact base `hat(C)` with Haar measure, so
that embeddability of `LG` is equivalent to embeddability for almost every
`beta`, and then upgrades "almost every" to "every" by showing the good set
is both dense and closed.

Note the proof text also uses, as standard, the identification
"`LG` is embeddable into `R^omega` (i.e. `G` is hyperlinear)".

## Remark 3.4 (verbatim)

> **Remark 3.4.** The proof yields that every quotient of a hyperlinear group
> by a central subgroup is again hyperlinear. Note however, that a central
> quotient of a group with factorization property does not necessarily has
> Kirchberg's factorization property, as the example above shows.

## Instantiation used in this repository

With `G=Wtilde=C(X) semidirect G_0` the Clifford lamp group over
`X=G_0/Gamma` and `C=<z> = Z/2`, the dual `hat(C)` has exactly two points and
the two twisted corners are

```text
beta=1:   L(W)=L^infinity({-1,1}^X) crossed_product G_0,
beta=sgn: Cl(X) crossed_product G_0.
```

So Lemma 3.3 reads: `Wtilde` is hyperlinear iff **both** crossed products are
Connes embeddable — the same statement the repository proves directly in
`notes/TRUE_CLIFFORD_LAMP_CENTRAL_SUMMANDS.md` by cutting with
`p_(+-)=(1+-z)/2`.  Remark 3.4 supplies the descent step
`Wtilde hyperlinear ==> W=Wtilde/<z> hyperlinear`, which with the Kun--Thom
nonsoficity of `W` closes Question 3.4.

**Trust surface.** Published, refereed, sixteen years old, and used here only
at statement level.  This is a materially lower risk than the 2026 preprints
this graph also depends on.

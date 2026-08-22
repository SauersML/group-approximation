---
rg: 2
id: atlas-rank-stability-literature-fence
kind: claim
title: Published rank stability corrects finite Atlas charts but not their amalgams or thirteen fillings
distinct_from:
  atlas-augmented-rank-zero-set-compactness: that states the exact rank-ultraproduct-to-finite-zero theorem needed by the augmented Atlas system; this audits primary stability theorems and proves that none of their hypotheses supplies it.
  atlas-augmented-thirteen-vf-fillings: that constructs the virtually free carrier and its thirteen explicit filling relators; this separates which pieces of that decomposition are covered by published rank-stability permanence.
  atlas-a4-packet-hs-regular-cores: that corrects the two finite chart factors in normalized Hilbert--Schmidt norm; this concerns flexible normalized-rank correction over `F_2` and the missing joint amalgam/filling step.
---

The primary normalized-rank literature gives the following exact boundary for
the augmented Atlas system.

## What is available

Bauer--Blachar--Greenfeld, *Rank-stability of polynomial equations*, IMRN
2025, rnaf173, arXiv:2401.04676v2, use normalized matrix rank over an
arbitrary field `F`.  Their Definition 1.1 is **flexible**: an approximate
`n`-dimensional tuple may be corrected to an exact `n'`-dimensional tuple,
with the zero-padded matrices differing by rank `o(n)`.  The relevant
theorems are:

1. Theorem 5.1: every finite-dimensional associative `F`-algebra is
   rank-stable.
2. Theorem 6.2: for a finitely presented group `G`, group rank stability over
   `F` is equivalent to rank stability of `F[G]`.
3. Proposition 7.1: for finitely presented algebras having finite-dimensional
   representations, the ordinary unital free product `A*A'` is rank-stable
   exactly when both factors are rank-stable.
4. Theorem 7.2 and Theorem 7.7 cover direct products and matrix rings.

These statements apply in characteristic two.  In particular every finite
Atlas vertex algebra `F_2[K]` is rank-stable, even when `2` divides `|K|`;
Theorem 5.1 assumes finite dimension, not semisimplicity.  Proposition 7.1
also makes

```text
F_2[A8]*F_2[A8]                                         (RLA1)
```

rank-stable.  Thus separate finite-chart correction and the completely free
two-chart product are rigorously available.

## The two missing permanence operations

The same paper contains no theorem for an amalgamated free product

```text
A *_C B                                                   (RLA2)
```

over a nontrivial finite-dimensional algebra `C`, no graph-of-algebras
theorem, and no HNN theorem.  Proposition 7.1 cannot be applied to `(RLA2)`:
its proof independently changes the two correction dimensions using their
representation-dimension semigroups.  An amalgam additionally requires the
two corrected restrictions to `C` to be conjugate with identical modular
multiplicities.  This synchronization is absent from its hypotheses and
conclusion.

Therefore Theorem 5.1 does not correct the Atlas virtually free carrier
`Pi`, which is a graph of finite groups with nontrivial finite edge groups.
It only corrects each vertex packet separately.  Even a future rank-stability
theorem for `Pi` would leave the second operation:

```text
Gamma_+ = Pi / <<r_1,...,r_13>>,                         (RLA3)
```

where the twelve stable-letter fillings and collision are Tietze-irredundant
by `atlas-thirteen-vf-fillings-are-tietze-irredundant`.

No quotient-by-finitely-many-relators permanence theorem appears in the
audited source.  Nor can one be inferred formally from presentation
invariance: the free algebra is rank-stable, while Bauer--Blachar--Greenfeld
Example 2.3 gives the one-relator quotient

```text
F<x,y>/<xy-yx-1>                                         (RLA4)
```

as non-rank-stable.  Thus finite polynomial filling is not a valid general
closure operation, even though `(RLA4)` is an algebra rather than a group
filling.

## Why the other virtually-free theorems do not transfer

Gerasimova--Shchepin, *Virtually free groups are p-Schatten stable*,
arXiv:2107.10032, prove stability for normalized Schatten norms on complex
unitaries, for `1<=p<infinity`.  Normalized rank over `F_2` is neither one of
those metrics nor controlled by small Schatten defect.

Fournier-Facio, *Ultrametric analogues of Ulam stability of groups*,
arXiv:2105.00516, proves virtually free stability for congruence/profinite
ultrametrics on groups such as `GL_n(Z_p)`.  The paper explicitly states that
the rank metric is not ultrametric and places an analogue in Question 9.16.
Its virtually-free theorem therefore does not apply to normalized rank on
`GL_n(F_2)`.

Mallahi-Karai--Mohammadi Yekta, *Optimal linear sofic approximations of
countable groups*, arXiv:2112.10111, Proposition 6.1, corrects approximate
multiplication tables of one finite group in normalized rank over `C`.  It
does not state finite-edge amalgam synchronization or relator-filling
permanence, and its field is not the binary Atlas setting.  The stronger
arbitrary-field finite-algebra theorem above already supplies exactly the
local part it could contribute.

## Consequence for the augmented Atlas endpoint

None of these theorems implies
`atlas-augmented-rank-zero-set-compactness`.  To apply
Bauer--Blachar--Greenfeld directly one would have to prove rank stability of
the full finitely presented algebra/group algebra of `Gamma_+`; finite
dimensionality of the local chart algebras and virtual freeness of the
pre-filling carrier do not establish that hypothesis.

The precise missing literature bridge is therefore one of:

```text
(a) flexible normalized-rank stability of finite graphs of finite groups
    over arbitrary fields, including modular edge algebras, together with
    stability under these thirteen specific fillings; or

(b) a bespoke lifting theorem for the faithful-chart face of E_+ which
    synchronizes all finite-edge restriction multiplicities and preserves
    the marked collision rank.                            (RLA5)
```

Claiming either from existing virtually-free stability conflates metrics or
omits a permanence hypothesis.

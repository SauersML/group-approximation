---
rg: 2
id: ha2-actions-give-fp2-twisted-brin-thompson-groups-citation
kind: route
title: Import the [HA_2] finiteness corollary and relative simplicity of abstract twisted Brin–Thompson groups
target: ha2-actions-give-fp2-twisted-brin-thompson-groups
requires: []
---

Citation import, not a reproof. Source: F. Fournier-Facio, X. Wu and
M. C. B. Zaremsky, *Abstract twisted Brin–Thompson groups*, arXiv:2603.24687v2
(2 Apr 2026). Read on 2026-09-13 from the arXiv HTML through four fetches. The
definition, Corollary 4.14, Proposition 4.12, Theorem 3.6, Lemma 4.3 and Remark
4.16 were returned as quotations; one earlier fetch only summarized the
definition, and its summary agrees.

Verbatim:

1. Definition (before Corollary 4.14): "Say that G↷S is of type [HA_n] if G is
   of type FP_n, all point stabilizers are finitely generated, and there are
   finitely many orbits of pairs." Pairs are orbits of the diagonal action on
   `S × S` (Definition 1.3(iii)).
2. "Corollary 4.14. If G↷S is of type [HA_2] then SV_G is of type FP_2."
3. "Proposition 4.12. Suppose G is finitely generated, and that G↷S has finitely
   many orbits of pairs and finitely generated point stabilizers. Then SV_G is
   isomorphic to a group of the form P/N, where P is a free product of finitely
   many groups each commensurable to a direct product of finitely many copies of
   G, and N is finitely normally generated."
4. "Theorem 3.6. The abstract twisted Brin–Thompson group SV_G is relatively
   simple, with largest normal subgroup the canonical kernel SK_G." Its proof
   uses "the simple group SV_G/SK_G = SV_{G/K}" from Belk–Zaremsky [BZ22]
   (*Twisted Brin–Thompson groups*, Geom. Topol. 26 (2022), arXiv:2001.04579).
5. Lemma 4.3 defines "ι_∅: G → SV_G send g to [·,id,g,·]", and Proposition 4.17
   says G embeds in SV_G via ι_∅.
6. "Remark 4.16. It would be interesting to try and use Corollary 4.14 to
   approach Boone–Higman-type questions regarding type FP_2. For example, does
   there exist a type FP_2 simple group with unsolvable word problem?
   (Equivalently a type FP_2 simple group that is not recursively presented?)
   Do there exist uncountably many type FP_2 simple groups?"

Verification level: fetched statements, not a line-by-line read of the PDF. The
repository node `abstract-btb-pairs-fp-and-relatively-simple` read the same
paper and cites the embedding as Lemma 5.2 and relative simplicity as Theorem
3.6; the lemma numbering differs between the two readings, and the statements
agree.

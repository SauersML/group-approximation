---
rg: 2
id: deligne-universal-cover-lattice-is-non-rf-kazhdan-citation
kind: route
title: Import property (T) of the universal-cover lattice from Bekka--de la Harpe--Valette and its failure of residual finiteness from Deligne
target: deligne-universal-cover-lattice-is-non-rf-kazhdan
requires: []
---

Citation import. Read on MSI on 2026-09-12 from the PDFs, converted with
ghostscript `txtwrite` in `/scratch.global/sauer354/bh-rn/`.

* **Items 1-3.** B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*,
  New Mathematical Monographs 11, Cambridge University Press 2008, read from
  the author PDF `KazhdanTotal.pdf` at perso.univ-rennes1.fr/bachir.bekka.
  - **Section 1.7, the remark after Theorem 1.7.11, item (ii):** "The
    fundamental group of G = Sp2n(R) is isomorphic to Z; hence the universal
    covering G~ is perfect ..., with centre isomorphic to Z and therefore
    non-compact. For n >= 2, Theorem 1.7.11 implies that G~ has Property (T)."
  - **The same remark, item (iii):** "Gamma = Sp2n(Z) is known to be a lattice
    in G = Sp2n(R). The inverse image Gamma~ of Gamma in G~ is a lattice
    containing the centre of G~. Hence, Gamma~ has an infinite centre and has
    Property (T) for n >= 2."
  - **Proof of Theorem 3.5.4:** "Z = pi_1(G) ... can be viewed as a discrete
    central subgroup of G~, and G~/Z is isomorphic to G."
  - **Introduction, footnote 6:** "it is classical that arithmetic lattices are
    finitely generated, indeed finitely presented".
* **Item 4.** A. Dogon, *Flexible Hilbert-Schmidt stability versus
  hyperlinearity for property (T) groups*, Math. Z. (2023),
  arXiv:2211.10492v3, the paragraph after Corollary 1.9.
  - For `G = Sp_2g(R)`, `g >= 2`, and `Gamma = Sp_2g(Z)`: "As pi_1(Sp2g(R)) = Z,
    we get a central extension of the form 1 -> Z -> Gamma~ -> Sp2g(Z) -> 1,
    where Gamma~ is a lattice in the universal cover Sp2g(R)~. The group Gamma~
    has been shown to be non-residually finite by Deligne [16]."
  - Reference [16] there is P. Deligne, *Extensions centrales non résiduellement
    finies de groupes arithmétiques*, C. R. Acad. Sci. Paris Sér. A-B 287
    (1978), no. 4, A203--A208. Deligne's note itself was not read. Item 4 is
    used as Dogon states it, which is also how
    `dogon-sp2g-corollary-citation` uses it.

Used at statement level. Not reproved here.

---
rg: 2
id: bestvina-brady-kernel-finiteness-theorem
kind: claim
title: The Bestvina--Brady kernel of a right-angled Artin group is of type F_n iff the flag complex is (n-1)-connected, and of type FP_n(R) iff it is (n-1)-acyclic over R
---

Let `L` be a finite flag complex and `BB_L` the kernel of the homomorphism `A_L → Z` sending every
generator to `1`. For `n ≥ 1`:

1. `BB_L` is of type `F_n` iff `L` is `(n−1)`-connected;
2. for a commutative ring `R`, `BB_L` is of type `FP_n(R)` iff `L` is `(n−1)`-acyclic over `R`.

Source: M. Bestvina and N. Brady, *Morse theory and finiteness properties of groups*, Invent.
Math. 129 (1997), 445--470, doi:10.1007/s002220050168 (bibliographic data checked through
Crossref on 2026-09-13). The statement above is recalled from the paper; its exact form and
theorem number have not yet been re-read from the source.

## Attempts

- 2026-09-13, lane z1-19-raag-kernel: citation import pending. The publisher page was reached
  from MSI, but the PDF text was not yet extracted. The `-citation` route lands only after the
  Main Theorem is read verbatim. Until then this claim is open, so routes that use it do not
  fire. Only the "if" directions are needed for Zaremsky's Problem 1.19; the case `n = 1` of
  (1) is proved directly in `raag-virtual-fg-kernel-implies-fg-kernel-proof`.

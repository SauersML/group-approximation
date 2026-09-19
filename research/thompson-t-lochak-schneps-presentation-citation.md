---
rg: 2
id: thompson-t-lochak-schneps-presentation-citation
kind: route
title: Import the Lochak--Schneps presentation of T from Funar--Kapoudjian Sec. 2.1 and check its relators in an exact PL model
target: thompson-t-lochak-schneps-presentation
requires: []
artifacts:
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/pl_circle.py
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/verify_ls.py
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/find_words.py
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/out_verify_ls.json
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/out_find_words.json
---

## Citation

The source is L. Funar and C. Kapoudjian, *The braided Ptolemy-Thompson group T^* is asynchronously
combable*, arXiv:math/0602490, Sec. 2.1, p. 6. The PDF was fetched on 2026-09-19 and converted to text with
`pypdf`. Verbatim, with the extracted superscripts restored:

> Lochak and Schneps ([27]) proved that the group T has the following presentation with generators α and β
> and relations
> α^4 = β^3 = 1
> [βαβ, α^2βαβα^2] = 1
> [βαβ, α^2β^2α^2βαβα^2βα^2] = 1
> (βα)^5 = 1

Their reference [27] is P. Lochak and L. Schneps, *On universal Ptolemy-Teichmuller groupoid*, in Geometric
Galois Theory, L.M.S. Lecture Notes Ser. 243, Cambridge Univ. Press, 1997. It was **not** read. The
attribution is Funar--Kapoudjian's.

Their Remark 2.1 (`A = βα^2, B = β^2α, C = β^2` give the CFP generators) depends on a composition convention
that the text does not fix. In our model and convention, `B` comes out as `βαβ` instead. The dictionary is
not used anywhere downstream.

## Independent check (the direction "these relators hold in T")

All scripts are in `experiments/thompson-t-opnorm-defect-gap-2026-09-17/`.

- **The circle maps.** `pl_circle.py` implements dyadic PL circle maps with exact `Fraction` arithmetic.
- **The relators.** `verify_ls.py` evaluates the five relators on
  `(alpha, beta) = (rot(1/4), C_cfp^(-1))` and on the variants `rot(3/4)` and `C_cfp`, under both reading
  conventions. Here `C_cfp` is the CFP order-3 generator.
  - It exits 0 because every relator is the identity for `(rot(1/4), C_cfp^(-1))`, in both conventions.
  - It also holds for `(rot(3/4), C_cfp)`.
  - Output: `out_verify_ls.json`.
- **Generation.** `find_words.py` runs a breadth-first search over positive words and finds `A = baa`,
  `B = bab`, `C = bb`, reading the leftmost letter first. Each identity is asserted exactly. Output:
  `out_find_words.json`.

So `alpha, beta` generate `T` (`A, B, C` generate `T`: Cannon--Floyd--Parry 1996, Sec. 5), and the displayed relators hold in `T`.
Completeness of the relator list, meaning that the normal closure of the relators is the whole kernel of
`Z/4 * Z/3 -> T`, is the one imported fact.

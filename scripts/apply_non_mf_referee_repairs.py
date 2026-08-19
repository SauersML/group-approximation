#!/usr/bin/env python3
from pathlib import Path

p = Path("non_mf_groups_exist.tex")
s = p.read_text()
old = r'''The same decomposition also proves that $E$ is exact.  The quotient
$C(\mathcal G)/\langle\zeta\rangle$ is the free product of the
elementary abelian $2$-groups attached to the blocks, each of order at
most $2^{8}$.  Every finite sub-free-product is exact by Dykema's
free-product theorem \cite{DykemaExact}; the full free product is the
increasing union of these finite sub-free-products, so it is exact by
the increasing-union permanence theorem of Kirchberg--Wassermann
\cite{KWExact}.  Since $\langle\zeta\rangle$ is finite, extension
permanence \cite{KWPermanence} then gives exactness of
$C(\mathcal G)$.'''
new = r'''The same decomposition also proves that $E$ is exact.  The quotient
$C(\mathcal G)/\langle\zeta\rangle$ is the free product of the
elementary abelian $2$-groups attached to the blocks, each of order at
most $2^{8}$.  Dykema's theorem applies to free products of arbitrary
families of exact discrete groups, so this quotient is exact
\cite{DykemaExact}.  Since $\langle\zeta\rangle$ is finite, extension
permanence \cite{KWPermanence} then gives exactness of
$C(\mathcal G)$.'''
count = s.count(old)
if count != 1:
    raise SystemExit(f"expected one exactness paragraph target, found {count}")
p.write_text(s.replace(old, new, 1))

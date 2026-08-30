---
rg: 2
title: STW XC strict-comparison group frontier audit (2026-08-30)
kind: artifact
---

# Current status

STW Problem XC asks whether `C*_r(G)` has strict comparison by its canonical
trace for every countable discrete C*-simple group `G`.  A primary-source
search through 30 August 2026 found no universal solution.  Vigdorovich,
arXiv:2602.10616v3 (18 June 2026), explicitly describes the converse from
simplicity to selflessness as open; selflessness would imply the desired
strict comparison.  The July 2026 correspondence paper listed below gives
new broad product classes but does not assert XC in general.

# Primary-source advances after the STW addendum

- Amrutam--Gao--Kunnawalkam Elayavalli--Patchell,
  arXiv:2412.06031 / *Inventiones Mathematicae* 242 (2025), prove strict
  comparison and selflessness for free groups and a rapid-decay
  acylindrically hyperbolic class.
- Raum--Thiel--Vilalta, arXiv:2505.18569, extend the rapid-decay method to
  twisted group algebras and finite-radical cases.
- Ozawa, arXiv:2508.07938, proves complete selflessness from PHP, removes
  rapid decay for acylindrically hyperbolic groups with trivial finite
  radical, and proves exact tensor-product permanence.
- Flores--Klisse--O Cobhthaigh--Pagliero, arXiv:2601.19758, prove pureness and
  stable rank one for further twisted finite-by-PHP extensions.
- Vigdorovich, arXiv:2602.10616v3, proves selflessness for all nontrivial
  linear groups with trivial amenable radical, settling XC for linear
  C*-simple groups.
- Gao--Junge--Kunnawalkam Elayavalli--Patchell--Robert,
  arXiv:2607.20361, prove that tensoring a completely selfless trace with the
  unique trace of any simple algebra preserves selflessness, without
  exactness of the second algebra.

# New unconditional reduction

`directed-unions-preserve-tracial-strict-comparison` proves directly that a
compatible directed union of strictly comparing tracial C*-algebras again
has strict comparison.  The proof moves a strict dimension gap to one stage
using the three cutdowns `(a_i-gamma)_+`, `(b_i-2gamma)_+`, and
`(b-3gamma)_+`; it does not assume selflessness or invoke abstract Cu
continuity.  The group specialization
`stw90-directed-unions-of-strict-comparison-groups` checks reduced-norm and
trace compatibility and proves simplicity when all subgroup stages are
C*-simple.

Since every group is the directed union of its finitely generated subgroups,
the contrapositive says that failure of canonical strict comparison always
reflects to a finitely generated subgroup.  The reflecting subgroup need not
be C*-simple, so this is a finite-localization theorem rather than a reduction
of XC to finitely generated C*-simple groups.

An explicit application not of tensor-product form is
`SL_infinity(Z)=union_m SL_{2m+1}(Z)`.  Vigdorovich settles every odd-rank
stage and Robert's directed-union theorem makes the stable reduced algebra
selfless.  Exactness passes from the linear stages through their reduced
C*-algebra inductive limit.  The stable group contains `direct_sum_N F_2`,
proving nonlinearity over every field, while complementary finite-support
blocks make every element centralizer non-virtually-cyclic, excluding
acylindrical hyperbolicity.  Thus it is a concrete exact XC case outside
those two established group classes.

# Products, exactness, and obstruction boundary

The 2026 complete-selflessness tensor theorem and Ozawa's PHP theorem imply
that `P x H` has selfless reduced algebra, hence strict comparison, whenever
`P` has PHP and `H` is C*-simple.  This includes `F_2 x H` for every
C*-simple `H`, with no exactness assumption on `H`.  It does not descend
strict comparison from the product to `H`: applying the trace slice to a
Cuntz comparison in the tensor product produces a finite row comparison, not
a single Cuntz implementer in `C*_r(H)`.

The earlier example `direct_sum_N F_2` is nonlinear and not
acylindrically hyperbolic, but it is not a literature-new XC case: Ozawa's
countable exact tensor-product theorem already covers its reduced algebra.

`stw91-finite-subgroup-projection-obstruction` has been strengthened to start
from strict comparison itself.  For finite `H,K<=G` with `|H|>|K|`, strict
comparison forces `e_H <=_Cu e_K` and
`[e_K]-[e_H] in K_0(C*_r(G))_+`.  A C*-simple violation would refute both XC
and XCI; no violating group is produced here.  Exactness alone removes an
extra-quasitrace obstruction but does not supply strict comparison.

# Trust boundary

Literature inputs are isolated in citation nodes: Ozawa's PHP results,
Robert's selflessness regularity, and the 2026 cp-map tensor theorem.  The
directed-union comparison proof, group-algebra specialization, simplicity
argument, and ordered-`K_0` calculation are supplied directly.  No converse
from regularity to selflessness, tensor-to-factor descent, or universal XC
solution is asserted.

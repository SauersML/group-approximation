---
rg: 2
title: STW XCI selfless group-algebra frontier audit (2026-08-30)
kind: artifact
---

# Status and definition audit

STW Problem XCI asks whether `C*_r(G)` is selfless for every countable
discrete C*-simple group `G`.  The free-group question in the first sentence
is solved, but the universal question remains open as of 30 August 2026.

The source definition in Robert, arXiv:2309.14188v3, Definition 2.1, is that
the first-factor map `(A,rho) -> (A,rho)*(A,rho)` is existential.  The
ultrapower characterization has a splitting embedding from the reduced free
product **into** `A^omega`, fixing the diagonal copy of `A`.  The previous
XCI root had this arrow reversed; it has been corrected.  Robert's Theorem
2.6 gives equivalent formulations using a free Haar unitary or the infinite
reduced free product.

# Primary-source literature audit

- Amrutam--Gao--Kunnawalkam Elayavalli--Patchell,
  arXiv:2412.06031 / *Inventiones Mathematicae* 242 (2025), prove the
  free-group case and an acylindrically hyperbolic rapid-decay class.
- Ozawa, arXiv:2508.07938, proves that a topologically-free extreme boundary
  implies selflessness and that the PHP property implies complete
  selflessness.  PHP contains acylindrically hyperbolic groups with trivial
  finite radical and is closed under finite direct products.
- Vigdorovich, arXiv:2602.10616v3 (18 June 2026), proves selflessness for
  every nontrivial linear group with trivial amenable radical; for linear
  groups this identifies C*-simplicity with selflessness.
- Gao--Junge--Kunnawalkam Elayavalli--Patchell--Robert,
  arXiv:2607.20361 (22 July 2026), develop relative selflessness and new
  tensor-product and crossed-product permanence theorems.  Their introduction
  still presents named sufficient group classes rather than a theorem for all
  C*-simple groups.

The audit used these primary arXiv records and source TeX, together with STW
v2 (`tmp/pdfs/stw99.txt`, lines 3890--4115).  Searches for a theorem covering
all C*-simple groups found none.  The conclusion that the universal question
remains open is a literature-status conclusion, not a mathematical theorem.

# New unconditional progress

The group-algebra specialization of Robert's directed-union theorem is
formalized in `stw91-directed-unions-of-selfless-groups`.  The reduced norm
and trace compatibility are checked directly.  Applying it after Ozawa's
finite-product PHP permanence proves that

```text
direct_sum_N F_2
```

has selfless, hence simple, reduced C*-algebra.  A finite-dimensional algebra
chain proves this group is nonlinear over every field; a centralizer argument
proves it is not acylindrically hyperbolic.  This is a concrete positive case
beyond those two group-theoretic regimes, but not a literature-new example:
Ozawa's countable tensor-product theorem independently covers its reduced
algebra as the infinite tensor product of copies of `C*_r(F_2)`.

For a possible negative solution, `stw91-finite-subgroup-projection-obstruction`
turns selfless strict comparison into a check on the averaging projections
of finite subgroups and then into an ordered-`K_0` certificate.  No group
violating the certificate is produced here.  Separately,
`stw91-exact-cstar-simple-groups-have-unique-quasitrace` shows that extra
quasitraces cannot detect an exact counterexample.

There is also a new permanence class beyond the PHP-specific Cantor example.
If `C*_r(P)` is exact and selfless and `X` is any nonempty compact metrizable
zero-dimensional space, then the locally constant step-function group
`LC(X,P)` has exact selfless reduced algebra.  Enumerating the countable
Boolean algebra of clopen subsets exhausts this group by finite powers
`P^(|Q_n|)`.  Exact tensor permanence makes each power selfless, and Robert's
directed-union theorem handles the limit.  This assumes neither PHP nor
linearity of `P`; it is a permanence result conditional only on the base
algebra already belonging to the exact positive class for XCI.

There is a second permanence theorem which is independent of exact tensoring
and directed limits.  If `(A,tau)` and `(B,sigma)` are selfless, put their two
free-product splittings in a common Fubini ultrapower.  The coordinate copies
`A^Omega` and `B^Omega` inside `(A*B)^Omega` remain free: alternating centered
ultrapower representatives can be centered coordinatewise, after which every
coordinate trace is zero.  The two free copies inside `A^Omega` and the two
inside `B^Omega` are therefore four jointly free copies.  Regrouping them
gives a trace-preserving map

```text
(A*B)*(A*B) -> (A*B)^Omega
```

whose first-factor restriction is diagonal.  The reduced-free-product trace
is faithful, so this map is injective.  The arrow is thus in the precise
free-product-to-ultrapower direction required by selflessness.  Consequently
reduced free products preserve selflessness, and
`C*_r(G*H)` is selfless whenever both factor reduced group algebras are.
No exactness, PHP, linearity, or rapid-decay assumption enters this argument.

The free- and tensor-product mechanisms can be interleaved along any
cograph.  Let `Gamma` be nonempty, countable, and `P_4`-free, with exact selfless vertex
groups.  Every finite induced subgraph has a recursive decomposition by
disjoint unions and joins.  These become group free products and direct
products; reduced-free-product permanence handles the former, while exact
ordinary-selfless tensor permanence handles the latter.  Exactness survives
both operations, so the induction can alternate them without losing its
hypothesis.  The full countable graph product is the directed union of its
finite induced graph products and is therefore selfless.  This gives
`stw91-cograph-products-preserve-selflessness`.

The cograph condition marks the present boundary.  Removing a vertex from a
general graph product produces an amalgamated product over its link subgroup,
and no amalgamated selflessness theorem follows from the ordinary free-product
splitting.  No such extension is asserted.

# Trust boundary

Imported results are explicitly isolated: Robert's directed-union and
regularity theorems; Ozawa's PHP theorem, finite-product permanence, and
acylindrically hyperbolic examples; Vigdorovich's linear-group theorem;
Haagerup's theorem on quasitraces of exact C*-algebras; the unique-trace
theorem for C*-simple groups; and the virtually-cyclic-centralizer theorem
for loxodromic elements in acylindrical actions.  Reduced-norm functoriality
for subgroup inclusions, the nonlinear algebra-chain argument, and the
finite-subgroup ordered-`K_0` calculation are given directly in their routes.

Nothing here proves the universal XCI assertion or supplies a counterexample.

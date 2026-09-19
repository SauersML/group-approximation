---
rg: 2
id: twin-lattices-exclude-known-llp-fences
kind: claim
title: Twin building lattices, acting on complete CAT(0) twin buildings, normalize no distorted free abelian subgroup, so the cohomological and expander LLP-failure families are excluded as subgroups
distinct_from:
  simple-kazhdan-kac-moody-lattices-exist: that imports the existence of the simple Kazhdan lattices; this proves a geometric rigidity theorem about all of them (and all twin building lattices) that closes the subgroup-permanence refutation route against the LLP candidacy.
  non-rf-kazhdan-group-with-llp-full-c-star-algebra: that is the open LLP hole; this theorem removes its one recorded live refutation risk for the Kac--Moody candidates, so that no known mechanism decides the hole in either direction there.
  no-published-unconditional-codense-stable-host: that records fences against stable co-dense hosts (LERF, amenable quotients); this is a fence-removal theorem on the lifting side, for a different candidate class and a different hypothesis type.
---

**THEOREM.**  Let `Lambda` be a group acting properly, factor-preservingly
and cellularly on a product `X_+ x X_-` of two locally finite, COMPLETE
CAT(0) polyhedral complexes each with finitely many isometry types of
cells (e.g. any twin building lattice acting on the Davis realizations of
its twin buildings: a Kac--Moody group over `F_q` acting on its twin
buildings, `q >= |S|`).  Then:

```text
(a) every infinite-order element of Lambda is hyperbolic on the product:
    it is semisimple on each factor and has positive translation length;
(b) for every free abelian A = Z^k <= Lambda, the image of the normalizer
    N_Lambda(A) in GL_k(Z) = Out-action on A is FINITE;
(c) consequently Lambda contains no pair A rtimes Sigma with A = Z^k and
    Sigma acting through an infinite subgroup of GL_k(Z); in particular
    no Z^2 rtimes F_2 with standard (or any infinite-image) action, no
    Z^2 rtimes SL_2(Z), no Sym^2-pair Z^3 rtimes GL_2(Z), and no SL_n(Z)
    with n >= 3 (which contains a standard pair) embeds in Lambda.  (TL1)
```

```text
(d) X_+ x X_- has finite asymptotic dimension when each factor is a
    building (Dymara--Schick, *Buildings have finite asymptotic
    dimension*, arXiv:math/0703199: the asymptotic dimension of any
    building is finite and equals that of an apartment; asymptotic
    dimension is subadditive under products), and the orbit map of the metrically
    proper Lambda-action is a coarse embedding; hence every subgroup of
    Lambda has finite asymptotic dimension and property A, and contains
    no coarsely embedded expander sequence.                        (TL2)
```

Since the local lifting property passes to subgroups, parts `(c)` and
`(d)` together show that two of the known LLP-failure families cannot
embed in a twin building lattice: the cohomological `Z^k rtimes Sigma`
pairs of Ioana--Spaas--Wiersma (`Z^2 rtimes Sigma` with
`Sigma <= SL_2(Z)` nonamenable, `SL_n(Z)` with `n >= 3`, and groups
containing these) and the Osajda-type examples of
Buss--Echterhoff--Willett, which contain coarsely embedded expanders
(Fournier-Facio--Willett §3.2).  NOT excluded by this fence (2026-08-21
audit; Fournier-Facio--Willett Remark 3.8 lists four families): the
property (T) examples of Ozawa [Cor. 5] and Thom [p. 198], which are
neither of `Z^k rtimes Sigma` shape nor expander-containing, and the
char-`p` ring pairs `R^2 rtimes SL_2(R)`, `SL_n(R)` of ISW Corollary B,
whose abelian parts are torsion modules invisible to the `Z^k` fence.
An earlier version of this node claimed that NO known LLP-failure group
embeds; that was an overstatement and is withdrawn.  Combined with the vacuity of the direct
Ioana--Spaas--Wiersma mechanism at infinite simple groups (recorded in
`non-rf-kazhdan-group-with-llp-full-c-star-algebra`), NO currently known
method decides the LLP for the simple Kazhdan Kac--Moody lattices in
either direction — the candidate survives everything published.

**Scope remarks.**  (0) One factor may be a point: the theorem covers
proper cellular actions on a SINGLE locally finite polyhedral complex
with finitely many shapes, hence all lattices in automorphism groups of
one building — e.g. the Cartwright--Mantero--Steger--Zappa exotic
`A~_2` lattices (property (T), triangles of finite groups); should any
of these be shown non-residually-finite, they would join the Kac--Moody
lattices as candidates for
`non-rf-kazhdan-group-with-llp-full-c-star-algebra` with the same fences
excluded.    (i) The theorem is geometric: it needs neither
simplicity nor property (T) of `Lambda`, only the proper cellular action
on COMPLETE CAT(0) factors -- this hypothesis is essential and was
omitted in an earlier version: without it, `Z^2 rtimes SL_2(Z)` acting
freely on its own Cayley graph (times a point) satisfies every other
hypothesis and violates `(b)` and `(c)`, `BS(1,2)` violates remark (ii),
and `Z wr Z` (infinite asymptotic dimension) violates `(d)`;
it applies to all twin building lattices, affine (`SL_n(F_q[t, t^-1])`)
included — but for the AFFINE ones the char-`p` ring fences of
Ioana--Spaas--Wiersma Corollary B bite anyway: for `R = F_q[t]` with `q`
odd, `2R` is infinite, so `C^*(SL_n(R))` (`n >= 3`) and
`C^*(R^2 rtimes SL_2(R))` fail the LLP, and an affine twin lattice of
rank `>= 3` contains `SL_3(F_q[t])` inside `SL_3(F_q[t, t^-1])`.  Hence
affine twin lattices of rank `>= 3` (odd `q`) FAIL the LLP by subgroup
permanence, and more generally any Kac--Moody lattice whose Dynkin
diagram contains an affine subdiagram of rank `>= 3` inherits such a
subgroup.  The LLP candidacy is therefore confined to types with NO
affine subdiagram of rank `>= 3` — in particular the COMPACT HYPERBOLIC
diagrams, where every proper subdiagram is spherical and all root-group
generated `R`-module pairs are finite; the `(2,4,6)` instance of
`simple-kazhdan-kac-moody-lattices-exist` is of this kind.  The one
unrecorded residual risk is a char-`p` fenced pair `R^2 rtimes SL_2(R)`
embedded WITHOUT an affine subdiagram (an infinite-exponent-`p` abelian
subgroup with an infinite `SL_2(R)`-normalizer); the `Z^k` fence of this
theorem is blind to torsion modules, and no such embedding is recorded
in either direction.  (ii) Conclusion (a)
also reproves that such `Lambda` has no infinite-order distorted cyclic
subgroups, hence no Baumslag--Solitar `BS(1, n)` (`n >= 2`) subgroups.

---
rg: 2
id: twin-lattices-exclude-known-llp-fences
kind: claim
title: Twin building lattices normalize no distorted free abelian subgroup, so every known LLP-failure group is excluded as a subgroup
distinct_from:
  simple-kazhdan-kac-moody-lattices-exist: that imports the existence of the simple Kazhdan lattices; this proves a geometric rigidity theorem about all of them (and all twin building lattices) that closes the subgroup-permanence refutation route against the LLP candidacy.
  non-rf-kazhdan-group-with-llp-full-c-star-algebra: that is the open LLP hole; this theorem removes its one recorded live refutation risk for the Kac--Moody candidates, so that no known mechanism decides the hole in either direction there.
  no-published-unconditional-codense-stable-host: that records fences against stable co-dense hosts (LERF, amenable quotients); this is a fence-removal theorem on the lifting side, for a different candidate class and a different hypothesis type.
---

**THEOREM.**  Let `Lambda` be a group acting properly, factor-preservingly
and cellularly on a product `X_+ x X_-` of two locally finite polyhedral
complexes each with finitely many isometry types of cells (e.g. any twin
building lattice: a Kac--Moody group over `F_q` acting on its twin
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

Since the local lifting property passes to subgroups and every group
C*-algebra currently known to fail the LLP is one of
`Z^2 rtimes Sigma` (`Sigma <= SL_2(Z)` nonamenable), `SL_n(Z)` (`n >= 3`),
their relatives through the same pairs, or contains one of these
(Ioana--Spaas--Wiersma; Fournier-Facio--Willett §3.2), the
subgroup-permanence route cannot refute the LLP for any twin building
lattice.  Combined with the vacuity of the direct
Ioana--Spaas--Wiersma mechanism at infinite simple groups (recorded in
`non-rf-kazhdan-group-with-llp-full-c-star-algebra`), NO currently known
method decides the LLP for the simple Kazhdan Kac--Moody lattices in
either direction — the candidate survives everything published.

**Scope remarks.**  (i) The theorem is geometric: it needs neither
simplicity nor property (T) of `Lambda`, only the proper cellular action;
it applies to all twin building lattices, affine (`SL_n(F_q[t, t^-1])`)
included.  For the affine ones `C^*(Lambda)` may still fail LLP through
OTHER subgroups — `SL_3(F_q[t])`-type groups are fenced by
Ioana--Spaas--Wiersma's Corollary B remark on `SL_n(F_p[X])` — but those
fences again enter through congruence-unipotent pairs, which are
`(F_q[t], +)`-modules, not `Z^k`'s; the theorem's `Z^k` form does not
exclude them, and non-affine lattices over `F_q` have torsion root
subgroups throughout, so the char-`p` analogues of the fence pairs have
torsion fibres and carry no relative-(T) `Z^k`.  (ii) Conclusion (a)
also reproves that such `Lambda` has no infinite-order distorted cyclic
subgroups, hence no Baumslag--Solitar `BS(1, n)` (`n >= 2`) subgroups.

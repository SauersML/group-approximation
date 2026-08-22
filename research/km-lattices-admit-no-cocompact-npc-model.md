---
rg: 2
id: km-lattices-admit-no-cocompact-npc-model
kind: claim
title: Kac-Moody lattices admit no cocompact CAT(0) model, so no triangle of finite groups presenting one is nonpositively curved
artifacts:
  - research/artifacts/isw-ddjmo-cr-cohomology-sources-2026-08-21.md
distinct_from:
  twin-lattices-exclude-known-llp-fences: that proves flat-torus and asymptotic-dimension rigidity of the proper twin action to exclude LLP-failure subgroups; this proves the NON-existence of any proper cocompact CAT(0) model at all, killing a hoped-for positive geometry rather than a refutation route.
  triangle-colimit-llp-reduces-to-relator-local-splitting: that is C*-algebraic bookkeeping for arbitrary triangles of finite groups; this is a geometric no-go theorem about which triangles can present a Kac--Moody lattice, and it corrects the geometry that node's instantiation may be read as promising.
---

Let `Lambda` be a split or almost split Kac--Moody group over `F_q`
with infinite Weyl group (a twin building lattice; in particular every
group of `simple-kazhdan-kac-moody-lattices-exist`).

**THEOREM.**

```text
(a) Lambda is not Gromov hyperbolic.  [Caprace--Remy, arXiv:math/
    0607664, Remark 2 after the normal-subgroup-property theorem,
    read at source: no Kac--Moody group over a finite field is
    hyperbolic -- via SQ-universality, or via the infinitely many
    conjugacy classes of torsion elements.]                      (NG1)

(b) Lambda admits no proper cocompact isometric action on any
    complete CAT(0) space: such an action allows at most finitely
    many conjugacy classes of torsion elements, while Lambda has
    infinitely many.                                             (NG2)

(c) Consequently no presentation of Lambda as the colimit of a
    nonpositively curved finite simple complex of FINITE groups
    exists.  For a triangle of finite groups presenting Lambda,
    with g_ij the girth of the vertex link (the coset graph of
    P_ij over P_i, P_j with edge set P_ij/P_0), necessarily

        2/g_12 + 2/g_13 + 2/g_23 > 1 :

    at least one link has short cycles, whatever finite vertex
    groups are used.                                             (NG3)

(d) Separation of families.  A triangle of finite groups whose
    links are generalized m_ij-gon incidence graphs (girth 2 m_ij)
    with 1/m_12 + 1/m_13 + 1/m_23 <= 1 IS nonpositively curved;
    its colimit acts properly cocompactly on the CAT(0) (CAT(-1)
    when the sum is < 1) development, has boundedly many torsion
    conjugacy classes, and is therefore NEVER a Kac--Moody
    lattice.                                                     (NG4)
```

Proof: `km-no-cocompact-npc-model-proof`.

**What this corrects and separates.**  The LLP hole's dossier
(`non-rf-kazhdan-group-with-llp-full-c-star-algebra`) hoped that "the
geometry that might power" an LLP permanence for the triangle —
generalized polygon links of large girth, CAT(0) complex — is
available at the Kac--Moody candidates.  By (NG3) it never is: the
Kac--Moody lattice's own triangles (the Abramenko--Mühlherr
presentation [AM97], identified at source through Caprace--Rémy) have
links with short cycles, and no metrization is nonpositively curved.
By (NG4) the large-girth NPC triangles form a DIFFERENT candidate
family — Gersten--Stallings colimits acting properly cocompactly on
their CAT(-1) developments (Fuchsian-building-type uniform lattices)
— to which `triangle-colimit-llp-reduces-to-relator-local-splitting`
applies verbatim, with `r = q^{m}` relators that are literally the
girth-length-`2m` cycles of the link.  Whether any such uniform
lattice is non-residually-finite is UNRECORDED (compare the
Cartwright--Mantero--Steger--Zappa scope remark on
`twin-lattices-exclude-known-llp-fences`), so this family does not
yet instantiate the non-RF hole; but for Fournier-Facio--Willett
Question 1.9 (any infinite (T) group with the (L)LP) it is the family
where the girth geometry genuinely lives, provided its (T) status
(Dymara--Januszkiewicz thickness bounds) is verified per instance.

**Consequences for the cohomology sub-task.**  (b) blocks every
shortcut of the form `H^*(Lambda, Z Lambda) = H^*_c(model)`: Brown's
criterion needs a proper cocompact contractible model, and none
exists in the CAT(0) world; the twin product `X_+ x X_-` is proper
but NOT cocompact (Caprace--Rémy at source), one building `X_+` is
cocompact but NOT proper (infinite chamber stabilizer), and the
triangle development is proper cocompact but not known contractible
(and never CAT(0), by (c)).  This is why
`compact-hyperbolic-km-lattices-fail-lp` is open rather than a
corollary of the building computations.

---
rg: 2
id: osajda-monster-hosts-for-bc-module-route
kind: claim
title: Verified host inventory for the module Baum--Connes route -- Gromov and Osajda non-exact groups, the Haagerup non-exact groups, and Higson--Kasparov
distinct_from:
  some-nonexact-group-has-a-k-inexact-module-triple: that is the open existence of a module triple with a K-defect; this records the verified literature about the candidate host groups G and the assembly-map theorem that prunes some of them.
  reduced-group-algebras-contain-no-nonzero-ghosts: that is the ghost obstruction inside the group algebra; this is a source-verified inventory of the candidate host groups and which of them fail Baum--Connes with coefficients.
---

**ESTABLISHED (citation)** by `osajda-monster-hosts-for-bc-module-route-citation`. Facts read
from the arXiv PDFs, quoted below with theorem numbers.

The module route (`bc-counterexample-via-module-k-inexactness`) needs a host group `G` for
`X = V^`, `Z = W^perp`. The candidates and their verified properties:

**(1) Gromov monsters.** M. Gromov, *Random walk in random groups*, Geom. Funct. Anal. 13
(2003), no. 1, 73--146 (MR1978492). A finitely generated group whose Cayley graph contains a
**weakly** embedded sequence of expanders (corrected 2026-09-13; an earlier version said
"coarsely"). Non-exact. Higson--Lafforgue--Skandalis (GAFA 12 (2002), no. 2, 330--354) show they
fail Baum--Connes **with commutative coefficients**, using the weak embedding. Gromov's labelling
gives only a *weak* embedding of the relators, not a coarse embedding of the graphs into the
group: Osajda (item (2)) writes that "in the case of the Gromov monster expanders are not even
coarsely embedded."

**(2) Osajda isometric-expander groups.** D. Osajda, *Small cancellation labellings of some
infinite graphs and applications*, Acta Math. 225 (2020), no. 1, arXiv:1406.5015.
- **Theorem 1 (= Theorem 2.7):** for every `lambda > 0` there is a `C'(lambda)` small
  cancellation labelling of any sequence `(Theta_n)` of `D`-regular graphs (`D > 2`) of growing
  girth over a finite alphabet.
- **Subsection 1.3:** taking `(Theta_n)` an expanding family, the resulting group has the
  expanders embedded **isometrically** into its Cayley graph, "in contrast, in the case of the
  Gromov monster expanders are not even coarsely embedded." These groups are therefore **not
  coarsely embeddable into a Hilbert space**, and "various versions of the Baum--Connes
  conjecture fail for them."

**(3) Osajda Haagerup non-exact groups.** Same paper, arXiv:1406.5015.
- **Theorem 2 (= Theorem 6.3):** there exist finitely generated groups acting **properly on
  CAT(0) cubical complexes** and **not having property A** (i.e. non-exact).
- Acting properly on a CAT(0) cube complex gives property PW, hence the **Haagerup property**
  (a-T-menability) and coarse (indeed equivariant) embeddability into a Hilbert space. So these
  are non-exact **and** a-T-menable; they answer negatively "Do coarsely embeddable groups have
  property A?"

**(4) Osajda residually finite non-exact groups.** D. Osajda, *Residually finite non-exact
groups*, Geom. Funct. Anal. 28 (2018), no. 2, 509--517, arXiv:1703.03791.
- **Main Theorem:** there exist finitely generated **residually finite** non-exact groups,
  defined by infinite graphical small cancellation presentations.
- **Construction, Sections 3.1--3.2.**
  - `(Theta_i)` is a sequence of `D`-regular graphs, `D >= 3`, carrying a strengthened `C'(lambda)`
    labelling, "constructed in [Osa14]".
  - The relators are the **Z/2-homology covers** `Theta^_1` of `Theta_1` and `Theta^_(i+1)` of a
    finite normal cover `Theta-bar_(i+1)` of `Theta_(i+1)`.
  - The Z/2-homology cover walls make each finite stage cubulated, hence residually finite by
    Wise and Agol.
- **Section 3.3 (proof).** The Cayley graph "contains isometrically embedded copies of all the
  graphs `Theta^_i`. That is, `Cay(G,S)` contains a sequence of `D`-regular graphs of growing
  girth, and hence `G` is non-exact, by [Wil11]" (R. Willett, *Property A and graphs with large
  girth*, J. Topol. Anal. 3 (2011), no. 3, 377--384). Non-exactness uses **girth only**.
- **Correction (2026-09-13).** An earlier version of this node said the embedded family "can be
  taken expanding", so that this residually finite host "also fails Baum--Connes with
  coefficients".
  - That was never verified.
  - It is false for the construction as written: Z/2-homology covers never form an expander family
    (`osajda-rf-relator-covers-are-not-expanders`).
  - No known theorem gives these groups a failure of Baum--Connes with coefficients.

**(5) Higson--Kasparov.** N. Higson and G. Kasparov, *E-theory and KK-theory for groups which
act properly and isometrically on Hilbert space*, Invent. Math. 144 (2001), 23--74. Every
**a-T-menable** (Haagerup) discrete group satisfies the Baum--Connes conjecture **with
coefficients**: `mu_(G,B)` is an isomorphism for every separable `G`-C*-algebra `B`.

**Reading for the route.**
- Failure of Baum--Connes with coefficients is the entry ticket for the module route. It is known
  for hosts with an embedded expander:
  - type (1), weakly embedded (Higson--Lafforgue--Skandalis);
  - type (2), isometrically embedded.
- Type (4) is residually finite and non-exact. Its relators are not expanders, and no known
  theorem gives it a coefficient failure, so it is **not** a verified host
  (`osajda-rf-relator-covers-are-not-expanders`).
- Type (3) is non-exact but a-T-menable, so by (5) it satisfies Baum--Connes with **every**
  coefficient. It is a witness that **non-exact does not imply failure of Baum--Connes with
  coefficients**. Its consequence for the route is drawn in
  `module-defect-needs-non-k-exact-host`.

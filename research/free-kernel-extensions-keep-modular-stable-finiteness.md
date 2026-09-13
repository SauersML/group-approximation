---
rg: 2
id: free-kernel-extensions-keep-modular-stable-finiteness
kind: claim
title: Over a division ring of positive characteristic, residually-p kernels, and in particular free kernels of any rank, carry stable finiteness from the quotient to the group, so free-by-sofic groups satisfy Kaplansky
distinct_from:
  residually-p-kernels-preserve-modular-stable-finiteness: that is the same extension step over fields; this extends it to division ring coefficients and adds free kernels, sofic quotients over division rings, and explicit free-kernel forms of doubles and trivial HNN extensions.
  doubles-of-surjunctive-groups-are-surjunctive: that transfers surjunctivity to doubles; this transfers stable finiteness over division rings, which needs no surjunctivity of the vertex group.
  linear-sofic-group-algebra-is-stably-finite: that is the field-coefficient theorem for linear sofic groups; this proves the division-ring statement for sofic groups by a direct rank count and uses it as the quotient input.
---

Let `D` be a division ring of characteristic `p > 0`.

1. **Extension step.** Let `1 -> N -> W -> Q -> 1` be a group extension in which `N` is
   residually a finite `p`-group. If `D[Q]` is stably finite, so is `D[W]`. If `D[Q]` is directly
   finite, so is `D[W]`.
2. **Free kernels.** Free groups of every rank, and free abelian groups of every rank, are
   residually finite `p`-groups.
3. **Sofic quotients.** If `Q` is sofic, `D[Q]` is stably finite.
4. **Doubles and trivial HNN extensions.** For every group `G`, subgroup `Gamma <= G` and
   `X = G/Gamma`:

   ```text
   G *_Gamma G              ~=  F(X \ {Gamma}) x| G,
   < G, t | [t, gamma] = 1 (gamma in Gamma) >  ~=  F(X) x| G,
   ```

   with `F(-)` free and `G` acting as in the proof. So each of
   `D[G *_Gamma G]`, `D[<G,t | [t,Gamma]>]`, `D[(directSum_X Z) x| G]` and `D[(*_X Z) x| G]` is
   stably finite (resp. directly finite) iff `D[G]` is.

**Consequence.** Every free-by-sofic group, with free kernel of any rank, has stably finite
group rings over every division ring of positive characteristic. This covers nonsofic groups:
see `nonsofic-witness-finiteness-over-modular-division-rings`.

**Credit and scope.**
- Ara--O'Meara--Perera (Adv. Math. 170 (2002) 224--238) proved stable finiteness of `D[G]` for
  free-by-amenable `G` over division rings of every characteristic. Checked from the abstract as
  returned by a web search; the paper was not read.
- Berlai (arXiv:1501.02893, abstract read) proved Kaplansky's direct and stable finiteness for
  {finitely generated residually finite}-by-sofic groups over all noetherian rings.
- The kernels here may be infinitely generated, as they are for doubles over infinite-index
  subgroups. Over fields the extension step is already on main, and the field case for doubles
  over surjunctive groups also follows from main's surjunctivity transfer together with Phung's
  theorem that surjunctive groups have stably finite group rings (Ceccherini-Silberstein--
  Coornaert--Phung, Groups Geom. Dyn. 19 (2025), Theorem 1.1, read from the PDF).
- Characteristic zero is not treated. Over fields of characteristic zero Kaplansky's theorem
  covers all groups; over division rings of characteristic zero the separation step below needs
  residually torsion-free nilpotent kernels instead, and that is not proved here.
- No novelty is claimed beyond the graph and the three sources above.

Proof: `free-kernel-extensions-modular-finiteness-proof`. Not independently reviewed.

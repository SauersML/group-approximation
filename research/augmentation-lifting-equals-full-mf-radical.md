---
rg: 2
id: augmentation-lifting-equals-full-mf-radical
kind: claim
title: For a group with no nontrivial finite-dimensional representations, augmentation-ideal lifting is equivalent to full MF radical
distinct_from:
  binary-leavitt-unit-group-is-minimally-almost-periodic: that establishes the hypothesis -- absence of nontrivial finite-dimensional unitary representations -- for one specific group; this is the general observation that, under exactly that hypothesis, a proposed C*-algebraic lifting route is not a route at all.
  full-mf-radical-cstar-reflection: that transports the full-radical property across a C*-algebraic reflection and is a usable tool; this records a proposed tool that is provably circular and therefore is not one.
  mf-relation-closure: that is the semantic organization of the MF radical as a closure operator; this is a no-go about one proposed proof strategy for making the radical full.
artifacts:
  - research/artifacts/opnorm-burnside-dossier-2026-08-24.md
---

Let `G` be countable with **no nontrivial finite-dimensional unitary
representation**. Put `A = C*_max(G)`, let `eps : A -> C` be the augmentation
and `I_G = ker eps`. Say `I_G` has the **corona lifting property** if for
every norm matrix corona `Q = (prod_n M_(d_n))/(oplus_n M_(d_n))` every
`*`-homomorphism `I_G -> Q` lifts to a `*`-homomorphism
`I_G -> prod_n M_(d_n)`.

Then the following are equivalent:

1. `I_G` has the corona lifting property;
2. every `*`-homomorphism `I_G -> Q` is zero, for every `Q`;
3. `Rad_MF(G) = G`.

**Consequence, which is the point.**  The tempting argument -- "if `I_G` were
matricially semiprojective and had no nonzero finite-dimensional
representations, every corona representation would annihilate it, hence
`Rad_MF(G) = G`" -- is *valid*, full-norm, and free of traces, corners and
compressions. It is nevertheless **not a proof strategy**: on exactly the
class of groups where it applies, its hypothesis is equivalent to its
conclusion. The dossier that proposed it described the two as merely "close";
they are the same statement.

**What would resurrect it.**  Only an independent structural criterion, of
the form *augmentation ideals of groups in some recognizable class are
matricially semiprojective for a C*-algebraic reason having nothing to do
with their finite-dimensional representation theory*. No such theorem is
known to this lane, and none applies to the binary Leavitt elementary groups.
Recorded so the route is not re-proposed as new.

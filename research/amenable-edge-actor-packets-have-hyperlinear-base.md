---
rg: 2
id: amenable-edge-actor-packets-have-hyperlinear-base
kind: claim
title: Amenable-edge actors give hyperlinear packet bases for every amenable module, so the character-energy interface fails for them
distinct_from:
  amenable-edge-graph-corners-cannot-groupify-a-nonce-game: that proves permanence for a graph of hyperlinear groups; this proves that an arbitrary module extension of an amenable-edge actor is again such a graph, and applies it to the marked packet.
  virtually-free-linear-self-similarity-retains-fd-mark: that treats finite-type linear modules over virtually free actors through finite-dimensional marks; this treats arbitrary countable amenable modules over arbitrary amenable-edge actors and kills the energy interface itself.
  sofic-chart-quotient-forces-character-energy-floor: that kills sofic permutation-module packets by chart adversaries; this kills packets according to the Bass--Serre shape of the actor, with no sofic or permutation hypothesis on the module.
  central-d8-seed-preserves-hyperlinearity: that says the seed detects rather than creates nonhyperlinearity; this identifies an explicit actor class where there is nothing to detect.
  normal-kazhdan-kernel-cannot-live-in-amenable-edge-tree: that locates Kazhdan normal subgroups in amenable-edge trees; this passes an amenable normal module through the tree.
---

**ESTABLISHED.**  Let `Gcal` be a finite connected graph of countable groups
with injective edge maps, and put `A=pi_1(Gcal)`.  Let `N` be a countable
amenable group with an action `theta:A -> Aut(N)` (for the packet, `N=M` is
the elementary abelian module).  Assume

```text
every G_e is amenable,  every N rtimes G_v is hyperlinear.   (AEA0)
```

(`AEA0` holds, for example, when every vertex group is amenable, since then
`N rtimes G_v` is amenable.)  Then

```text
N rtimes A ~= pi_1(Gcal_N),
  (Gcal_N)_v = N rtimes G_v,   (Gcal_N)_e = N rtimes G_e,      (AEA1)
```

is again a finite graph of groups with amenable edge groups, and so

```text
N rtimes A is hyperlinear.                                    (AEA2)
```

Consequently, for every packet `G=M rtimes A` in this class and every
involution `m_0` of `G`, the marked group `P(G,m_0)` is hyperlinear, `J!=1`
in `P`, `J` is not in the hyperlinear radical, and

```text
no fixed finite presentation of P(G,m_0) satisfies the uniform
terminal estimate (ICR2); every seed-preserving decoded PVM on
canonical microstates has liminf E_act >= gamma/4.            (AEA3)
```

**Actors killed.**  Amenable actors (one vertex); finite graphs of finite
groups, hence every virtually free actor, including `SL_2(Z)=C_4 *_(C_2)
C_6`; free groups and free products of amenable groups; Baumslag--Solitar
groups `BS(m,n)` (HNN over `Z`); fundamental groups of finite graphs of
amenable groups with amenable edges; and, recursively, amenable-edge graphs
whose vertex groups `G_v` are themselves in this class **relative to the
restricted module**, since `N rtimes G_v` is then hyperlinear by the same
theorem.  No hypothesis is placed on the module: arbitrary infinite
characters, nonsofic coordinate actions, non-permutation modules and
non-dense homoclinic duals are all covered.

**Invariant and death step.**  The invariant is hyperlinearity of the
unmarked base `M rtimes A`.  Every member of the class dies at the terminal
estimate `(ICR2)`: that estimate forces `J` into the hyperlinear radical of
`P`, which by `central-d8-mark-radical-equals-seed-radical` and `(CDS3)`
requires the base to be nonhyperlinear, contradicting `(AEA2)`.

**Consequence for surviving actors.**  A packet that could still prove the
interface needs an actor with a nonamenable edge in *every* splitting at the
load-bearing level: in practice an actor with Serre's property (FA) or with
only nonamenable splittings (e.g. `SL_3(Z[1/2])`, the Andre--Guirardel
Kazhdan actor).  Actor-word energy arguments whose only rigidity input is a
spectral gap of a free, virtually free or amenable-edge actor on `Omega` are
therefore refuted as a class, however the module and seed are chosen.

DERIVATION
amenable-edge-actor-packet-base-hyperlinear-proof

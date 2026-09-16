---
rg: 2
id: amenable-by-maximal-groups-have-positive-rokhlin-entropy
kind: claim
title: A group with an amenable normal subgroup whose quotient has infinite Rokhlin supremum has a free ergodic action of positive Rokhlin entropy
distinct_from:
  rokhlin-maximality-ascends-amenable-normal-extensions: that asks for maximal Rokhlin entropy of every Bernoulli shift over W; this asks only for one free ergodic action of W, of any kind, with positive Rokhlin entropy. The two are equivalent for the whole class (products P x W stay in it), but not visibly for one group.
  every-group-has-positive-rokhlin-entropy-action: that is Seward's POS hypothesis for all countably infinite groups; this is POS only for amenable-by-INF groups, where the quotient already has maximal entropy.
  positive-rokhlin-entropy-action-gives-positive-supremum: that shows the conditions POS and h_sup > 0 are equivalent for each group; this is the open existence statement for one class of groups.
  kun-thom-wreath-bernoulli-rokhlin-maximal: that is maximality for one nonsofic group; this is positive entropy for every amenable-by-INF group, whose instance at P x W_KT is equivalent to that claim.
  rokhlin-supremum-of-torsion-products-is-zero-or-infinite: that proves POS(P x G) iff INF(G) for each G, which transports the question without deciding it; this asserts POS for the amenable-by-INF class, which that theorem neither proves nor refutes for any nonsofic member.
---

**OPEN.** Let `W` be a countable group with an amenable normal subgroup `N` such that `h_sup(W/N) = ∞`. Here
`h_sup` is Seward's Rokhlin entropy supremum (`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`). The
condition is equivalent to: `W/N` is countably infinite and Rokhlin-maximal at some `q`. Then some free ergodic
p.m.p. action of `W` has positive Rokhlin entropy.

**Equivalence with the target.**
- The route `amenable-kernel-ascent-from-positive-entropy-on-products` derives
  `rokhlin-maximality-ascends-amenable-normal-extensions` from this claim. It applies the claim to `P × W` with
  `P = ⊕ Z/nZ`, then uses `rokhlin-supremum-of-torsion-products-is-zero-or-infinite`.
- Conversely, the target makes `W` maximal, hence INF(`W`) by Seward's Theorem 1.10, hence POS(`W`). That
  direction is not recorded as a route.
- So this hole is a **reformulation**, not a strictly weaker statement.

**What the reformulation changes.**
- A proof may use any single free ergodic action of `P × W` with any positive lower bound. It does not need the
  Bernoulli shift or the value `log q`.
- A counterexample to the target at `W` produces the group `P × W` in this class with `h_sup = 0`. By
  `generators-dense-iff-zero-rokhlin-entropy`, generating partitions are then dense in every free ergodic action
  of `P × W`. So disproof attempts may aim at total collapse.

**Known cases.**
- `W` sofic: every Bernoulli shift has full entropy.
- `W/N` finite cannot occur, since `h_sup` is defined for infinite groups.
- Split `W = N ⋊ Q` with `Q` co-amenable in `W`: Theorem A of
  `rokhlin-maximality-ascends-co-amenable-subgroups` gives maximality, hence POS.

Open instances include `P × W_KT` for the Kun–Thom wreath `W_KT` (`kun-thom-nonsofic-wreath`), and every
nonsplit or non-co-amenable shape.

## Attempts

Full details are in `notes/rokhlin-maximality-ascends-amenable-norm-swarm-2026-09-16.md`, Section 3
(swarm-rokhlin-maximality-ascends-ame, 2026-09-16).

- **Bernoulli shifts over `W`.** This is the target itself. The Følner count along `N` needs coherent windows,
  hence a conjugation-invariant mean (`coherent-kernel-folner-windows-force-conjugation-invariant-mean`), which fails
  on the Kun–Thom wreath. The count along `W/N` pays a nonamenable boundary.
- **Actions assembled from the quotient.** Suppose `N` is infinite. Pulling back a Bernoulli shift of `W/N` gives
  a non-free action `Y` whose information is fixed by `N`. For any free ergodic joining `Y × X`, zero outer entropy
  gives `h_W(Y × X) = h_W(Y × X | F_N)`, and `F_N ⊇ B(Y)`
  (`infinite-subgroup-invariant-information-has-zero-outer-entropy`). So the quotient's entropy does not survive.
  For `P × W`, product actions `X_P × X_W` fare no better: each factor is fixed by an infinite subgroup, so the
  entropy equals the entropy relative to either factor, and no lower bound follows. A finite `N` is the open
  finite-kernel case below.
- **Skew products over cocycles `W/N × Y → N`.** These are free, but no lower bound is available. A lower bound
  again needs a relative count along `W/N` with `N`-fibres, i.e. Seward's direct-product conjecture
  (`seward-direct-product-relative-rokhlin-entropy-conjecture`) for a non-weakly-minimal factor.
- **Finite subgroups `T ≤ P`.** Restriction gives only `h_(W×T) ≥ h_W / |T|`, which decays. This is the collapse
  mechanism of Seward's Theorem 6.7 run backwards, and it produces no positive bound.
- **Finite approximations.** Finite quotients of `N` and invariant random subgroups inside `N` see only the sofic
  radical (`sofic-radical-localizes-bernoulli-deficit-witnesses`). They reduce to finite-kernel ascent
  (`rokhlin-maximality-ascends-finite-normal-extensions`), which is open.

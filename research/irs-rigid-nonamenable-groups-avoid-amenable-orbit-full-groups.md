---
rg: 2
id: irs-rigid-nonamenable-groups-avoid-amenable-orbit-full-groups
kind: claim
title: A realization inside an amenable orbit full group that is free off its fixed points forces amenability, so IRS-rigid non-amenable groups act trivially
distinct_from:
  stabilizer-rigid-groups-avoid-amenable-orbit-full-groups: That excludes infinite simple groups with only trivial and regular characters, such as V, through a GNS argument; this isolates the amenability step and excludes every non-amenable group whose ergodic invariant random subgroups are only the two trivial ones, a weaker rigidity hypothesis that is what is known for some Kac--Moody lattices.
  kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf: That uses property (T) to force finite orbits; this uses stabilizer rigidity to force freeness and then amenability, and applies to groups without (T).
---

**ESTABLISHED.**

**Setting** (as in `amenable-orbit-full-group-subgroups-are-sofic`). `Lambda` is a
countable amenable group acting essentially freely, preserving `mu`, on a standard
probability space `X`. `W(Lambda ~ X)` is the group of Borel bijections `g` with
`g(x) = c_g(x) x` for a Borel `c_g : X -> Lambda` of finite range. `Gamma` is a
countable group and `rho : Gamma -> W(Lambda ~ X)` a homomorphism. Let
`F = {x : rho(g) x = x for all g}` and `Y = X \ F`.

**Theorem.**
1. **Free realizations are amenable.** If `mu(Y) > 0` and `mu(Fix rho(g) ∩ Y) = 0`
   for every `g != 1`, then `Gamma` is amenable.
2. **IRS rigidity.** Suppose every ergodic invariant random subgroup of `Gamma` is
   `delta_{1}` or `delta_Gamma`, and `Gamma` is not amenable. Then `mu(Y) = 0`: the
   realization is trivial almost everywhere.

**Consequence for the finitely presented simple question.** A non-amenable
realization, in particular one of a non-amenable finitely presented infinite
simple group witnessing `fp-simple-group-in-amenable-orbit-full-group`, has a
nontrivial ergodic invariant random subgroup: the stabilizer of a random point of
some ergodic component. So such a witness is a finitely presented infinite simple
group with a nontrivial IRS.
- `stabilizer-rigid-groups-avoid-amenable-orbit-full-groups` is the special case
  of item 2 for infinite simple groups with only trivial and regular characters.
- `caprace-thom-v2-leaves-km-character-rigidity-open` records IRS rigidity for
  specified compact-hyperbolic Kac--Moody lattices (Caprace--Thom, arXiv:2606.27993v2,
  Corollary 5.3). Whenever those lattices are non-amenable, item 2 excludes them,
  with or without property (T). Which finitely presented simple lattices satisfy
  those hypotheses was not cross-checked here.

**Model test.** `Lambda` itself realizes freely and is amenable, so item 1 is sharp.
The Elek--Monod dynamical alternating group is non-amenable and realized
nontrivially, so by item 2 it has a nontrivial ergodic IRS, as its non-free Cantor
action shows.

Proof: `irs-rigid-nonamenable-groups-avoid-orbit-full-groups-proof`.

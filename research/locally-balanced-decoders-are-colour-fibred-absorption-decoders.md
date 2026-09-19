---
rg: 2
id: locally-balanced-decoders-are-colour-fibred-absorption-decoders
kind: claim
title: An automaton is locally balanced exactly when it decodes a Bernoulli absorption fibred over a proper-colouring shift, and whether it decodes a genuine absorption is decided on the symmetric locus of targets
distinct_from:
  locally-balanced-decoders-admit-translation-lifts: that asks for a genuine absorption from a non-injective balanced automaton; this proves the colour-fibred absorption always exists, so that claim becomes exactly the de-colouring of it, and it localizes the de-colouring for a fixed automaton to targets supported on the symmetric locus.
  extension-decoders-are-locally-balanced: that proves translation lifts give balance and that balance gives one-site lifts; this schedules those one-site lifts by colourings, which turns balance into a full product trivialization over the colouring base and makes the one-site-lift characterization an equivalence.
  post-surjective-sft-covers-admit-scheduled-sections: that schedules lifts of a post-surjective cover to get a section, an injective map of fibre dimension zero; this schedules bijective lifts of a balanced automaton to get a homeomorphism onto a product, and needs balance, not only post-surjectivity.
  cover-pair-sections-localize-to-the-symmetric-locus: that localizes the section problem of a cover pair to seeds exact on Sym_E; this localizes the absorption problem of a balanced automaton to fibre trivializations over targets that equal a constant off the locally symmetric sites.
  monomial-quantum-automata-are-topological-bernoulli-absorptions: that identifies absorptions with automata carrying commuting translation lifts; this shows that without commutation, scheduled lifts already give the absorption over any colouring base, so commutation is only needed where no colouring exists.
---

**ESTABLISHED (elementary)** by [[balanced-decoders-colour-fibred-absorption-proof]].

**Setting.** `G` is a group, `A = Z/q` with `q >= 2`, and `sigma` is a cellular automaton on `A^G` with memory
`W`. "Locally balanced with lift set `S`" is as in `extension-decoders-are-locally-balanced`. For a finite
symmetric `E ∋ 1`, `C_E ⊆ [N]^G` is the shift of proper colourings of the Cayley graph `g ~ gk`, `k ∈ E \ {1}`,
with `N = |E|`; it is a nonempty SFT, with no constant point once `E ≠ {1}` (and `E` may always be enlarged). A **`C_E`-fibred absorption with decoder `sigma`** is
a continuous equivariant homeomorphism

    Psi : C_E x A^G -> C_E x A^G x Y,   Psi(kappa, u) = (kappa, sigma(u), W_kappa(u)),

with `Y` a subshift. The decoder `sigma` does not depend on the base point `kappa`. The shift acts diagonally.

**Theorem I (balance is colour-fibred absorbability).** These are equivalent:
1. `sigma` is locally balanced for some lift set `S`;
2. for some finite symmetric `E ∋ 1`, there is a `C_E`-fibred absorption with decoder `sigma`.

In (2), `|Y| >= 2` exactly when `sigma` is not injective, and `Y` can be taken to be `sigma^-1(c_0)`, the fibre
over the constant `c_0 = sigma(0^G)`, which contains `0^G`. For (1) ⇒ (2) one can take
`E = {1} ∪ DW S^-1 ∪ S(DW)^-1`, with `D = {e} ∪ SW^-1`.

**Theorem L (localization to the symmetric locus).** Let `sigma` be locally balanced, with `E` as in Theorem I and
`Y = sigma^-1(c_0)`. Put `Sym_E = {y ∈ A^G : k.y = y for some k ∈ E \ {1}}`, a closed set of *targets*. For a
clopen `U ⊇ Sym_E` and a target `y`, put

    Z_U(y) = {g ∈ G : g^-1 . y ∈ U},     y_U = c_0 + (y - c_0) 1_(Z_U(y)).

So `y_U` agrees with `y` at the sites where `y` looks locally `E`-symmetric, and with `c_0` elsewhere. These are
equivalent:
- (i) there is an equivariant homeomorphism `Psi : A^G -> A^G x Y'`, for some subshift `Y'`, whose first
  coordinate is `sigma`;
- (ii) for some clopen `U ⊇ Sym_E`, there is a continuous equivariant `L : A^G x Y -> A^G` such that, for every
  target `y`, `L(y, .)` is a bijection from `Y` onto `sigma^-1(y_U)`;
- (iii) statement (ii) holds for every clopen `U ⊇ Sym_E`.

When `sigma` is not injective, (i) is a topological Bernoulli absorption, as in
`no-group-carries-a-topological-bernoulli-absorption`.

**Proposition F (fibre conjugacy over fixed targets).** If (i) holds, then for every subgroup `H ≤ G` and every
`H`-fixed target `y`, the fibre `sigma^-1(y)` is `H`-equivariantly homeomorphic to `Y`. In particular:
- the `q` fibres over the constant targets are pairwise conjugate subshifts;
- each contains exactly one constant configuration;
- `sigma` permutes the `q` constant configurations.

None of this needs the lift radius. It depends on `sigma` alone.

**Consequences.**
1. **T2 is exactly a de-colouring problem.** By Theorem I, `locally-balanced-decoders-admit-translation-lifts`
   says: a group that carries a `C_E`-fibred absorption with a base-independent decoder and `|Y| >= 2` carries a
   genuine absorption. Commutation of one-site lifts is never needed off the symmetric locus. This is the
   absorption analogue of the section de-colouring question (Proposition C of
   `post-surjective-sft-covers-admit-scheduled-sections`, bus need 36774ad3).
2. **The w16 cocycle obstruction is empty.** Attempt 1 on that claim died because fibre enumerations must form a
   cocycle over the moves of the neighbouring lifts. The scheduled product in colour order is such a cocycle
   whenever a proper colouring is available: Theorem I over an external colouring, and Theorem L over a colouring
   read from the target wherever the target is locally `E`-free. So no argument that only uses free (locally
   asymmetric) windows can obstruct T2. Every obstruction to a translation lift of a fixed `sigma` is carried by
   the targets `y_U`, which equal `c_0` off the locally symmetric sites.
3. **Class kill: keeping the automaton.** Consider the approaches that keep `sigma` and look for commuting lifts at
   a larger lift set or radius. This includes the finite constraint problem on the labelled ball recorded on T2.
   - *Invariant.* The conjugacy classes of the fibres `sigma^-1(c^G)`, `c ∈ A`, and more generally of `H`-fixed
     fibres. Enlarging `S` or the radius leaves them unchanged.
   - *Where every member dies.* At a constant target, a genuine lift makes the constant element `b^G` of the
     compact group `(Z/q)^G` act as a `G`-equivariant homeomorphism `sigma^-1(c^G) -> sigma^-1((c+b)^G)`.
   - By Proposition F, all such approaches die on any balanced `sigma` with two non-conjugate constant fibres, or
     with a constant fibre holding two constants. For such `sigma`, a proof of T2 must change the automaton.
   - Whether every balanced automaton has conjugate constant fibres is open. On sofic groups it is automatic,
     since balanced automata are reversible there.
4. **Measure-theoretic shadow (remark, not claimed).** Over a countably infinite `G`, feeding Theorem I a Borel
   proper colouring of the free part of an auxiliary Bernoulli shift `E'^G` (as in Theorem B of
   `post-surjective-sft-covers-admit-scheduled-sections`) should give a measure-preserving equivariant
   isomorphism `(A x E')^G ≅ A^G x Z` over `E'^G`. The fibre measure is not a point mass when `sigma` is not
   injective. The proof sketch is in Step 7 of the route. It is not needed above.

**Not claimed.** Nothing here decides T2 at any group. No balanced non-injective automaton is known (any carrier is
nonsofic). Whether condition (ii) of Theorem L can be met by changing `sigma` is the open content.

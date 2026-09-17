---
rg: 2
id: translating-transport-split-lifts-are-surjective
kind: claim
title: An injective automaton whose quiescent sites are carried along by a cofinite translation is surjective, so one-letter split lifts with translating rest bits are never strict
distinct_from:
  passive-fixing-injective-automata-are-surjective: that keeps every passive site in place and passive symbols passive; this lets the quiescent sites and their extra data move, merge and mix arbitrarily near a finite defect, and asks only for an injective transport that is a translation cofinitely.
  local-passivity-preserving-injective-automata-are-surjective: that assumes passivity is preserved coordinatewise; this allows the quiescent set to change shape and uses a counting transport instead.
  finite-injective-charge-noncreation-forces-surjectivity: that assumes the charge never increases; this derives that nonincrease for the non-quiescent count from a transport of quiescent sites or of the data stored on them, then applies that theorem.
  count-raising-reversible-automata-lower-biased-rokhlin-entropy: that proves consequences of a count-raising reversible automaton through Rokhlin entropy; this is a counting obstruction for lift designs over every group with no entropy input.
  nonsurjunctive-alphabet-sizes-are-upward-closed: that asks for strict automata at every larger alphabet size; this kills the one-letter split lifts with translating rest bits as a method for producing them.
---

**ESTABLISHED** by `split-letter-lift-translation-count-proof`, from `finite-injective-charge-noncreation-forces-surjectivity`.

Let `G` be any group, `A` a finite alphabet and `a0 ∈ A`. For a configuration `u` whose sites outside `a0` form a
finite set `E(u)`, write `Z(u) = G \ E(u)`.

**Theorem A (transport count).** Let `τ` be a cellular automaton on `A^G` with `τ(a0^G) = a0^G`, injective on
finitely supported configurations. Suppose that for every finitely supported `u` there are an element `s_u ∈ G`, a
finite set `Q_u` with `|Q_u| >= 2`, a finite set `F_u ⊆ G`, and an injective map

    T_u : Q_u^{Z(u)} -> Q_u^{Z(τ u)}

such that, for every `g ∉ F_u`, the coordinate `T_u(z)(g s_u)` is a fixed bijective relabelling of `z(g)`. Then
`|E(τ u)| = |E(u)|` for every finite `u`, and `τ` is surjective.

The special case `|Q_u| = 2` with `T_u` induced by an injective site map `m_u : Z(u) -> Z(τ u)` that equals
`g -> g s_u` for all but finitely many `g` is the *hotel transport*: quiescent sites may be moved injectively, with
bounded or unbounded displacement near the defect, but must be translated rigidly far from it.

**Theorem B (one-letter split lifts).** Let `Q` be a finite set with `|Q| >= 2`, let
`B = (A \ {a0}) ⊔ ({a0} × Q)`, and let `r : B -> A` forget the `Q`-coordinate. Let `τ` be an injective automaton on
`A^G` and `Φ` an injective automaton on `B^G` with `r ∘ Φ = τ ∘ r`. Suppose the rest bit map is a translation with
relabelling: there are `s ∈ G` and a bijection `π` of `Q` with

    Φ((a0, z))(g s) = (a0, π(z(g)))          for all z ∈ Q^G and g ∈ G.

Then `τ` and `Φ` are both surjective. So neither is strict. In particular, a strict `τ` on `k` symbols admits no
lift of this kind to `k + |Q| - 1` symbols. Also, no strict automaton on `k + |Q| - 1` symbols arises this way over a
bijective `τ`.

**Consequences.**
- **The direct ascent `k -> k+1` by moving one extra bit dies.** Splitting one letter into two and carrying the bit
  along a local matching of `a0`-sites, or any design that copies the bit by a translation away from the defects and
  mixes arbitrarily near them, never gives a strict automaton. It dies at the count `|E(τ u)| <= |E(u)|`, which the
  transport forces, followed by charge noncreation.
- **Where a lift can survive.** A one-letter split lift that is strict needs a rest bit map `T_0 = Φ|_{a0 × Q^G}`
  that is an injective automaton on `Q^G` and not a relabelled translation. If `T_0` is not surjective, then
  `|Q| ∈ NS(G)` already, which for `|Q| = 2` is the binary witness of `some-nonsurjunctive-group-gives-a-binary-one`.
  So the only undecided one-letter split designs have a bijective, non-translation rest bit map. Splits of several
  letters (for instance the product lifts `τ × id`, which do give the multiples) are not covered: all split letters
  then carry zero charge, and charge noncreation needs a unique zero-charge symbol.
- **Scope.** The theorem is about lift designs. It does not decide `nonsurjunctive-alphabet-sizes-are-upward-closed`,
  since an ascent need not commute with any letter collapse.

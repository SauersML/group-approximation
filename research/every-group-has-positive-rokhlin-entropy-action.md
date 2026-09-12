---
rg: 2
id: every-group-has-positive-rokhlin-entropy-action
kind: claim
title: Every countably infinite group has a free ergodic p.m.p. action of positive Rokhlin entropy
root: true
distinct_from:
  gottschalk-surjunctivity-conjecture: that is surjunctivity of cellular automata; this is an entropy existence statement from which Seward's Krieger II derives surjunctivity, with no converse known.
  bernoulli-shift-entropy-classifies-for-every-group: that is the classification of Bernoulli shifts by base entropy; this is the positive-entropy hypothesis from which Seward derives the equality of Bernoulli Rokhlin entropy with base entropy.
refuted_by:
  - leavitt-unit-group-nonsurjunctive
---

**OPEN.** Every countably infinite group `G` admits a free ergodic
probability-measure-preserving action with positive Rokhlin entropy.

**Source.** B. Seward, *Krieger's finite generator theorem for actions of
countable groups II*, arXiv:1501.03367. The abstract, read on 2026-09-12:
"Under the assumption that every countable group admits a free ergodic action
of positive Rokhlin entropy, we prove that: (i) the Rokhlin entropy of a
Bernoulli shift is equal to the Shannon entropy of its base; (ii) Bernoulli
shifts have completely positive Rokhlin entropy; and (iii) Gottschalk's
surjunctivity conjecture and Kaplansky's direct finiteness conjecture are
true."

**Why it is a root.** One statement implies:
- `gottschalk-surjunctivity-conjecture`;
- Kaplansky direct finiteness, whose counterexample side is
  `leavitt-unit-group-algebra-not-directly-finite`;
- `bernoulli-shift-entropy-classifies-for-every-group`.

It can only fail on nonsofic groups. Seward, arXiv:1805.08279, introduction:
"The Rokhlin entropy of the Bernoulli shift G↷(L^G,λ^G) is H(L,λ) when G is
sofic but when G is not sofic its value is not yet known."

## Wiring

Read from the PDF of arXiv:1501.03367 on 2026-09-12. For a countably infinite
group `G`, Seward names three statements:
- **POS:** some free ergodic p.m.p. action of `G` has positive Rokhlin entropy;
- **INF:** `h^Rok_sup(G) = ∞`;
- **RBS:** `h^Rok_G(L^G, λ^G) = H(L, λ)` for every standard probability space
  `(L, λ)`.

The per-group implications INF ⟹ RBS ⟹ Gottschalk and Kaplansky direct
finiteness for `G` are recorded in
`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`. Seward, §1: "We do not
know whether POS implies INF." Theorem 1.11 makes the universal forms coincide:
"Let P be a countable group containing arbitrarily large finite subgroups. If G
is any countably infinite group with h^Rok_sup(G) < ∞ then h^Rok_sup(P × G) = 0.
Thus (∀G POS)⇒(∀G INF)." So this root is equivalent to ∀G INF, and hence to
∀G RBS.

Routes out of this claim:
- `every-group-positive-rokhlin-gives-leavitt-unit-case`, into
  `leavitt-unit-group-has-positive-rokhlin-entropy-action`;
- `every-group-positive-rokhlin-gives-tester-host-case`, into
  `tester-host-has-positive-rokhlin-entropy-action`. Composed with
  `positive-rokhlin-entropy-on-one-host-proves-gottschalk`, this gives
  Gottschalk's conjecture for every group.

On those hosts POS and INF coincide, by
`rokhlin-supremum-dichotomy-with-centralized-self-copies`.

## Refutation

`refuted_by: leavitt-unit-group-nonsurjunctive`. If `U = L_(F_2)(1,2)^×` is not
surjunctive:
- RBS(U) fails, by the contrapositive of Seward, Corollary 4.1 ("Assume that
  h^Rok_G(k^G, u^G_k) = log(k) for every k ∈ N. Then G satisfies Gottschalk's
  surjunctivity conjecture");
- so INF(U) fails, since INF ⟹ RBS for each group;
- so ∀G INF fails, and this root fails by Theorem 1.11.

The same chain refutes this root from any group that is not surjunctive,
including any group whose group algebra over a finite field is not stably
finite (`stable-finiteness-failure-refutes-surjunctivity`). Cairn fires
`refuted_by` only once the refuter is established.

Proving this root is therefore at least as hard as Gottschalk's conjecture for
all groups. A counterexample to Gottschalk or to Kaplansky direct finiteness
anywhere refutes it.

## Attempts

- **Origin.** The strategy lane `opportunity-mapper` opened this claim (item 1
  of `research/artifacts/opportunity-map-2026-09-12.md`). The lane
  `rokhlin-entropy` read the per-group statements and did the wiring above.
- **Host-level failure modes are recorded elsewhere.** Sofic entropy,
  restriction to sofic subgroups, co-induction and small free factors are on
  `leavitt-unit-group-has-positive-rokhlin-entropy-action`. A lower bound for
  one nonsofic host is at least as hard as that host's surjunctivity
  (`positive-rokhlin-entropy-makes-leavitt-units-surjunctive`).
- **Factor maps give no lower bound.** Bowen, arXiv:0812.2718, abstract: "if G
  is a countable group that contains a nonabelian free subgroup then every pair
  of nontrivial Bernoulli shifts over G are weakly isomorphic." Rokhlin entropy
  is not monotone under factors. Over the sofic group `F_2`, the 2-shift and the
  4-shift have Rokhlin entropy log 2 and log 4 (sofic entropy bounds Rokhlin
  entropy below and base entropy bounds it above), yet the 2-shift factors onto
  the 4-shift (Ornstein–Weiss). Weak isomorphism therefore transfers nothing.
- **Compression along a Kazhdan pair reaches only restrictions.** Let
  `G ↷ (X, μ)` be p.m.p., `Γ ≤ G` and `t ∈ G` with `tΓt^(-1) ≤ Γ`. The map
  `x ↦ t·x` intertwines the `Γ`-action with the `tΓt^(-1)`-action along
  `γ ↦ tγt^(-1)`, so `h_Γ(X) = h_(tΓt^(-1))(X)`.
  - For finite index `m = |Γ : tΓt^(-1)| ≥ 2`, Seward arXiv:1602.06680v2
    Lemma 8.1 gives only `h_(tΓt^(-1))(X) ≤ m·h_Γ(X)`, which is vacuous here.
  - The reverse inequality is the subgroup formula. §1 of that paper records it
    as a conjecture: "For non-amenable groups it is unknown, both for sofic and
    Rokhlin entropy". Lemma 8.3 proves it when almost every ergodic component
    splits into `m` components. Under the formula, `h_Γ(X) ∈ {0, ∞}`.
  - The Kun–Thom and Leavitt compressions have infinite index, and there nothing
    follows.
  - In every case `G`-level Rokhlin entropy is bounded only above by the entropy
    of an ergodic restriction, so these constraints do not reach POS.
- **The lamp-invariant factor gives no lower bound.** The Kun–Thom wreaths
  `W = (⊕_(G/Γ) Z/2) ⋊ G` have an infinite amenable normal subgroup `N` of
  lamps and a sofic quotient `G`. A lower bound
  `h^Rok_W(X) ≥ h^Rok_(W/N)(X_N)` through the `N`-invariant factor `X_N` fails
  already for amenable groups:
  - take `W = Z^2` and `N = Z × 0`;
  - take `Y` to be the 2-shift in the second coordinate, with `N` acting
    trivially, and `Z` a free Bernoulli `Z^2`-shift of base entropy `ε < log 2`;
  - then `X = Y × Z` is free and `X_N = Y` has `W/N`-entropy log 2;
  - but `h_W(X) = h_W(Y) + h_W(Z) = 0 + ε`.
  Soficity of the lamp quotient gives nothing through the invariant factor.
- **What is left.** A lower bound for any nonsofic group needs a counting
  mechanism that is not a sofic approximation. The sources read here
  (arXiv:1501.03367, 1602.06680, 1805.08279, 0812.2718) derive lower bounds only
  from sofic entropy or from amenability.

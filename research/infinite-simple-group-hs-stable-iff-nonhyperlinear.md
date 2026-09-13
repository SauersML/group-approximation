---
rg: 2
id: infinite-simple-group-hs-stable-iff-nonhyperlinear
kind: claim
title: An infinite simple group without finite-dimensional unitary representations is HS stable, strictly or flexibly, exactly when it is not hyperlinear
distinct_from:
  infinite-simple-group-permutation-stable-iff-nonsofic: that is the permutation-metric dichotomy for every infinite simple group; this is the Hilbert--Schmidt analogue, which needs the absence of finite-dimensional unitary representations and a projective-kernel step with no permutation counterpart.
  leavitt-unit-hs-stable-iff-nonhyperlinear: that proves the equivalence for the single finitely presented group L^x, through finite presentation; this proves it for every countably infinite simple group with no nontrivial finite-dimensional unitary representation, with no presentation.
  fp-simple-nonhyperlinearity-is-one-word-domination: that identifies nonhyperlinearity of a finitely presented infinite simple group with a quantitative one-word collapse modulus on relators; this is the qualitative pointwise stability equivalence for countable simple groups, with no finite presentation.
  hyperlinear-flexibly-hs-stable-group-is-residually-finite: that says a finitely generated hyperlinear flexibly HS-stable group is residually finite; this is the case of simple groups, where nonhyperlinearity alone already forces stability.
  pointwise-hs-stability-from-no-hyperlinear-quotient: that is the one-way implication for arbitrary groups; this is the two-way equivalence for simple groups, including the flexible notion.
artifacts:
  - research/artifacts/solve-hyperlinear-not-sofic-2026-09-13.md
---

**ESTABLISHED.** Let `S` be a countably infinite simple group such that every
homomorphism `S -> U(d)`, `d >= 1`, is trivial. Here `||.||_2` is the
normalized Hilbert--Schmidt norm, and an *asymptotic representation* is a
sequence `phi_n : S -> U(d_n)` with `||phi_n(gh) - phi_n(g) phi_n(h)||_2 -> 0`
for all `g, h`. The following are equivalent:

1. `S` is not hyperlinear.
2. Every asymptotic representation satisfies `||phi_n(g) - 1||_2 -> 0` for
   every `g ∈ S`.
3. For every free ultrafilter `omega` and every sequence `d_n`, every
   homomorphism `S -> U(prod_omega (M_(d_n), tr))` is trivial.
4. `S` is strictly HS stable: every asymptotic representation is pointwise
   `||.||_2`-asymptotic to genuine representations `rho_n : S -> U(d_n)`.
5. `S` is flexibly HS stable, in the Dogon--Vigdorovich sense: every asymptotic
   representation is pointwise asymptotic to corners `P_n lambda_n P_n` of
   genuine representations `lambda_n : S -> U(D_n)`, `D_n >= d_n`.

The correcting representations in 4 and 5 are always trivial. Moreover every
nontrivial homomorphism `pi` from `S` into the unitary group of a tracial von
Neumann algebra `(M, tau)` is injective, with `|tau(pi(g))| < 1` for all
`g != 1`. Proof: `infinite-simple-group-hs-stable-iff-nonhyperlinear-proof`.

**Consequences.**
- **Dichotomy.** Every such group is hyperlinear or HS stable, never both, and
  strict and flexible stability coincide for it.
- **Question 3.4 for simple groups.** Combined with
  `infinite-simple-group-permutation-stable-iff-nonsofic`, every countably
  infinite simple group is a hyperlinear nonsofic group exactly when it is
  permutation stable but not HS stable. No representation hypothesis is needed
  for this reading, because nonsofic simple groups satisfy it (Scope below). Equivalently, every almost action collapses to the identity, but
  some asymptotic representation does not collapse.
- **Firewall.** For such `S`, "prove HS stability, then conclude
  nonhyperlinearity" is a restatement of nonhyperlinearity, as on the
  permutation side. A stability route has to use a non-simple input.

**Scope of the hypothesis.** It is used only in 5 ⇒ 2. It holds for every
finitely generated infinite simple group: an injective finite-dimensional
unitary representation would make `S` a finitely generated linear group, hence
residually finite (`finitely-generated-linear-groups-are-residually-finite`),
which an infinite simple group is not. It also holds for every nonsofic
simple group: an injective `S -> U(d)` would make every finitely generated
subgroup residually finite, hence sofic, and soficity is determined by finitely
generated subgroups. Without the hypothesis, 1 ⇔ 2 ⇔ 3 and
2 ⇒ 4 ⇒ 5 still hold.

**Credit.** Elementary. The identity `tr(X ⊗ conj X) = |tr X|^2` is used the
same way in `research/artifacts/ex-q34-kt-wreath-soft-kernel-part4-2026-09-13.md`
and in the domination nodes. No priority is claimed.

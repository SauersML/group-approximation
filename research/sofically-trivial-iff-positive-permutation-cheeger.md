---
rg: 2
id: sofically-trivial-iff-positive-permutation-cheeger
kind: claim
title: A finitely presented group has no nontrivial sofic quotient iff its permutation Cheeger constant is positive iff it is permutation stable with no finite quotients
distinct_from:
  sofic-stable-implies-residually-finite: that is the one-way principle that sofic plus stable forces residual finiteness; this is an equivalence for groups with no nontrivial sofic quotient, with a linear rate, and it adds that for any flexibly stable finitely presented group the sofic radical equals the finite residual.
  thompson-v-sofic-iff-not-permutation-stable: that is the equivalence for Thompson's V, from simplicity and character rigidity; this is the presentation-level equivalence for every finitely presented group, stated for the sofic radical, with V as the simple instance.
  finite-quotient-caps-cocycle-cheeger-constant: that caps a cocycle Cheeger constant by finite quotients; this defines a group-level permutation Cheeger constant whose positivity is exactly sofic triviality.
  sofic-radical-soficization: that shows the sofic radical has sofic quotient and detects nonsoficity; this characterizes when the radical is the whole group, by a presentation-level Cheeger constant and by stability.
  binary-leavitt-unit-group-is-permutation-stable: that is one stable group; this characterizes when stability together with no finite quotients certifies that a group has no nontrivial sofic quotient.
---

**ESTABLISHED** through `sofically-trivial-iff-positive-permutation-cheeger-proof`.

## Definitions

Let `Q = <S | R>` with `S` and `R` finite and `S` nonempty. For a map
`sigma : S -> Sym(n)`:

- `sigma(w)` is the evaluated permutation of a word `w`;
- `e(pi)` is the fraction of points moved by a permutation `pi`;
- `supp(sigma)` is the fraction of points moved by at least one `sigma(s)`;
- `delta(sigma) = max_{r in R} e(sigma(r))` is the defect.

The **permutation Cheeger constant** is

```text
h(S|R) = inf { delta(sigma) : n >= 1, sigma : S -> Sym(n), supp(sigma) = 1 }.
```

This is the least defect of an almost-action with no global fixed point.

The **sofic radical** `Rad_sof(Q)` is the intersection of the kernels of all
homomorphisms from `Q` into sofic groups. Equivalently, it is the intersection
of the kernels of all homomorphisms into a universal sofic group `S_omega`.
Call `Q` **sofically trivial** when `Rad_sof(Q) = Q`.

## Theorem B

The following are equivalent.

- (a) `Q` is sofically trivial: it has no nontrivial sofic quotient.
- (e) Every homomorphism `Q -> S_omega` is trivial.
- (b) `h(S|R) > 0`.
- (c) `Q` is strictly permutation stable (Glebsky--Rivera,
  Arzhantseva--Paunescu) and has no nontrivial finite quotient.
- (d) `Q` is flexibly permutation stable (Becker--Lubotzky) and has no
  nontrivial finite quotient.

**Linear rate.** Under (b), for every `n`, every `sigma : S -> Sym(n)` and
every word `w` in `S`:

```text
e(sigma(w)) <= supp(sigma) <= delta(sigma) / h(S|R).
```

So every almost-action is within `delta / h` of the trivial action,
uniformly in `n`. In particular, positivity of `h` does not depend on the
finite presentation.

## Lemma C (sofic radical of a stable group)

If `G` is finitely presented and flexibly permutation stable, then
`Rad_sof(G) = Res(G)`, the finite residual.

This contains Glebsky--Rivera Proposition 3: if `G` is also sofic, then
`Res(G) = Rad_sof(G) = 1`. It also measures what a stability certificate for
nonsoficity certifies. For a flexibly stable `G`, a stability argument proves
nonsoficity exactly when `Res(G) != 1`, and the nonsofic part it detects is
exactly the finite residual.

## Calibration

- The free group `<a,b | >` has `h = 0`: any fixed-point-free action has
  defect 0.
- `Z/2 = <s | s^2>` has `h = 0`: take a fixed-point-free involution.
- The trivial group `<s | s>` has `h = 1`.
- Every group with a nontrivial finite quotient has `h = 0`.
- A simple infinite group `V` is sofically trivial iff it is not sofic. For
  Thompson's `V`, Theorem B recovers "V is nonsofic iff V is permutation
  stable" (`thompson-v-sofic-iff-not-permutation-stable`).
- Property (T) together with no finite quotients does **not** force `h > 0`,
  because sofic simple Kazhdan groups exist
  (`lef-kazhdan-group-without-finite-quotients-exists`).

No literature survey for novelty was done. Parts of Lemma C may be folklore.
Not Lean-verified.

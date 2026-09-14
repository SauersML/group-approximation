# The dihedral marker splits into two single-coset markers: a composition reduction

Lane `w4-dihedral-marker`, 2026-09-12. Family F (formalizability), verifier `w3-vf-nonlinear`.

The marker test object on Thompson's `V` was floated as the load-bearing test of stable
formalizability on a finitely generated simple host. This artifact shows it is **not independent**:
its stable formalizability, with full equivariance, follows from the *integer-marker* instance of
`injective-binary-automata-are-stably-formalizable`, which the regrouping work already studies over
`Z`. Everything is on paper.

## 0. Setup

- `D = <g, s | s^2, sgs = g^(-1)>` is infinite dihedral. `tau` on `{0,1}^D` flips cell `h` when
  `(x(hg^(-3)), x(hg^(-2)), x(hg^(-1)), x(hg), x(hg^2), x(hg^3)) = (0,0,1,1,0,0)`.
- Coset coordinates: `a(k) = x(g^k)`, `b(k) = x(g^k s)`. Left multiplication by `g` shifts both cosets
  by `+1`; left multiplication by `s` sends `g^k` to `g^(-k) s` and `g^k s` to `g^(-k)`, so `s` acts by
  `a(k) <-> b(-k)`.
- A formal pair `(E, Dec)` for an automaton is a pair of polynomial representatives over `F_2` with
  `Dec o E = id` as polynomials (all tracks recovered); `tau x id_m` adjoins `m` identity ancilla
  tracks.

## 1. The marker is two integer markers, one per coset

The window `{g^(±1), g^(±2), g^(±3)}` of a flip at `h` lies in the coset of `h`: if `h = g^k` then
`h g^j = g^(k+j)` (a-cells), and if `h = g^k s` then `h g^j = g^(k-j) s` (b-cells). So the a-flips read
only a-cells and the b-flips only b-cells. The pattern `(0,0,1,1,0,0)` is a palindrome, so under the
coset reflection `j -> -j` the b-rule is the same marker. Hence

> **Lemma 1.** `tau = tau_Z x tau_Z`: the integer marker `tau_Z` on the `a`-coset and the integer
> marker on the `b`-coset, with `s` exchanging the two copies through `a(k) <-> b(-k)`.

## 2. Formalizability is closed under composition

**Lemma 2.** If `(F_1, G_1)` and `(F_2, G_2)` are formal pairs, then `(F_2 o F_1, G_1 o G_2)` is a
formal pair for the composite automaton.

*Proof.* Polynomial substitution is functorial: `G_2(F_2(X)) = X` as polynomials gives
`G_2(F_2(P)) = P` for every tuple of polynomials `P`. So `G_1(G_2(F_2(F_1(X)))) = G_1(F_1(X)) = X`. ∎

## 3. The reduction

Factor, as automata on the two cosets, `tau = (tau_Z x id) o (id x tau_Z)`. The factors commute
functionally.

- `id x tau_Z` is the integer marker on the `b`-coset, with the `a`-coset left as identity. With `m`
  ancilla tracks it is exactly `tau_Z x id_m`, the integer-marker instance of
  `injective-binary-automata-are-stably-formalizable`. Assume a formal pair `(F_1, G_1)` for it whose
  representatives involve **only** the `b`-coset and an ancilla set `A1`. (Any formalization can be
  taken this way: it is a statement about a single `Z`-subsystem, so the other coset and the other
  ancillas need not appear.)
- Put `F_2 = s F_1 s`, `G_2 = s G_1 s`. Since `s (id x tau_Z) s = tau_Z x id`, this is a formal pair
  for `tau_Z x id` involving only the `a`-coset and the reflected ancilla set `A2 = s A1`.

By Lemma 2, `E = F_2 o F_1` with decoder `Dec = G_1 o G_2` formalizes `tau`.

> **Theorem 3.** `dihedral-marker-involution-is-stably-formalizable` follows from the integer-marker
> instance of `injective-binary-automata-are-stably-formalizable`.

## 4. The reflection symmetry is free

`F_1` touches only the variables `{b-coset, A1}` and `F_2` only `{a-coset, A2}`. These sets are
disjoint, so `F_1` and `F_2` commute as polynomial maps: applying one leaves the other's variables
untouched, and each factor's changed components depend only on its own variables. Hence

`s E s = s (F_2 o F_1) s = (s F_2 s) o (s F_1 s) = F_1 o F_2 = F_2 o F_1 = E`,

where `s` is extended to permute `A1 <-> A2`. Each factor is `<g>`-equivariant, so `E` is
`D`-equivariant with finite memory. This is full dihedral equivariance, **not** merely
`<g>`-equivariance.

This is the step regrouping cannot supply: regrouping `tau` along `<g^4>` formalizes it over `D` but
only `<g^4>`-equivariantly, so it does not induce to `V`. The composition construction is
`D`-equivariant and does induce.

## 5. Induction to V and scope

- **To V.** `<g, s> <= V` (the first-letter-swap dihedral pair). A `D`-equivariant formal pair pushes
  up to `V` with the same polynomials, because the formal identity at cell `1` reads only cells of
  `<g, s>`; the ancilla tracks, added over all of `V`, stay identity on their own cells
  (`thompson-v-marker-stable-formalizability-from-dihedral`). And `V <= L_(F_2)(1,2)^x`.
- **Stable, not plain.** The construction spends ancilla tracks, so it reaches the stable targets, not
  the plain ones. Stable formalizability already gives the Kaplansky payoff on simple hosts
  (`stable-formalization-reduces-surjunctivity-to-kaplansky`), so this loses nothing for the program.
- **Consequence.** The `V`-marker (and the dihedral marker) is not an independent test object for
  stable formalizability: it is downstream of the integer-marker warm-up. The only way this route
  leaves the marker failing on a simple host is if the integer marker itself is not stably
  formalizable. No such obstruction is known, and no unconditional construction of the integer-marker
  instance is known either (Attempts of `injective-binary-automata-are-stably-formalizable`).
- **What this does not give.** The marker is bijective, not strict. Passing the marker test object is
  consistent evidence for the stable-formalizability conjecture, not a proof of surjunctivity; the
  surjunctivity payoff needs stable formalizability of *strict* pairs plus Kaplansky.

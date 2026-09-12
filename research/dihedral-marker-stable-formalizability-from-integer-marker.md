---
rg: 2
id: dihedral-marker-stable-formalizability-from-integer-marker
kind: route
title: Split the dihedral marker into two single-coset markers and formalize each with a disjoint ancilla
target: dihedral-marker-involution-is-stably-formalizable
requires:
  - injective-binary-automata-are-stably-formalizable
artifacts:
  - research/artifacts/dihedral-marker-composition-reduction-2026-09-12.md
---

1. **Coordinates.** Over `D = <g, s>`, `{0,1}^D` splits into the cosets `a(k) = x(g^k)` and
   `b(k) = x(g^k s)`. The flip window `{g^(±1), g^(±2), g^(±3)}` stays in the coset of the flipped
   cell, and the pattern is a palindrome, so the marker is `tau_Z x tau_Z`: one integer marker per
   coset. `s` acts by `a(k) <-> b(-k)`.
2. **Factor.** `tau = (tau_Z x id) o (id x tau_Z)` as automata on the two cosets; the factors commute
   functionally.
3. **Formalize each factor.** `id x tau_Z` is the integer marker on the `b`-coset with the `a`-coset
   (plus ancilla tracks) left as identity: the instance of
   `injective-binary-automata-are-stably-formalizable` at `tau_Z` with `m` ancilla tracks. Take a
   formal pair `(F_1, G_1)` for it whose representatives involve only the `b`-coset and its ancilla set
   `A1`. Put `F_2 = s F_1 s`, `G_2 = s G_1 s`, a formal pair for `tau_Z x id` on the `a`-coset and the
   reflected ancilla set `A2 = s A1`.
4. **Compose.** `E = F_2 o F_1`, `Dec = G_1 o G_2`. Polynomial substitution is functorial, so
   `Dec o E = id` formally.
5. **D-equivariance.** `F_1` touches only `{b-coset, A1}` and `F_2` only `{a-coset, A2}`, disjoint
   variable sets, so the factors commute as polynomial maps and `s E s = F_1 o F_2 = E` (extending `s`
   to permute `A1 <-> A2`). Each factor is `<g>`-equivariant, so `E` is `D`-equivariant with finite
   memory. Hence `tau x id` over `D`, with ancilla set `A1 ∪ A2`, is formalizable.

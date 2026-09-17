---
rg: 2
id: dual-certificate-groups-force-large-host-dehn-functions
kind: claim
title: For every recursive function there is a finitely generated group with solvable word problem whose every finitely presented overgroup has Dehn function at least that function
distinct_from:
  dehn-function-bound-gives-word-problem-time-bound: that bounds the word-problem time of one finitely presented group by its Dehn function; this goes the other way, forcing a Dehn lower bound at every scale on every finitely presented group that contains a fixed hard subgroup.
  fp-simple-groups-with-arbitrarily-complex-word-problem: that asks for finitely presented simple groups with hard word problems; this is about Dehn functions of arbitrary finitely presented overgroups of one finitely generated group, and needs no simplicity.
  fp-simple-dehn-functions-realize-every-recursive-lower-bound: that is the open strong reading of Zaremsky 1.16 for simple groups; this is an unconditional statement about overgroups, which gives that claim once some finitely presented simple group contains the subgroup.
---

**ESTABLISHED.** Let `f: N -> N` be total recursive. There is a finitely
generated group `H_f` with 6 generators and solvable word problem such that every
finitely presented group `P` containing a subgroup isomorphic to `H_f` satisfies
`f ≼ delta_P`: some `K > 0` has `f(n) <= K delta_P(Kn) + Kn` for all `n >= 1`.

At `n = 0` every Dehn function vanishes, so the inequality `f(0) <= K delta_P(0)`
holds for no group once `f(0) > 0`. The restriction `n >= 1` is the intended
content of `≼`.

**Construction.** Take a recursive set `A ⊆ N` that every decision procedure
decides slowly on almost every input (`almost-everywhere-hard-recursive-sets-exist`,
with a time bound `F` computed from `f`). In `F(a, b)` put `x_i = b^i a b^(-i)`.
For `B ⊆ N` let `G_B = <a, b, t | t x_i t^(-1) = x_i, i in B>` and
`H_f = G_A * G_(N \ A)`. Then:

- `u_i = [t, x_i]` in the first factor is trivial iff `i ∈ A`;
- `v_i = [t', x'_i]` in the second factor is trivial iff `i ∉ A`;
- both words have length `4i + 4`.

So `H_f` carries a positive certificate for each of `i ∈ A` and `i ∉ A`. Exactly
one of the two short words is trivial.

**Why every overgroup has large Dehn function.** In a finitely presented `P ⊇ H_f`,
search in parallel for van Kampen expressions of both images, by increasing area.
The search needs no Dehn bound known in advance. It halts by area
`delta_P(8 lambda i)` and decides `A`. If `delta_P(8 lambda n) < f(n)` for
infinitely many `n`, the search is fast on infinitely many inputs, which
contradicts almost-everywhere hardness.

**Consequences.**

- Boone–Higman (`boone-higman-conjecture`) implies the strong reading of Zaremsky
  1.16 (route `fp-simple-large-dehn-via-boone-higman`).
- Contrapositive: a recursive `f` with no finitely presented simple `S` having
  `f ≼ delta_S` (`a-recursive-function-is-no-fp-simple-dehn-lower-bound`) would
  refute the Boone–Higman conjecture.
- The argument needs both certificates. With `u_i` alone, the area search halts
  only on inputs `i ∈ A`, so it does not decide `A`. The second free factor
  certifies non-membership, and that is what turns "fast on some inputs" into a
  contradiction.

Not checked against the literature. The ingredients (Rabin's almost-everywhere
hard sets, HNN extensions with Britton's lemma, van Kampen search) are
classical, and a folklore version may exist.

DERIVATION
dual-certificate-groups-force-large-host-dehn-functions-proof

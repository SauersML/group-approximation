---
rg: 2
id: fp-almost-v-groups-have-fp-germ-groups
kind: claim
title: Every finitely presented group between V and the almost-V group H has finitely presented isotropy germ groups at every point, however its finite presentation is proved
distinct_from:
  shell-envelope-fp-forces-fp-germ-group: that proves the same implication for shell envelopes E_nu at their one singular orbit; this proves it for every finitely presented group of Cantor homeomorphisms that contains V and has finite V-singular sets, at every point.
  bhm-singfix-condition-forces-fp-germ-groups: that shows the hypothesis of Belk--Hyde--Matucci Theorem 2.1 forces finitely presented singular germ groups, and says nothing about finite presentation proved by other means; this shows finite presentation itself forces them, by any proof.
  shell-fp-stabilizer-forces-fp-germ-group: that derives a finitely presented germ group from a finitely presented one-point stabilizer; this needs only the whole group finitely presented.
---

**ESTABLISHED** by `fp-almost-v-groups-fp-germ-groups-proof` (lane proof, elementary; the
mechanism is that of `shell-envelope-fp-forces-fp-germ-group-proof`, extended from shells
to all almost-V groups; not independently reviewed; no novelty claimed).

**Setting.** `V` acts on `C = {0,1}^N`. A homeomorphism `g` of `C` is V-local at `x` if it
agrees near `x` with an element of `V`, and `sing(g)` is the set of points where it is not.
`H = {g in Homeo(C) : sing(g) finite}`, as in
`almost-v-fw-subgroups-act-through-finitely-many-germs`. Every finite germ extension of `V` in
the sense of Belk--Hyde--Matucci lies in `H`. For `E <= Homeo(C)` and `p in C`, `(E)_p` is
the group of germs at `p` of the elements of `E` fixing `p`.

**Theorem.** Let `V <= E <= H`. If `E` is finitely presented, then `(E)_p` is finitely
presented for every `p in C`. More precisely, write `E = <Y ∪ Z | R>` with `Y` a finite
generating set of `V`, `Z` finite and `R` finite. Then `(E)_p` is the quotient of a free
product of at most finitely many infinite cyclic groups by the normal closure of finitely
many words, one for each pair `(r, x)` in which the relator `r`, read from the point `x`,
applies a letter of `Z^±` at one of its singular points.

## Consequences

1. **No compensation.** A finitely presented host between `V` and `H` cannot carry an input in
   germ groups that are not finitely presented. Together with
   `simple-kazhdan-in-germ-extension-of-v-sits-in-one-germ-group` and
   `deligne-lattice-in-almost-v-sits-in-one-germ-group`, whose germ statements hold in any
   `E <= H`:
   - an infinite simple Kazhdan subgroup of any finitely presented `E` with `V <= E <= H` lies
     in a single finitely presented singular germ group of `E`;
   - so does a finite-index subgroup of the Deligne lattice, center included.

   This holds whether or not Theorem 2.1 of Belk--Hyde--Matucci is used.
2. **Grigorchuk groups.** For `ω` not eventually periodic, the germ group of
   `E_ω = <V, b_ω, c_ω, d_ω>` is not finitely presented
   (`grigorchuk-groups-lie-in-one-point-germ-extensions-of-v`, item 3). So `E_ω` itself is
   not finitely presented, by any method, which strengthens item 4 there.
3. **Shells.** This reproves `shell-envelope-fp-forces-fp-germ-group` and extends it to
   genuine-action shells, multi-point shells and every other construction inside `H`. So
   the germ gates of `shell-germ-fp-is-an-ascending-hnn-gate` are necessary for finite
   presentation of any such host.

## Scope

- Only `V <= E <= H` and finite presentation of `E` are used. No finite germ extension axiom
  beyond finiteness of singular sets, and no finiteness property of point stabilizers.
- The converse is false in general, since germ groups say nothing about how the singular
  orbit is assembled. It is not claimed.
- The base is the binary `V`. The proof uses only that `V`-orbits are dense and that two points
  of one `V`-orbit in an open set `U` are exchanged by an element of `V` supported in `U`, so it
  transfers to `V_(d,r)`.

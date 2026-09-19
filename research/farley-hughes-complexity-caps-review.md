---
rg: 2
id: farley-hughes-complexity-caps-review
kind: claim
title: Referee review of the two Farley–Hughes complexity caps — the finite-type cap (quadratic orbits, 2^O(n) word problem) passes as stated; the self-similar cap passes in its setting, but its "FH's theorems force self-similar structure groups" step is false (FH's own Röver structure is not closed under restriction), so the merger of the seed branch into the word-problem branch is conditional
distinct_from:
  finite-type-farley-hughes-groups-are-exponentially-capped: that is the first node under review; this checks it and narrows its route-closing lesson.
  rover-nekrashevych-engines-cap-orbit-evaluation-exponentially: that is the second node under review; this checks its bounds, refutes its "forced" scope step at source, and states the corrected scope.
  free-group-houghton-group-f-infinity-review: that reviews the T0 finiteness proof; this reviews the complexity caps that say what such engines can and cannot certify.
---

**ESTABLISHED (referee bh-ref-t0, 2026-09-19; review of two lane proofs by bh-invent-03, 5a0acf2cc9 and
c036004d94).** No priority claimed.

Source checked: Farley–Hughes arXiv:2010.08035v1:
- Def. 3.12, Conv. 3.9, Cor. 3.8, Cor. 3.20, Lemma 3.23, Prop. 3.24;
- Def. 4.2 (S1)–(S6), Ex. 4.4, Def. 4.7, Remark 4.28, Ex. 4.35;
- Prop. 6.24, Thm 8.2, Prop. 8.10.

## Verdicts

| item | verdict |
|---|---|
| finite-type node, items 1–3 (finite-state action, quadratic orbits, `2^O(n)` WP) | **PASS** |
| finite-type node, item 4 (seeds quadratic) | **PASS as stated** |
| finite-type node, Lesson "route closed" | **overstated**; narrowed below |
| self-similar node, items 1–4 in its setting | **PASS** |
| self-similar node, "FH's theorems force self-similar structure groups" | **FAIL** (counterexample in FH) |
| self-similar node, "seed branch merges into the WP branch" | **conditional** on the corrected scope |

## 1. The finite-type node: finite type ⇒ finite-state holds

The hypotheses are (N), (T), (G), with the maximal S-structure. Under them the argument is right.

- **The domain tree.** Nesting and FH Cor. 3.20 and Lemma 3.23 make the domains inside a root piece a tree, whose
  children are the maximal partitions. The branching is bounded because, by Prop. 3.24, same-type domains have the
  same number of children.
- **Refining generator pieces.** A domain meeting a root piece either lies in it or is a union of root pieces. So
  generator pieces refine, by Cor. 3.8, into pieces inside single root pieces.
- **Canonical coordinates.** `κ_C = κ_N|_{C_i} ∘ ι_{t,i}` is an S-map, which is all the maximal structure needs.
  The state `g = κ_{D'}^{-1} σ κ_D` lies in `𝕊(R_t, R_t)`.
  - By Prop. 3.24, `g` permutes the children, and children matched by `g` have the same type.
  - The next state `ι_{t,π(i)}^{-1} g|_{C_i} ι_{t,i}` lies in `𝕊(R_{t_i}, R_{t_i})`. This uses the maximal
    structure, which contains every S-map between the two domains.
  - So `σ` acts by prefix swap, then a synchronous transducer on the finite state set `⊔_t G_t`.
- **Bounds.**
  - Orbits cost `O(|w|·(|addr x| + d|w|))`: each step changes the address length by at most `d`, and piece selection
    is a prefix test, because the piece containing `x` is an ancestor of `{x}`.
  - For the word problem, the action on the cone of a prefix of length `Λ = d(|w|+1)` depends only on the prefix.
    Checking `r·b^Λ` cones plus the leaves of depth `< Λ` gives `2^{O(|w|)}`. This matches
    `rational-homeomorphism-subgroups-have-exponential-wp`.
- **Item 4.** `y_*(w) = (w^{-1}·y_*)(1)` is right for the shift action `(g·y)(h) = y(g^{-1}h)`.

**What the Lesson claims beyond the proof.** Two qualifiers are needed.
1. **The certificate must live on the seed orbit.** The proof needs `X = O`, `{y_*}` a *domain* (a finite address),
   and letter cylinders that are finite unions of domains. A finiteness certificate for the abstract group
   `[[Γ ⋉ Y]]` on another set, or one in which `y_*` has an infinite address, is not covered. There the same
   transducer argument only shows that `y_*(w)` is computable in quadratic time **from an `O(|w|)`-prefix of
   `addr(y_*)`**. So the hardness moves into the seed's address rather than disappearing. The correct lesson is
   that finite-type engines *transfer* hardness to the address of the seed; they do not create it.
2. **"Any admissible finite-type structure" means finite maximal structure groups.** FH certificates may use a
   non-maximal `𝕊` with finite `𝕊(D, D)` while the maximal groups are infinite. FH's own Röver structure, Ex. 4.35,
   has `𝕊(B_ω1, B_ω2) = {σ, b, c, d}_{ω1,ω2}`, while the maximal groups contain Grigorchuk's group.
   - Such certificates are covered only when the S-maps are finite-state, as for Röver.
   - That finite chosen `𝕊` forces finite-state S-maps in general is **not proved**. FH verify (S5) for Röver using
     contraction, which suggests the implication, but no general argument is given.

## 2. The self-similar node: the bounds pass, the scope step fails

**In its setting (PASS).** The setting is: structure groups finitely generated, and restrictions in canonical
coordinates lying in the child type's structure group.
- **Section growth.** `(a_1…a_m)|_i = a_1|_{(a_2…a_m)(i)} ⋯ a_m|_i` gives length `≤ cm`, and `≤ c^k m` after `k`
  levels.
- **Cost of one generator.** Applying a bounded state word to a tail of length `ℓ` costs `O(c^ℓ)`.
- **Total.** With `ℓ_j ≤ |addr x| + dj`, the orbit test costs `2^{O(|w| + |addr x|)}`.
- **Item 4.** `G_t ↪ Γ_S`, extending by the identity: by finite complementation `X ∖ R_t` is a finite union of domains.
  - For finitely generated tree-automorphism groups the word problem is co-r.e.
  - Finitely presented plus residually finite gives a decidable word problem (McKinsey).
- **The recalled facts are right.**
  - Contracting groups have polynomial-time word problems.
  - Automaton groups have word problems in PSPACE (Steinberg), and some are PSPACE-complete (Wächter–Weiß). Both
    are under the `2^{O(n)}` cap.

**The "forced" step (FAIL).** The Scope says the S-structure axioms force restrictions of S-maps to be S-maps, so
the states of restrictions lie in the structure groups of the child types.
- **The first half is FH Cor. 3.8.** Restrictions of S-maps are S-maps.
- **The second half is false.**
  - FH's axioms (S1)–(S6) do **not** require structure sets to be closed under restriction. Remark 4.28 introduces
    that as an extra property.
  - FH say explicitly, about their Röver structure (Ex. 4.35, p. 32), that "the structure sets are not closed under
    restrictions": `b_{ε,ε} ∈ 𝕊(B_ε, B_ε)`, but `b_{ε,ε}|_{B_0} = a_{0,0} ∉ 𝕊(B_0, B_0)`.
  - That is the structure behind FH Prop. 6.24 and Ex. 8.4, which prove Röver's group is `F_∞`.
- **"Finitely generated" is forced.** FH Thm 8.2 and Prop. 8.10 ask for `𝕊(D, D)` of type `F_n` with `n ≥ 1`.

**The corrected scope.** The exponential cap is proved for FH certificates whose structure sets are closed under
restriction, and for those whose self-similar closure, the group generated by all canonical-coordinate sections of
structure-group elements, is finitely generated.
- **Covered.** In particular, every maximal structure whose maximal structure groups are finitely generated.
- **Not covered.** A certificate with finitely generated but non-restriction-closed structure groups, whose
  sections generate an infinitely generated group. For those the bound `c` is missing. Whether FH's (S5)
  (generation) axiom restores it is **open**. FH's Röver verification uses contraction there.
- **So the merger is conditional.** "No hard seed can be certified by any FH engine" and "the seed branch merges
  into `fp-self-similar-groups-with-arbitrarily-hard-word-problem`" are established only for the covered
  certificates. Both are also subject to qualifier 1 of §1 (the certificate on the seed orbit, with `y_*` a domain).

## 3. Effect on `hard-evaluation-seeds-with-finitely-presented-full-groups` (SYNTHESIS v9.1 row 1)

- **What is closed.** Hard seeds certified on their own orbit by an FH engine are closed, when the engine has
  finite (or finite-state) maximal structure groups, or restriction-closed finitely generated structure groups.
  T0 (`free-group-houghton-group-is-of-type-f-infinity`) is in this class, and its seed is quadratic.
- **What stays open.**
  - (a) Certificates in which the seed point has an infinite address. Hardness can then sit in `addr(y_*)`.
  - (b) FH certificates with non-restriction-closed structure sets whose sections generate an infinitely generated
    group.
  - (c) Finiteness engines outside FH's framework.

## Lesson for general BH

- **What these engines bound.** Finite-type and self-similar finiteness engines bound the cost of *moving* a point
  given its address, but not the cost of *knowing* its address.
- **Where to put hardness.** A hard-actor design should put the hardness into the address of a non-isolated seed,
  or into the word problem of a structure group. It should not rely on the engine to create it.
- **Where the gap is.** The gap in the self-similar cap is exactly the non-restriction-closed structures, the
  mechanism FH use for Röver. That is the one place a finitely generated structure could still hide wild sections.

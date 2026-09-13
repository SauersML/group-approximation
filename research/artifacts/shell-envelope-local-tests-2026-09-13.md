# Local finite-presentation tests for shell envelopes, 2026-09-13

Lane `solve-bh-shell-envelopes`. Targets: `decidable-inputs-have-fp-shell-envelopes`
and `boone-higman-via-shell-stabilizer-overgroups`, both OPEN.

## Verdict

- **Zaremsky's Proposition 3.1 gives no new condition on the enumeration.**
  On the Belk–Hyde–Matucci germ complex, the complex built from finite
  singular configurations, every cell stabilizer is already finitely
  generated, so the bad-edge criterion collapses to the classical one: finite
  presentation of the vertex stabilizers `S(M,M')`, `|M'| <= 2`. That is the
  existing three-stabilizer hypothesis `decidable-inputs-have-fp-shell-stabilizers`.
- **The cheaper germ corollary of Belk–Hyde–Matucci never applies** to
  inputs that are not virtually cyclic (`shell-isotropy-germs-fail-bhm-germ-hypothesis`).
- **Removing the free-near-shift obstruction is cheap.** Every route input
  `P_0 x Z` has computable enumerations with a mixed near relation, and the
  other generators stay unconstrained
  (`route-form-shell-inputs-have-computable-mixed-near-relations`).
- **What is still missing:** finite presentation of any `S(M,M')`, for any
  enumeration, when the input is not virtually cyclic.

## 1. Sources pinned

Both papers were fetched on MSI, copied locally, and the text was extracted
with `pdftotext -layout`.

**Zaremsky, arXiv:2405.18354v2 (November 27, 2024).**
- **Proposition 3.1:** "Let K be a simply connected simplicial complex and Γ
  a group with an orientation preserving, cocompact action on K, such that
  every vertex stabilizer Γv is finitely presented. Suppose that for each edge
  e = {v, w}, there exists an edge path e1, . . . , en from v to w such that
  each stabilizer Γei is finitely generated, and the subgroup ∩ Γei of Γe has
  finite index. Then Γ is finitely presented."
- **The proof** rewrites the edge relations R(f, g), for g in the finite-index
  path fixer, through the triangle relations along the path. Only finitely
  many coset representatives of the path fixer need their own edge relations.
- **Lemma 4.9 (Long edge stabilizers):** "Let v < w be a long edge. Then
  there is a path of short edges from v to w such that the fixer in SVG of
  this path has finite index in the stabilizer of v < w." The remark after it
  says the path fixer is an intersection of finitely generated groups and need
  not be finitely generated, which is why Proposition 3.1 is needed.
- **Corollary 5.11:** "Let H be a finitely generated simple subgroup of a
  finitely presented group G, and assume H is not normal in G. If there are
  finitely many double cosets in H\G/H, then G admits an action of type (A),
  and hence satisfies the (permutational) Boone–Higman conjecture."

**Belk–Hyde–Matucci, arXiv:2407.03149.**
- **Definition (finite germ extension of B):**
  1. every element of G has finitely many singular points;
  2. B is exactly the subgroup of elements with no singular points;
  3. every singular germ is realized by an element with one singular point.
- **Theorem 2.1:** "Let X be Hausdorff space, and let G be a finite germ
  extension of some B ≤ Homeo(X). Let n ≥ 1, and suppose that: (1) The induced
  action of B on sing(G)^n has finitely many orbits, and (2) For every pair
  M ⊆ M′ of subsets of sing(G) with 0 ≤ |M′| ≤ n, the group SingFixG(M, M′) :=
  {g ∈ G | sing(g) ⊆ M and g|M′ = id} has type Fn. Then G has type Fn."
- **Proof of Theorem 2.1:** it uses the germ complex K, a product of trees.
  Cube stabilizers in the sublevel complex are conjugate to groups
  SingFixG(M, M′) with |M′| ≤ n.
- **Corollary 2.10** (Theorem 1.1 is its F∞ case), hypothesis (3): "Either
  |(G)p : (B)p| < ∞ for each p ∈ sing(G), or (B)p E (G)p for each p ∈ sing(G)
  and (G)p/(B)p has type Fn." Propositions 2.8 and 2.9 derive the SingFix
  finiteness from that hypothesis.

## 2. Step 1: the Proposition 3.1 test in the shell setting

**(a) Bad enumerations fail automatically.** Proposition 3.1 is a sufficient
condition. When `E_nu` is not finitely presented, as for the computable
free-product enumerations of `decidable-inputs-have-computable-non-fp-shell-envelopes`,
no action of `E_nu` on any complex can meet its hypotheses. So "tracking finite
presentation" can only mean positive certification of good enumerations.

**(b) On configuration complexes the bad-edge relaxation is vacuous.**
- **Setting.** `E_nu` is a finite germ extension of V
  (`shell-cantor-embeddings-are-finite-germ-extensions`). On the germ complex,
  and on any complex whose cells are stabilized by stabilizers of finite
  singular configurations, each cell stabilizer is conjugate to some
  `S(M,M') = SingFix(M,M')`, or contains one with finite index.
- **Every edge is good.** `shell-finite-point-stabilizers-are-finitely-generated`
  makes every `S(M,M')` and every pointwise stabilizer `E_F` finitely generated,
  for every enumeration and every finitely generated input. A setwise stabilizer
  of a finite set contains the pointwise one with finite index, so it is
  finitely generated too. Each edge is therefore its own one-edge repair path
  (n = 1 in Proposition 3.1).
- **What remains.** The criterion reduces to the classical Brown–Armstrong
  statement: finite presentation of the vertex stabilizers, which are the
  groups `S(M,M')` with `|M'| <= 2`.

**(c) This is exactly the three-stabilizer hypothesis.**
- **Orbit condition.** Take `p = 0^infinity` and `q = 1*0^infinity`. V acts
  highly transitively on the orbit `Omega = V*p`, so condition (1) of Theorem
  2.1 holds for n = 2. The singularity-free groups `S(∅,M')` are stabilizers in
  V of finite sets of rational points. Belk–Hyde–Matucci's Appendix A verifies
  type F∞ for those; this was seen in their introduction, and the appendix was
  not re-read.
- **Remaining clauses.** Up to V-conjugacy they are `A_1 = S({p},{p})`,
  `A_12 = S({p},{p,q})` and `A_2 = S({p,q},{p,q})`. The pair `S({q},{p,q})` is
  conjugate to `A_12`.
- **Conclusion.** Proposition 3.1 on these complexes gives the same local
  condition on `nu` as `decidable-inputs-have-fp-shell-stabilizers`, and nothing
  weaker.
- **Where Proposition 3.1 could still help.** Only on a cocompact
  simply connected `E_nu`-complex with infinitely generated edge stabilizers.
  Its cells cannot be stabilized by finite singular configurations; one
  candidate is cells built from infinite clopen data around the singular orbit.
  No such complex is known.

## 3. Step 2: the germ corollary is unavailable

The claim `shell-isotropy-germs-fail-bhm-germ-hypothesis` gives the proof.
With `(G)_p = Q = <germs of rho(P), tau>` and `(B)_p = <tau>`:
- **Not normal, for every infinite input.** The near-permutation index forces
  any conjugate of `tau` lying in `<tau>` to be `tau` itself. A germ of
  `rho_g` commuting with `tau` fixes all large odd numbers, hence all large
  numbers, so it is trivial.
- **Not of finite index, for inputs that aren't virtually cyclic.** Germ
  faithfulness puts `P` inside `Q`.

So Corollary 2.10 cannot certify any shell envelope of an input that is not
virtually cyclic. The virtually cyclic positive control
(`finite-ray-regular-orbit-classification-proof`) lives exactly in the
finite-index regime. For all other inputs, finite presentation has to come from
finite presentation of `A_1`, `A_12` and `A_2` themselves.

## 4. Step 3: mixed near relations do not bound complexity

- **Why this matters.** `free-shift-shell-envelopes-are-not-finitely-presented`
  shows any successful enumeration needs a mixed near relation.
  `arithmetic-near-shift-actions-have-mixed-relations` supplies one from
  eventually residue-affine regular permutations. The lane `bh-fp-criterion`
  (idea A5) noted that groups generated entirely by such permutations have
  exponentially bounded word problems, so they can't carry hard inputs.
- **What the new claim shows.** The relation needs only ONE generator.
  `route-form-shell-inputs-have-computable-mixed-near-relations` realizes the
  central factor `t` of `P = P_0 x Z` by an explicit free residue-affine
  permutation `lambda'`. Its orbits are indexed by `3 + 4N`, and it gives
  `[lambda_t s^4 lambda_t^-1, s^8] = 1`. The generators of `P_0` act through an
  arbitrary computable bijection `beta: P_0 -> 3 + 4N`, so their germs carry
  `P_0`'s full word problem. The bounded-complexity constraint of idea A5 applies
  to fully arithmetic actions, not to this mixed shape.
- **Consequence for the route.** `boone-higman-via-fp-shell-envelopes` already
  uses inputs `P_0 x Z`. The free-near-shift obstruction is removed computably,
  and hardness is never capped.
- **What is open.** Whether some enumeration of this shape, or any other, makes
  `A_1`, `A_12` and `A_2` finitely presented.

## 5. Verification boundary

- **Proofs.** The proofs of both new claims are written in their routes. Each
  imports one established claim from main.
- **No computation.** None was needed. The orbit analysis of `lambda'` is by
  hand.
- **Cairn.** `cairn why` / `cairn check` run on MSI against a snapshot of
  origin/main.
- **Finite-bi-index route.** `boone-higman-via-shell-stabilizer-overgroups`
  is untouched by these results. It needs a host of finite bi-index, which
  Corollary 5.11 recasts in published form. Recorded obstructions to that are
  on main (`shell-finite-biindex-hosts-require-large-intersections`), and
  nothing here changes them.

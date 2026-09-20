---
rg: 2
id: f-exotic-co-amenable-route-is-amenability-plus-not-brin-sapir
kind: claim
title: "For every family S of subgroups of F, 'some member of S is co-amenable' and 'every member of S is amenable' hold together iff F is amenable and S is nonempty; so the exotic co-amenable route is exactly amenability of F plus failure of Brin–Sapir, and under amenability P1 is equivalent to the failure of Brin–Sapir"
distinct_from:
  f-sandwich-splits-collapse-unless-kernel-is-brin-sapir-exotic: that classifies splits with one fixed kernel K and shows each collapses unless K is Brin–Sapir exotic; this treats the existential-over-K packaging used by the exotic route and computes its conjunction exactly as A ∧ (S nonempty).
  f-has-a-co-amenable-subgroup-neither-ea-nor-containing-f: that is P1 itself; this shows that P1 ∧ P2 ⟺ A ∧ ¬BS and that, given A, P1 ⟺ ¬BS.
  some-subgroup-of-thompson-f-is-neither-ea-nor-contains-f: that is ¬BS as a standalone claim; this shows that the exotic route is equivalent to it together with A.
  every-f-free-subgroup-of-thompson-f-is-amenable: that is P2; this shows that P2 adds nothing over A, and that the route's content over A is exactly ¬BS.
  thompson-f-interval-stabilizer-cosets-separate-only-if-amenable: that proves the implication "amenable co-amenable subgroup gives A" (item 3), used here as the only nontrivial input.
---

**ESTABLISHED** (lane proof, not reviewed) by
`f-exotic-co-amenable-route-amenability-plus-not-bs-proof`.

**Notation.**
- `A` is "`F` is amenable" (`thompson-f-is-amenable`).
- `BS` is the Brin–Sapir conjecture `every-subgroup-of-thompson-f-is-ea-or-contains-f`.
  `¬BS` is `some-subgroup-of-thompson-f-is-neither-ea-nor-contains-f`.
- For a set `S` of subgroups of `F`:
  - `E(S)` means `S ≠ ∅`;
  - `C(S)` means some `K ∈ S` has an `F`-invariant mean on `F/K`;
  - `M(S)` means every `K ∈ S` is amenable.
- `X` is the set of *Brin–Sapir exotic* subgroups of `F`: those with no subgroup isomorphic to `F`
  that are not elementary amenable. So `E(X) = ¬BS`.
- `P1 = f-has-a-co-amenable-subgroup-neither-ea-nor-containing-f`, which is `C(X)`.
- `P2 = every-f-free-subgroup-of-thompson-f-is-amenable`.

**Theorem.**
1. **(Class-quantified splits.)** For every set `S` of subgroups of `F`,
   `C(S) ∧ M(S) ⟺ A ∧ E(S)`.
2. **(P2 is `M(X)`.)** `P2 ⟺ M(X)`.
3. **(The exotic route, exactly.)** `P1 ∧ P2 ⟺ A ∧ ¬BS`.
4. **(P1 relative to A.)** If `A` holds, then `P1 ⟺ ¬BS`, and `P2` holds.
5. **(The route dies under Brin–Sapir.)** If `BS` holds, then `P1` is false, whether or not `A` holds.
   So `thompson-f-amenable-via-exotic-co-amenable-subgroup` can be completed only in a world where
   the Brin–Sapir conjecture is false.
6. **(Dichotomy for the whole class.)** If `E(S)` is known, then `C(S) ∧ M(S) ⟺ A`, so the split is a
   reformulation of the root. If `E(S)` is not known, then the split is the root together with the
   existence statement `E(S)`. In that case its two prerequisites "fail independently" only because
   `E(S)` can fail while `A` holds: the route is then not necessary for the target.

**Correction to the route node.** `thompson-f-amenable-via-exotic-co-amenable-subgroup` says that
"each prerequisite is weaker than the target on its own". That is true of `P2`, since `A ⇒ P2`. It is
not known for `P1`: by item 4, `A ⇒ P1` holds iff `A ⇒ ¬BS`, and that is open. In the believed world
(`BS` true), `P1` is false even if `A` is true. So `P1` is not a weakening of the target. It is an
independent assertion, the failure of Brin–Sapir, packaged with a co-amenability witness.

**Class killed.**
- *Class:* routes to `A` of the form `C(S) ∧ M(S)`, meaning "some subgroup from a family is
  co-amenable" and "every subgroup in the family is amenable", for any family `S` defined by a
  subgroup property. This includes the exotic route (`S = X`) and every variant that shrinks or
  enlarges `X` (for example "F-free", "F-free and finitely generated", or "exotic and unconfined").
- *Invariant:* the existence statement `E(S)`.
- *Dying step:* the existential prerequisite `C(S)`.
  - If `E(S)` is provable, `C(S) ∧ M(S)` is root-equivalent. For example, the family of F-free subgroups
    contains `{e}`, and the family of all subgroups contains `F`.
  - If `E(S)` is unknown, completing the route also proves `E(S)`. For `S ⊆ X` this is a refutation of
    the Brin–Sapir conjecture.
- *Combined with the sandwich claim* (item 4 there: "Under the Brin–Sapir conjecture every datum
  collapses"): every co-amenable-induction split of `A`, whether it names one kernel or quantifies
  over a family, is root-equivalent or proves `¬BS`. No member of the class is a decomposition of `A`
  that is neutral about Brin–Sapir.

**What survives.** A decomposition of `A` whose prerequisites can each fail independently, and which
does not prove `¬BS`, must leave co-amenable induction entirely. It must also leave (T1) twisted
embeddings, by the same sandwich claim. On 2026-09-20 the frontier of `thompson-f-is-amenable` has three
leaves:
- `f-has-a-co-amenable-subgroup-neither-ea-nor-containing-f` (P1), which proves `¬BS`;
- `every-f-free-subgroup-of-thompson-f-is-amenable` (P2), which adds nothing over `A` (item 4);
- `f-dyadic-inverted-orbit-is-subballistic-on-rare-events`, which is equivalent to the root by
  `f-dyadic-ea-iff-inverted-orbit-confinement` and `thompson-f-amenable-iff-dyadic-action-extensively-amenable`
  (the breakpoint cocycle, kernel `{e}`, item 3 of the sandwich claim).

So every open leaf toward the goal is either root-equivalent or proves `¬BS`. The frontier has no
leaf that is strictly weaker than the root and neutral about Brin–Sapir.

**Scope.** The proof is elementary, and no novelty is claimed for item 1. The point is bookkeeping with
consequences: the exotic route has been listed as the one uncollapsed split, and this shows that it is
uncollapsed only because it carries the extra, disbelieved conjunct `¬BS`.

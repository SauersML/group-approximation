---
rg: 2
id: fp-relatively-simple-pair-with-unsolvable-simple-quotient
kind: claim
title: Some finitely presented relatively simple group has a simple quotient with unsolvable word problem, so it sharply embeds in no finitely presented relatively simple pair with finitely normally generated largest normal subgroup
distinct_from:
  fp-relatively-simple-pairs-embed-with-fng-kernels: that is the second part of FFWZ Question 5.9, the universal removal assertion; this is its negation, and that node names this one in refuted_by.
  some-a2-action-has-a-nonrecursive-kernel: that is the action-level statement; this transfers it to relatively simple groups through the abstract twisted Brin--Thompson construction.
  relatively-simple-removal-between-pbh-and-bh-of-quotient: that proves one relatively simple pair is removable only when its simple quotient embeds in a finitely presented simple group; this exhibits a pair whose simple quotient cannot, because its word problem is unsolvable.
---

**ESTABLISHED** by the proof below. Lane proof by bh-ffwz-q59, 2026-09-18. One referee PASS (bh-ref-ffwz, see Referee below; the SV_P finite-presentation condition is discharged). It is not
reviewed and no priority is claimed. It depends on the lane proof
`nonrecursive-a2-kernel-from-abstract-rover-nekrashevych-groups`.

## Statement

There is a finitely presented group `H` with a proper normal subgroup `M` such that:
1. `(H, M)` is relatively simple: every proper normal subgroup of `H` lies in `M`, so `H/M`
   is the unique simple quotient of `H`;
2. `H/M` has unsolvable word problem;
3. `(H, M)` sharply embeds in no finitely presented relatively simple pair `(H', M')` with
   `M'` finitely normally generated in `H'`.

So the second part of Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, Question 5.9, has
answer **no**. It is quoted in `fp-relatively-simple-pairs-embed-with-fng-kernels`.

## Proof

Let `P ↷ Ω` be a type `[A_2]` action with non-recursive kernel `K`
(`some-a2-action-has-a-nonrecursive-kernel`). Put `H = SV_P`, the abstract twisted
Brin--Thompson group of `P ↷ Ω` (FFWZ Definition 2.12), and let `M = SK_P` be its canonical
kernel.

- **Finite presentation.** `H` is finitely presented, by `abstract-twisted-bt-type-fn-criterion`
  item 2. That is the non-faithful case, proved on main by a route that avoids the gap in
  FFWZ's proof.
- **Relative simplicity.** FFWZ Theorem 3.6 (Theorem A) says every proper normal subgroup of
  `SV_P` lies in `SK_P`, imported in `abstract-btb-pairs-fp-and-relatively-simple`. This gives
  item 1.
- **The quotient contains the hard group.** FFWZ Lemma 5.2: `(P, K)` embeds in `(SV_P, SK_P)`,
  via `g ↦ [·, id, g, ·]`. So `P/K` embeds in `H/M`. `P/K` is finitely generated with
  unsolvable word problem, so `H/M` has unsolvable word problem, which is item 2.
- **No removal.** Suppose `ι : H → H'` is injective with `ι(H) ∩ M' = ι(M)`, where `(H', M')`
  is finitely presented and relatively simple with `M'` finitely normally generated. Then:
  - `H'/M'` is finitely presented, and it is simple by relative simplicity;
  - `H/M` embeds in `H'/M'`, hence so does the finitely generated `P/K`;
  - by `subgroups-of-fp-simple-groups-have-solvable-wp` (Kuznetsov), `P/K` then has solvable
    word problem. That contradicts item 2, so item 3 holds. ∎

## Remarks

- **Direct padded RN refinement (user submission, 2026-09-20).**
  `padded-abstract-rn-perfect-decidable-nonrecursive-kernel` strengthens this
  witness to a perfect decidable group with a simple quotient that is not
  even recursively presentable, directly in the derived subgroup of a padded
  abstract RN group. The conditional route
  `unsolvable-relative-quotient-via-direct-padded-rn` feeds this
  claim without an additional `SV_P` envelope. The new structural theorem is
  still unresolved; see the edited source reconstruction in
  `research/artifacts/padded-abstract-rn-manuscript-integration-2026-09-20.md`.
  The older derivation and referee record below do not certify that refinement.
- **Kuznetsov's algorithm needs the simple group itself to be finitely presented.** Here `H`
  is finitely presented and has a unique simple quotient, but that quotient's word problem
  is unsolvable. Kuznetsov's argument still enumerates the non-trivial words, since `w ∉ M`
  iff `⟨⟨w⟩⟩ = H`. It cannot enumerate the trivial ones.
- **The two parts of Question 5.9 fall together.** Any type `[A_2]` action with
  non-recursive kernel refutes both parts at once: the first directly, the second through
  `SV_G`. Conversely, a positive second part would have forced every type `[A_2]` kernel to
  be recursive.
- **The conjectures themselves are untouched.** `(relBH)` and `(relPBH)` are not refuted:
  every finitely generated group sharply embedded here has solvable word problem
  (`a2-stabilizer-image-presentation-controls-kernel` (4)). What fails is only the route
  "relative, then remove the kernel".

## Lesson for general BH

- **Relative simplicity is cheap; its simple quotient is not.** A finitely presented
  relatively simple group can have a simple quotient as undecidable as a Minsky machine.
- **So finite presentation must be won at the simple quotient itself.** A relatively simple
  envelope does not supply it.
- **Consequence for the relative route to BH.** Such a route must show that the canonical
  kernel of its own envelope is finitely normally generated, using that envelope's
  structure. For `SV_G`, that is finite presentation of the action image
  (`abstract-btb-simple-quotient-fp-gate`).

## Referee (bh-ref-ffwz, 2026-09-18): PASS, conditional on finite presentation of SV_P

I read the statements of FFWZ Theorem A and Lemma 5.2 in their TeX source (arXiv:2603.24687v2).
- **Theorem A:** "every proper normal subgroup of SV_G lies in the kernel of SV_G → SV_{G/K}".
  It is unconditional, which gives item 1.
- **Lemma 5.2:** "(G,K) sharply embeds in SV_G". It is unconditional.

The rest of the argument:
- **Item 2.** `P/K` contains `⟨Φ⟩`, which is finitely generated with unsolvable word problem.
  So `H/M ⊇ P/K` has unsolvable word problem. This is correct.
- **Item 3.** `ι(H) ∩ M' = ι(M)` makes `H/M ↪ H'/M'`. `H'/M'` is simple by relative
  simplicity and finitely presented because `M'` is finitely normally generated. Kuznetsov
  then gives a contradiction. This is correct.
- **The one external dependency is that `H = SV_P` is finitely presented.** It rests on FFWZ
  Theorem B (fp iff type [A_2], non-faithful case). That theorem is stated in their paper,
  but the repo records a gap in its printed proof. The node therefore invokes
  `abstract-twisted-bt-type-fn-criterion` item 2, which I did not referee here. Referee that
  node before citing part 2 unconditionally.
- **Reading of "sharply embeds" for pairs.** The same equality reading is used; see the
  referee note on `nonrecursive-a2-kernel-from-abstract-rover-nekrashevych-groups`.
- **Credit.** The relative-simplicity and pair-embedding inputs are FFWZ's. The observation
  that a type [A_2] action with a non-recursive kernel refutes both parts at once is already
  in Attempt 1 of `fp-relatively-simple-pairs-embed-with-fng-kernels`.
- **Update (bh-ref-ffwz, same day): condition discharged.** `abstract-twisted-bt-type-fn-criterion`
  item 2 received a fourth independent referee PASS (see its Referee section). Earlier
  passes were from referees a, b and c. So `SV_P` is finitely presented without FFWZ
  Theorem B's printed proof, and this node's PASS is unconditional. The remaining
  from-memory citations are Brown 1984, Hatcher–Wahl Prop 3.5 and Kuznetsov.

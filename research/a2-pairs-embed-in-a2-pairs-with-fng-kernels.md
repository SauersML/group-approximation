---
rg: 2
id: a2-pairs-embed-in-a2-pairs-with-fng-kernels
kind: claim
title: Every type [A_2] pair sharply embeds in a type [A_2] pair whose kernel is finitely normally generated
distinct_from:
  permutational-boone-higman-conjecture: that asks every decidable group to embed in a faithful type (A) actor; this asks that the kernel of any given type [A_2] actor can be removed by a sharp embedding, which together with Boone--Higman would give that conjecture.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4, removing mixed identities by enlarging a finitely presented simple group; this is FFWZ Question 5.9, removing an action kernel by enlarging a type [A_2] pair.
  a2-kernel-removal-forces-recursive-kernel: that proves a recursive kernel is necessary for one pair; this is the universal assertion.
  a2-action-with-non-finitely-presented-image: that is one pair whose image is not finitely presented but whose kernel is removable; this asserts removability for every pair.
  a2-kernel-removable-iff-image-in-type-a2-actor: that proves one pair is removable exactly when its image embeds in a type (A_2) actor; this asserts that every pair is removable, that is, that every type [A_2] action image lies in that class.
refuted_by:
  - a2-pair-with-non-removable-kernel-exists
artifacts:
  - research/artifacts/bh-type-a-actions-2026-09-12.md
---

**REFUTED** (2026-09-18, lane proofs, not reviewed) by `a2-pair-with-non-removable-kernel-exists`.
The answer to the first part of Question 5.9 is no: see
`nonrecursive-a2-kernel-from-abstract-rover-nekrashevych-groups`.

This is the first part of Fournier-Facio--Wu--Zaremsky,
arXiv:2603.24687v2, Question 5.9, read from the PDF text on MSI:

> "For G ↷ S an action of type [A_2] with kernel K, does there always exist an
> action G′ ↷ S′ of type [A_2] with kernel K′ finitely normally generated, such
> that (G,K) sharply embeds in (G′,K′)?"

Their note: "a 'yes' answer to the first part of Question 5.9 would tell us that
(relPBH) implies (PBH)". With their Theorem C
(`boone-higman-implies-relative-permutational-bh`), (BH), (relPBH) and (PBH)
would then all be equivalent. The graph carries this as the route
`pbh-via-bh-and-a2-kernel-removal` into `permutational-boone-higman-conjecture`.

## Attempts

1. **Normalizer covers.** Extend a type (A) actor `Γ` by a free group acting
   through a normalizing subgroup `Q`, as in
   `normalizer-extension-of-type-a-actor-is-a2-cover`. The kernel is removable
   whenever `Q` lies in a finitely presented group `P` of normalizing
   permutations with `P ∩ Γ = 1`: embed in `Γ x| (F_m * P)`. The explicit
   example `a2-action-with-non-finitely-presented-image` has a non-finitely-
   presented image, with `Q = δ(Z wr Z)` inside `P = δ(V)`. Its kernel is
   removed this way. *Dies* as a counterexample source: failure of finite
   presentation of the image does not by itself obstruct removal. Covers whose
   `Q` lies in no such `P` were not examined.
2. **Computability.** `a2-kernel-removal-forces-recursive-kernel` shows a
   removable kernel is recursive. For the FFWZ Theorem C actor of a finitely
   presented simple group `Γ`, recursiveness of the kernel implies
   recursiveness of the one-variable mixed identities of `Γ`. So an infinite
   finitely presented simple group with a non-recursive set of mixed identities
   would refute this claim. *Deferred*: no such group is known here, and
   producing one needs a simple group whose mixed identities encode a
   non-r.e. set while the group stays finitely presented.
3. **Remove mixed identities instead.** For the Theorem C actor, an element of
   the kernel sends each `x_i` to `x_i` times a mixed identity (BFFHZ, the
   non-MIF discussion after Lemma 2.2). An MIF overgroup of `Γ` makes the actor
   faithful. That is BFFHZ Question 3.4
   (`fp-simple-groups-embed-in-fp-simple-mif-groups`), also open, so this only
   trades one open question for another.
4. **Exact criterion.** By `a2-kernel-removable-iff-image-in-type-a2-actor`, one
   pair is removable exactly when its image `G/K` embeds in a group admitting a
   type (A_2) action. The witness is `G x Λ` acting through `Λ`, with `G`
   embedded along the graph of `G → Λ`. So this claim is the permutational
   Boone--Higman conclusion for every type [A_2] action image. Consequences:
   - a no answer with a recursive kernel would refute FFWZ Conjecture 1.5;
   - if Conjecture 1.5 holds, this claim is equivalent to recursiveness of
     every type [A_2] kernel.

   *Reformulation only*: it settles neither direction, and no type [A_2] action
   with a non-recursive kernel is known here.
5. **Non-recursive kernels** (lane solve-bh-q59-nonrecursive, 2026-09-13).
   One type [A_2] action with a non-recursive kernel would answer this claim
   negatively, by `a2-kernel-removal-forces-recursive-kernel`. The new claim
   `a2-stabilizer-image-presentation-controls-kernel` answers it positively for
   every pair with a finitely presented point-stabilizer image. It also fixes
   the shape of such a counterexample: the image is not recursively presented,
   every point-stabilizer image is finitely generated but not finitely
   presented, and no finitely generated sharply embedded subgroup carries the
   undecidability. Candidates tested:
   - **Acting through a quotient with solvable word problem**, e.g. `H x Λ`
     acting through a type (A_2) actor `Λ`, with `H` finitely presented with
     unsolvable word problem. *Dies.* The kernel is recursive whenever the image
     has solvable word problem.
   - **Hard sharply embedded subgroups.** *Dies* by item 4 of the new claim.
   - **Normalizer covers** (Attempt 1). *Dies for transitive actors* (hand
     remark, not a node).
     - The centralizer of a transitive type (A) actor `Γ` in `Sym(S)` is
       `N_Γ(H)/H`, which is finite because `H` has finite bi-index.
     - So a normalizing permutation is its automorphism of `Γ`, given by finite
       data, up to a finite ambiguity.
     - The image then has solvable word problem, so the kernel is recursive.
   - **FFWZ Theorem C actors** of an infinite finitely presented simple `Γ`.
     *Deferred.* The substitution `x_1 -> x_1 w(x_2, ..., x_(k+1))` of the route
     of `a2-kernel-removal-forces-recursive-kernel` many-one reduces `J_k(Γ)`
     to the kernel for every `k < n`, not only `J_1(Γ)`. Still no finitely
     presented simple group with a non-recursive set of mixed identities is
     known here.
   - **Affine actors** `A x| W` acting on `A` through `W -> Aut(A)` with finitely
     many orbits. *Unclear.* The kernel is `ker(W -> Aut(A))`, so a finitely
     presented `A x| W` whose image has co-r.e. non-recursive word problem would
     answer the question. Take `A = C(C, F_2)`, with the image containing `V`
     and extra computable homeomorphisms. The obstruction is finite presentation
     of `A x| W`: the module relations involve the stabilizer of a clopen set,
     which contains the kernel.

   *Open:* no type [A_2] action with a non-recursive kernel is known.
6. **Mixed identities of Thompson's group T** (lane
   solve-mixed-identity-undecidable, 2026-09-13). *Dies for T.*
   - `T` is the standard non-MIF finitely presented simple group
     (`homeo-circle-three-arc-commutator-word-is-mixed-identity`), so its
     Theorem C actor has a nontrivial kernel.
   - But `thompson-t-mixed-identity-problem-is-decidable` decides `J_k(T)` for
     every `k`, so the kernel is recursive
     (`thompson-t-relative-automorphism-actor-kernel-is-recursive`).
   - The remaining input is the OPEN claim
     `fp-simple-group-with-nonrecursive-mixed-identities`. Its route
     `non-removable-a2-kernel-from-nonrecursive-mixed-identities` would establish
     `a2-pair-with-non-removable-kernel-exists`, which this node names in
     `refuted_by`.

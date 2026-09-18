---
rg: 2
id: fp-relatively-simple-pairs-embed-with-fng-kernels
kind: claim
title: Every finitely presented relatively simple pair embeds in a finitely presented relatively simple pair whose largest normal subgroup is finitely normally generated
refuted_by:
  - fp-relatively-simple-pair-with-unsolvable-simple-quotient
distinct_from:
  a2-pairs-embed-in-a2-pairs-with-fng-kernels: that is the first part of FFWZ Question 5.9, removing the kernel of a type [A_2] action inside another action; this is the second part, removing the largest normal subgroup of a finitely presented relatively simple group inside another such group, with no action required.
  fp-quotient-iff-kernel-finitely-normally-generated: that is the general equivalence between finite presentation of a quotient and finite normal generation of its kernel; this asks for an enlargement in which the largest normal subgroup becomes finitely normally generated.
  abstract-btb-simple-quotient-fp-gate: that says when the simple quotient of one finitely presented abstract twisted Brin--Thompson group is finitely presented; this asks that every finitely presented relatively simple group embed compatibly in one whose simple quotient is.
  a2-kernel-removal-forces-recursive-kernel: that proves a removable action kernel is recursive; this is the universal removal assertion for largest normal subgroups, whose computability condition is Attempt 1 here.
  proper-normal-subgroups-miss-the-normally-generating-core: that shows every proper normal subgroup meets trivially a simple subgroup containing a normal generator; this asks for enlargements in which the largest normal subgroup becomes finitely normally generated.
  relatively-simple-removal-between-pbh-and-bh-of-quotient: that proves one pair is removable when its simple quotient embeds in a type (A_2) actor, and only when that quotient embeds in a finitely presented simple group; this asserts removability for every finitely presented relatively simple pair.
artifacts:
  - research/artifacts/bh-simple-products-embed-2026-09-12.md
---

**REFUTED** (2026-09-18, lane proof, not reviewed) by
`fp-relatively-simple-pair-with-unsolvable-simple-quotient`. The answer to the second part of
Question 5.9 is no.

This is the second part of Fournier-Facio--Wu--Zaremsky,
arXiv:2603.24687v2, Question 5.9, read from the PDF text on MSI (lines 1344–1346):

> "Does every finitely presented relatively simple (G,N) sharply embed in a
> finitely presented relatively simple (G′,N′) such that N′ is finitely normally
> generated in G′?"

**Terms** (their Definitions 1.2 and 1.6).
- **Relatively simple.** `N` is a proper normal subgroup of `G`, and every proper
  normal subgroup of `G` lies in `N`. Then `G/N` is simple.
- **Sharply embeds, for pairs.** This is read as their "embeds": an injective
  `ι: G → G′` with `ι(G) ∩ N′ = ι(N)`. FFWZ use the phrase this way for pairs in
  Lemma 5.2, and the note below needs only this reading.

**Statement.** Let `(G,N)` be finitely presented and relatively simple. Then there
are a finitely presented relatively simple `(G′,N′)`, with `N′` finitely normally
generated in `G′`, and an injective `ι: G → G′` with `ι(G) ∩ N′ = ι(N)`.

**Consequence.** `G′/N′` is then finitely presented and simple, and every `Γ ≤ G`
with `Γ ∩ N = 1` embeds in it. Their note (lines 1347–1351): "the second part would
tell us that (relBH) implies (BH)", and with Theorem C, "(BH), (relPBH), and (relBH)
are all equivalent to each other". In this graph it is the last premise of
`bh-product-closure-via-relatively-simple-kernel-removal`.

**Trivial case.** If `G/N` is finitely presented, `(G,N)` itself works, by
`fp-quotient-iff-kernel-finitely-normally-generated`.

## Attempts

1. **Computability.** Let `(G,N)` be finitely presented and relatively simple,
   with `G = <X | R>`.
   - **`N` is co-r.e.** `g ∉ N` iff `<<g>> = G`, iff every `x ∈ X` follows from
     `R ∪ {g}`.
   - **Recursive iff solvable.** `N` is recursive iff `G/N` has solvable word
     problem. By Kuznetsov's argument, `N` r.e. already suffices.
   - **Necessary condition.** If `ι` is as in the statement, then `G′/N′` is
     finitely presented simple. So it has solvable word problem, and
     `N = ι⁻¹(N′)` is recursive.
   - **Where counterexamples live.** A finitely presented relatively simple group
     whose simple quotient has unsolvable word problem refutes this claim. Every
     counterexample has a simple quotient that is not finitely presented.
   - **FFWZ's example.** Their finitely presented relatively simple group with
     unsolvable word problem (lines 1251–1254) comes from an action on one point.
     The image is trivial, so by their Corollary 4.2 the simple quotient is
     finitely presented, and the pair is its own witness.
   - **Twisted pairs.** For a type [A_2] action `H ↷ S` with kernel `K`, membership
     in `K` reduces to membership in `SK_H`, through the pair embedding of FFWZ
     Lemma 5.2 (`abstract-btb-pairs-fp-and-relatively-simple`). So a type [A_2]
     action with non-recursive kernel refutes this claim and the first part at
     once. For the Theorem C actor, an infinite finitely presented simple group
     with non-recursive one-variable mixed identities would give one, since those
     identities many-one reduce to the kernel
     (`a2-kernel-removal-forces-recursive-kernel` (c)).
   - *Deferred*: no such group is known here.
2. **No formal link with the first part.**
   - **First part to this one.** A kernel-removing embedding `(G,K) → (G′,K′)` of
     type [A_2] pairs comes with no map between the sets acted on. So it gives no
     evident embedding `(SV_G, SK_G) → (SV_{G′}, SK_{G′})`. If it did, FFWZ
     Corollary 4.2 would make `SK_{G′}` finitely normally generated, which is this
     claim for twisted pairs.
   - **This one to the first part.** The output here carries no action. Turning
     even a twisted Brin--Thompson pair into an action pair is FFWZ Question 5.7.
   - *Stops*: neither part is known to give the other in general.
   - **Partial link (09-13).** Suppose the first part holds, and the simple
     quotient `G/N` embeds in the image of some type [A_2] action. Then `G/N`
     embeds in a type (A_2) actor (`a2-kernel-removable-iff-image-in-type-a2-actor`),
     and `(G,N)` is removable by Attempt 4. This gives the second part only for
     pairs whose simple quotient lies inside a type [A_2] action image.
3. **Removal does not multiply over factors.** For proper pairs,
   `(G_1 x G_2, N_1 x N_2)` is not relatively simple: `G_1 x N_2` is a proper
   normal subgroup outside `N_1 x N_2`. Kernel removability in the first part
   passes to products (`relative-pbh-closed-under-finite-direct-products`,
   item 3). This claim for two factors gives no relatively simple pair for the
   product. The product route therefore applies it once, to the abstract twisted
   Brin--Thompson group of the product actor. *Consequence only.*
4. **Bounds by the simple quotient.**
   `relatively-simple-removal-between-pbh-and-bh-of-quotient`:
   - **Sufficient.** If `G/N` embeds in a type (A_2) actor `Λ`, let `G x Λ` act
     through `Λ` and pass to its abstract twisted Brin--Thompson group. Then
     `(G,N)` is removable.
   - **Necessary.** Removal forces `G/N` into a finitely presented simple group,
     which recovers Attempt 1.
   - **Consequences.** A no answer with recursive `N` would refute FFWZ
     Conjecture 1.5. If Conjecture 1.5 holds, this claim is equivalent to
     recursiveness of `N` for every finitely presented relatively simple pair.

   *Reformulation only*: no finitely presented relatively simple pair with
   non-recursive `N` is known here, and the gap between the two bounds is BH
   versus PBH for `G/N`.

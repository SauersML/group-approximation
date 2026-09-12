# Boone–Higman swarm 5, lane `bh-type-a-actions`: type [A_2] kernels, FFWZ Question 5.8, and what kernel removal needs

2026-09-12. This lane approaches the full Boone–Higman conjecture through actions. It pins down the source statements, then isolates where the step from Boone–Higman to its permutational form is stuck.
- **Answered:** one published question, FFWZ Question 5.8, positively.
- **Proved:** a necessary condition for the kernel-removal question, FFWZ Question 5.9 (first part).
- **Not proved:** Boone–Higman and its permutational form, both still open.

## 0. Sources and verification level

**Read from PDF text extracted on MSI:**
- **FFWZ.** Fournier-Facio–Wu–Zaremsky, *Abstract twisted Brin–Thompson groups*, arXiv:2603.24687v2, extracted at `/scratch.global/sauer354/bh-reviewer/2603.24687.txt`.
  - Lines 118–200: Conjectures 1.4, 1.5, 1.7 and 1.8, Definition 1.6, the statement of Theorem C, and the introduction's sentence on known PBH classes.
  - Lines 1205–1360: the proof of Theorem 5.1, Remark 5.3, Observation 5.4, Lemma 5.5 with its proof, Remark 5.6, and Questions 5.7–5.9 with the note after them.
- **BFFHZ.** Belk–Fournier-Facio–Hyde–Zaremsky, arXiv:2503.21882v2, extracted at `/scratch.global/sauer354/bh-outfn-mcg/2503.21882v2.txt`. Only grep hits at lines 99–499 were read: the opening of Theorem C, Corollary D, Theorem E, Corollary F, the MIF remarks, and the non-MIF kernel discussion.

**Not re-extracted in this session:**
- **FFWZ Definition 1.3 (type [A_n]) and Theorem B.** These stay at the level recorded on main, a summarizing fetch.
- **Zaremsky, arXiv:2405.18354 (Theorem A, Corollary B).** These stay at main's level, "read from source 2026-08-24". The PDF was downloaded to `/scratch.global/sauer354/bh-type-a/`, but `pdftotext` on MSI failed with a libstdc++ version mismatch.
- **Later literature.** The MSI master dropped mid-session and the fleet auth breaker was set, and the session's web-search budget was exhausted. So no literature after the FFWZ text was searched.

## 1. Exact hypotheses

- **Type (A)** (Zaremsky, verbatim on main in `type-a-action-gives-boone-higman-for-subgroups`):
  - the action is faithful;
  - G is finitely presented;
  - every Stab_G(s) is finitely generated;
  - there are finitely many G-orbits of two-element subsets of S.
- **Type [A_n]** (FFWZ Definition 1.3, via main):
  - G is of type F_n;
  - Stab_G(T) is of type F_(n−|T|) for finite T;
  - the diagonal action on S^n has finitely many orbits.

  For n = 2 this says: G finitely presented, point stabilizers finitely generated, finitely many orbits on S². Faithfulness is not required.
- **PBH** (FFWZ Conjecture 1.5, verbatim): "Every finitely generated group with solvable word problem embeds in a group admitting an action of type (A2) (equivalently embeds in a finitely presented simple twisted Brin–Thompson group)."
- **BFFHZ Theorem C:** (i) G satisfies PBH iff (iv) "G embeds in a finitely presented simple group that is MIF".
- **relPBH** (FFWZ Conjecture 1.8): Γ sharply embeds in (G, ker(G↷S)) for some type [A_2] action.
- **FFWZ Theorem C:** (BH) ⇒ (relPBH).
- **FFWZ Lemma 5.5:** relPBH holds iff there is a finitely presented G with a finitely generated H ≤ G of finite bi-index such that Γ embeds in G with every nontrivial element of Γ conjugate into G∖H.

**Which known classes satisfy PBH.** FFWZ, introduction, verbatim: "By now the Boone–Higman conjecture is known for many families of groups, e.g., Q-linear groups [Sco84, Zar25a], Aut(Fn) [BFFHZ], hyperbolic groups [BBMZ23a], Baumslag–Solitar and free-by-cyclic groups [BLIW], and more [BBMZ23b]; in all these cases, the groups not only satisfy (BH) but even (PBH)."

This answers the open item "which literature envelopes are type (A) actors" in `bh-type-a-permanence-2026-09-12.md`, at the level of FFWZ's assertion; their references were not re-checked. The repository's positive-characteristic class (`positive-char-surface-linear-groups-satisfy-boone-higman`) is not in that list. Whether it satisfies PBH is open here. By BFFHZ Theorem C it would follow if (L_p⊗L_p)^×/F_p^× embedded in a finitely presented simple MIF group. That was not attempted.

## 2. Decidability inside a type [A_2] actor

`a2-kernel-removal-forces-recursive-kernel`, established.

**(a) The action is computable.** Let G↷S be of type [A_2] with kernel K, and fix finite data: orbit representatives, stabilizer generators, and double-coset representatives. With that data, membership in each point stabilizer is decidable, and the action is computable. So K is co-r.e., and G/K has co-r.e. word problem. Only finite presentation of G is used. Main's `finite-bi-index-subgroups-have-decidable-membership` assumes a solvable word problem.

**(b) Removable kernels are recursive.** Suppose (G,K) sharply embeds in a type [A_2] pair (G′,K′) with K′ finitely normally generated. Then G/K embeds in the finitely presented group G′/K′, so K is r.e., hence recursive.

**(c) The Theorem C actor.** Let Γ be an infinite finitely presented simple group, n ≥ 2, A = Aut_Γ(Γ∗F_n) acting on Hom_Γ(Γ∗F_n,Γ), and K its kernel. The map w ↦ α_w, where α_w sends x_1 to x_1·w(x_2), many-one reduces the one-variable mixed identities J_1(Γ) to K. So if J_1(Γ) is not recursive:
- K is not recursive;
- A/K is not recursively presented, hence not finitely presented;
- (A,K) has no sharp embedding into a type [A_2] pair with finitely normally generated kernel.

**Consequence.** A "yes" to the first part of Question 5.9 forces every infinite finitely presented simple group to have a recursive set of one-variable mixed identities. No finitely presented simple group with a non-recursive set of mixed identities is known here.

## 3. Normalizer covers

`normalizer-extension-of-type-a-actor-is-a2-cover`, established.
- **Setting.** Let Γ ≤ Sym(Ω) be finitely presented, with finitely generated point stabilizers and finitely many orbits on Ω². Let Q = ⟨q_1,…,q_m⟩ lie in the normalizer of Γ in Sym(Ω), and let φ: F_m → Q send the basis to the q_i.
- **Conclusion.** Γ ⋊ F_m acts on Ω through γφ(w), with type [A_2]. Its kernel is ≅ φ^−1(Q∩Γ) and its image is ΓQ.
- **Criterion.** If Q/(Q∩Γ) is not finitely presented, neither is ΓQ, because Γ is finitely generated and normal in ΓQ.

## 4. Twisted Brin–Thompson clopen actions

`twisted-btb-clopen-action-is-type-a`, established. Let G↷S be faithful of type (A), and let Γ = SV_G act on the proper nonempty clopen subsets Ω of the cube C^S.
- **Type (A).** The action is of type (A).
- **Orbits.** Orbits of k-tuples are classified by nonempty Boolean atoms. There are seven orbits on ordered pairs (counting equal pairs) and five on two-element subsets.
- **Stabilizers.** Point stabilizers are D(U)×D(U^c), each factor ≅ SV_G.
- **Proof.** It uses only the brick calculus: brick unions, refinement, transitivity on equal-size brick partitions, patching, and conjugation by prefix insertion h_p.
- **Special case.** With S a single point and G trivial, SV_G = V, so this recovers the clopen action of V.

## 5. FFWZ Question 5.8: yes

`a2-action-with-non-finitely-presented-image`, established.

**Question 5.8** (verbatim): "Does there exist an example of a group action G ↷ S that is of type [A2] such that G/ker(G ↷ S) is not finitely presented?" FFWZ, just before: "we do not know an explicit example where it fails".

**Construction.**
- **Actor.** Γ = SV_V, for V acting on the proper clopen sets Ω_C of C. Γ acts on the proper clopen sets Ω of C^(Ω_C) with type (A) (§4).
- **Diagonal.** δ_w(κ)(s) = w(κ(s)) for w ∈ V normalizes Γ. The conjugate of a branch h_q τ_g h_p^−1 decomposes into finitely many branches, because only the coordinates in supp p ∪ g^−1 supp q see a nontrivial map. And δ_w ∉ Γ for w ≠ 1: pick a coordinate outside a branch's finite supports and compare a free input coordinate with the output.
- **Wreath product.** In F ≤ V, t = x_0 and b = λx_0λ^−1 on [1/4,1/2] generate Z≀Z.
- **The action.** Q = δ⟨b,t⟩ ≅ Z≀Z meets Γ trivially. §3 gives Γ⋊F_2 ↷ Ω of type [A_2] with image Γ⋊(Z≀Z). That image is not finitely presented, since Z≀Z is not (G. Baumslag, Math. Z. 75, 1961).

**Corollary.** The abstract twisted Brin–Thompson group SV_(Γ⋊F_2) is finitely presented (FFWZ Theorem B). Its canonical simple quotient is not (`abstract-btb-simple-quotient-fp-gate`).

**The kernel is removable.** Γ⋊F_2 sharply embeds in Γ⋊(F_2∗V), acting through Γ⋊δ(V). That kernel, {1}×ker(F_2∗V → V), is normally generated by two elements. So the first part of Question 5.9 holds for this action. Failure of finite presentation of an action image does not obstruct removing the kernel.

## 6. The kernel-removal hinge in Cairn

- **Open claim** `a2-pairs-embed-in-a2-pairs-with-fng-kernels`: FFWZ Question 5.9, first part, verbatim.
- **Route** `pbh-via-bh-and-a2-kernel-removal` into `permutational-boone-higman-conjecture`: BH + FFWZ Theorem C + kernel removal ⇒ PBH. With `boone-higman-via-permutational-boone-higman` it forms an intended conditional cycle, and it does not fire while BH is open.
- **Attempts recorded:**
  - normalizer covers are removable;
  - a recursive kernel is necessary, and for Theorem C actors this reduces to recursiveness of mixed identities;
  - removing mixed identities instead is BFFHZ Question 3.4, also open.

## 7. What this pins down for full Boone–Higman

- **Roots stay open.** Nothing here proves BH or PBH. `boone-higman-conjecture` and `permutational-boone-higman-conjecture` stay OPEN.
- **Universal constructions of type (A) actors** reduce, on main, to finite presentation of an explicitly specified actor: the shift-similar, shell full Cantor, fiber-product and finite bi-index routes. Any such construction must consume the input's word-problem algorithm (`complexity-bounded-host-classes-are-not-universal`, `compilers-cannot-drop-the-decidability-hypothesis`).
- **From BH to PBH.** Given BH, PBH needs exactly a kernel removal (FFWZ Q5.9) or a mixed-identity removal (BFFHZ Q3.4). §5 shows non-finitely-presented action images are not by themselves the obstruction. §2 shows that any refutation of Q5.9 through the Theorem C actors needs a finitely presented simple group whose one-variable mixed identities are not recursive.
- **Not settled in this session:**
  - permanence of the permutational class under HNN extensions or amalgams over decidable edges; sibling `bh-decidable-edge-hnn` covers the BH form;
  - the named classes Out(F_n) and closed-surface mapping class groups (BFFHZ lines ~396–405, which discuss Out(F_n), were not re-read);
  - PBH for the repository's positive-characteristic linear groups.

## 8. Novelty and credit

- **§§3–5: priority not checked.** No priority search was possible beyond the FFWZ v2 text, which poses Question 5.8 and says no explicit example is known to the authors. The normalizer construction is elementary and may be folklore.
- **§2(a),(b):** standard two-sided enumeration arguments.
- **§2(c):** the reduction to mixed identities uses BFFHZ's description of the kernel (automorphisms x_i ↦ x_i·(mixed identity)).
- **Lean:** none of this is verified in Lean.

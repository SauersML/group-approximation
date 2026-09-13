# Idea lane bh-ec-groups: existentially closed groups and model theory (2026-09-13)

Target: `boone-higman-conjecture` (OPEN root). Lens: existentially closed groups,
the space of marked groups, compactness. Nothing here is claimed established.
Hand arguments are marked as such.

Notation:
- `Dec` = finitely generated groups with solvable word problem.
- `K` = finitely generated groups that embed in some finitely presented simple group.
- BH says `K = Dec`. The converse inclusion `K ⊆ Dec` is a theorem (`simple-envelope-forces-solvable-word-problem`).

## Sources actually read

- **Cornulier–Guyot–Pitsch, arXiv:math/0511714** (text extracted with pdftotext; locators are theirs):
  - Proposition 2 = Proposition 2.2: a group is isolated iff it is finitely presented and finitely discriminable.
  - Theorem 3.4 (Simmons): solvable word problem iff recursively presentable and recursively discriminable.
  - Corollary 3.5: an isolated group has solvable word problem.
  - Proposition 3.6: groups with solvable word problem are not dense (Miller III).
  - Proposition 3.8: the skeleton of an existentially closed group is dense. They quote "[Neu73, Lemma 2.4]: a given isolated group embeds in every existentially closed group".
  - Theorem 7: finitely discriminable and isolated groups are stable under extensions and finite-index overgroups.
  - Proposition 8: infinite residually finite groups and infinite hyperbolic groups are not finitely discriminable.
  - Theorem 9: every finitely generated group is a quotient of an isolated group.
  - Question 4, verbatim: "Does every finitely generated group with solvable word problem embed into an isolated group?", followed by "Note that the stronger well-known question whether every finitely generated group with solvable word problem embeds in a finitely presented simple group is open."
  - Their §3 also records Macintyre [Mac72]: two existentially closed groups whose skeletons intersect exactly in the groups with solvable word problem. And [Neu73] / [LS77, IV.8.4]: every finitely generated group with solvable word problem embeds in every existentially closed group. I did not read Macintyre or Neumann directly.
- **Belk–Bleak–Matucci–Zaremsky, arXiv:2306.16356v3** (pdftotext):
  - Theorem 3.6 (Boone–Higman 1974): solvable word problem iff embeds in a computably presented simple group.
  - Corollary 3.7 and Theorem 3.8 (Thompson 1980).
  - Problem 5.3, items (1)–(12). Higman's four-generator group is not listed, and the text never mentions it.
  - Footnote 8: solvable Baumslag–Solitar groups BS(1,n) "are self-similar [3], and they can be seen to embed in finitely presented simple groups".
- **Word problem of Higman's group H4:** polynomial time, per a web-search summary of arXiv:1103.1232. Abstract not read.
- **Repo:**
  - root Attempts 1, 2, 6, 7 and "A strictly easier subproblem";
  - `bht-trivial-normal-intersection-envelope`;
  - `complexity-bounded-host-classes-are-not-universal`;
  - `almost-automorphism-conjugate-to-proper-power-is-equicontinuous`, as used in `baumslag-gersten-rn-obstruction-via-equicontinuity`;
  - `higman-four-cycle-intrinsic-mf-seed`, which records H4 as acylindrically hyperbolic (Minasyan–Osin Cor. 4.26).

## Approach 1. Compactness weakening W, and why it collapses on isolated inputs

**Idea.** Replace "G embeds in a finitely presented simple group" by W: every G in `Dec` is locally embeddable into `K`. That is, for every finite `F ⊂ G` there are `S ∈ K` and an injective partial homomorphism `F → S`. W is compactness-friendly: it is a condition on existential sentences and it passes to marked limits. So one might hope to prove it by approximation from known Boone–Higman classes.

**What it would prove.** BH, together with CGP Question 4.

**Kill test, run now (hand proof, standard).**

*Lemma.* If G is isolated and locally embeddable into a class C closed under finitely generated subgroups, then G ∈ C.

*Proof.* Write `G = <X | R>` finitely presented, with a finite discriminating set D. Choose F containing 1, X, every prefix of every relator, and a word path for each d ∈ D. A partial homomorphism injective on F extends to a homomorphism ψ: G → S: along each relator's prefix chain the image is forced back to 1. Also ψ(d) ≠ 1 for d ∈ D. Every nontrivial normal subgroup of G meets D, so ker ψ = 1.

*Consequences.*
- **BH ⟺ W ∧ (CGP Question 4).**
  - BH ⇒ W trivially.
  - BH ⇒ Q4, because a finitely presented simple group is finitely discriminable, hence isolated (CGP Prop. 2.2).
  - Conversely, let G ≤ I with I isolated. Then I ∈ `Dec` (CGP Cor. 3.5). W for I and the Lemma give I ∈ `K`, so G ∈ `K`.
- On isolated inputs W is literally BH. An isolated point is not a limit of other groups, so approximation arguments never reach exactly the inputs that matter once Q4 holds.

**Verdict.** Killed as a strategy, since it buys no leverage. Kept as a reformulation: BH = W + CGP Question 4.

## Approach 2. CGP Question 4 through outer semidirect products

**Idea.** Attack Question 4 directly. It is the model-theoretic half of BH, open as posed by CGP in 2007; my searches found no answer, but they were not exhaustive.

*Hand lemma.* Let S be a finitely presented nonabelian simple group, P a finitely presented group, and φ: P → Aut(S) injective with φ(P) ∩ Inn(S) = 1. Then `I = S ⋊_φ P` is isolated.

*Proof.*
- I is finitely presented: take the relators of S and P, plus `p s p^-1 = φ_p(s)` on generators.
- Let N ⊴ I be nontrivial. If N ∩ S = 1, then [N, S] ⊆ N ∩ S = 1, so N ⊆ C_I(S). But (s, p) centralizes S iff φ_p is conjugation by s^-1, which forces p = 1 and then s ∈ Z(S) = 1. So N ∩ S ≠ 1.
- Hence N ⊇ S, and any single nontrivial s ∈ S is a discriminating set.

**What it would prove.** Question 4, and with Approach 1, BH reduces to W. Take P to be a finitely presented overgroup of the input with solvable word problem (a Clapham-type embedding, recalled, not re-read). Then find a finitely presented simple S on which P acts faithfully by outer automorphisms.

**Kill tests, run now.**
- **A fixed S cannot serve every input (hand).** For finitely generated P ≤ Aut(S), the word problem of P reduces to S's word problem on images of generators, of length at most exponential in the word length. So a single S gives one recursive time bound, and `complexity-bounded-host-classes-are-not-universal` applies. S must depend on the input, just as the fp simple group does in BH.
- **The natural candidates add nothing.** Twisted Brin–Thompson groups SV_H already contain H, so they give nothing beyond the BFFHZ route. Aut(V) acts by rational homeomorphisms (recalled, not re-read), which the repo's rational-host nodes already exclude as universal containers.

**Verdict.** Survives as a reduction: CGP Question 4 follows from outer embeddings of finitely presented decidable groups into Aut(S) for finitely presented simple S. Feasibility unclear; no candidate S yet.

## Approach 3. The existential shadow of BH at Higman's group H4

**Idea.** W implies that every existential sentence true in a decidable group is true in some finitely presented simple group. Take

`ψ_H4 = ∃ a,b,c,d ( a^b = a^2, b^c = b^2, c^d = c^2, d^a = d^2, a ≠ 1 )`.

It holds in H4, which has solvable word problem (search summary above) and is not in BBMZ Problem 5.3. Realizing ψ_H4 in a finitely presented simple S needs only a nontrivial quotient of H4 inside S, which is weaker than embedding H4.

**Hand lemmas, checked now.**
- **(Higman's smallest-prime argument, in any group.)** Suppose a, b, c, d satisfy the four relations and all have finite order. From `b^-1 a b = a^2` we get `ord(a) | 2^ord(b) − 1`. A prime p dividing ord(a) then forces a smaller prime dividing ord(b), and this runs around the cycle; taking p minimal is a contradiction. So all four are trivial. Separately, a = 1 forces d = c = b = 1.
- **(BS(1,2) lemma.)** In any group, if x has infinite order and `y^-1 x y = x^2`, then `<x, y> ≅ BS(1,2)`. Indeed, every nontrivial normal subgroup of `BS(1,2) = Z[1/2] ⋊ Z` meets `Z[1/2]` nontrivially and then contains a power of x.
- **Consequences.**
  - A nontrivial image of H4 in a group G forces BS(1,2) ≤ G.
  - ψ_H4 is false in every residually finite group: the image would be a residually finite quotient of H4, hence trivial. In particular it is false in every finitely generated linear group.

**Kill test against known hosts.**
- BS(1,n) embeds in finitely presented simple groups (BBMZ footnote 8), so the necessary condition BS(1,2) ≤ S is met by some hosts.
- In the almost-automorphism hosts A_{d,r}, which contain V_{d,r}(G), V, T and F, `almost-automorphism-conjugate-to-proper-power-is-equicontinuous` makes every generator image equicontinuous, since each generator is conjugate to its square. I did not settle whether four equicontinuous elements can realize the four-cycle nontrivially.

**What it would prove.**
- A "no" (ψ_H4 false in every finitely presented simple group) refutes BH at H4.
- A "yes" in a concrete host gives the existential half for H4.

**Verdict.** Survives as a sharp test input, not as a counterexample. Next test: either search explicitly for a nontrivial H4 quadruple in V_{d,r}(G) for a self-similar G containing BS(1,2), or prove that equicontinuity together with the four-cycle forces triviality in A_{d,r}.

## Approach 4. Build fp simple hosts by compactness or omitting types

**Idea.** Uniformly simple groups (bounded normal generation) form an elementary class. Realize a decidable G in a model of "uniformly N-simple, containing G", and extract a finitely presented model.

**Kill test.** Finite presentation is not a first-order property. Compactness and ultraproducts produce non-finitely-generated models, and their finitely generated subgroups only give local embeddability, which is Approach 1 and collapses at isolated inputs. BBMZ Theorems 3.6 and 3.8 already give computably presented simple envelopes, so the only missing clause is exactly the non-elementary one. The root's Attempts 1–2 and its "strictly easier subproblem" record the same wall in lattice form.

**Verdict.** Killed.

## Approach 5. A single existentially universal host

**Idea.** Find one finitely presented simple group realizing every existential sentence realized by any group, as existentially closed groups realize every coherent system.

**Kill test (hand).**
- For a finitely generated S with solvable word problem, the existential theory Th_∃(S) is recursively enumerable.
- The set of coherent parameter-free finite systems (E = 1, N ≠ 1) is Π^0_1-complete: it is the complement of the uniform word problem of finite presentations. So no decidable group realizes every coherent existential sentence.
- For the version restricted to decidable inputs, `complexity-bounded-host-classes-are-not-universal` already excludes any single host.

**Verdict.** Killed. It duplicates the repo's non-universality principle, in model-theoretic form.

## Summary

- **Survive:**
  - Approach 3: a sharp H4 test input, with BS(1,2) as a proved necessary condition and equicontinuity in A_{d,r} from the repo.
  - Approach 2: a reduction of CGP Question 4 to outer actions on finitely presented simple groups.
- **Lemma kept:** BH ⟺ W ∧ CGP Question 4 (Approach 1).
- **Killed:** compactness and omitting-types constructions (Approach 4); a single existentially universal host (Approach 5).

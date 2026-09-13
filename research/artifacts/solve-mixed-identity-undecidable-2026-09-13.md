# Mixed identities of finitely presented simple groups: lane solve-mixed-identity-undecidable, 2026-09-13

**Target.** An infinite finitely presented simple group `Γ` with non-recursive
`J_k(Γ)`. Through the Theorem C actor this would answer the first part of FFWZ
Question 5.9 negatively.

**Verdict.** Not found. Thompson's `T`, the standard non-MIF example, is ruled
out, and the target is recorded as an OPEN claim wired to the negation of
Question 5.9.

## 1. Source pins

**BFFHZ, arXiv:2503.21882v2.** Extracted text on MSI at
`/scratch.global/sauer354/bh-reviewer/2503.21882.txt`. Subscripts and
superscripts were split onto separate lines by the extraction and are restored
inline below.

- l.155–156: "Similarly, any twisted Brin–Thompson group is highly transitive
  [BBMZa, Proposition 5.4]."
- l.157–163: "If G is a group, a non-trivial word w(x_1,...,x_n) ∈ G ∗ F_n is
  called a mixed identity in G if w(g1,...,gn) = 1 for all g1,...,gn ∈ G. That is,
  a mixed identity is similar to a law, except that it can involve constants from
  G. A group G is mixed identity-free (MIF) if it has no mixed identities. MIF
  groups are always lawless, but the converse does not hold; for example,
  Thompson's group T is lawless but not MIF [LBMB22b, Proposition 4.7]."
- l.164–166: "[HO16, Theorem 5.9] or [LBMB22b, Proposition A.1] for a proof that
  every finitely generated, highly transitive simple group is MIF."
- l.223–227: "there do exist finitely presented simple groups that are not MIF,
  for example among groups acting on the circle, see [LBMB22b, Proposition 4.7],
  such as Thompson's group T and certain variants, including torsion-free examples
  [HL]. Note however that T embeds in Thompson's group V, which is MIF, so it is
  unclear what to expect in general."
- l.463–464, Observation 2.4: "When n ≥ 2 and G is not MIF, the action is never
  faithful."
- l.465–467: "The kernel of the action consists of all automorphisms α ∈
  Aut_G(G∗F_n) such that α sends each x_i to itself times a mixed identity."
- l.690–698, Question 3.2: "For G a finitely presented simple group and n ≥ 2, is
  the quotient of Aut_G(G∗F_n) by the kernel of its action on Hom_G(G∗F_n,G)
  finitely presented? ... Aut_G(G∗F_n) itself is finitely presented ... for G
  non-MIF and n ≥ 2 it is definitely non-trivial, so it is unclear what to expect,
  even for example for Thompson's group T."

**Bibliography (l.978–981).**
- [LBMB22a] Le Boudec–Matte Bon, Confined subgroups and high transitivity, Ann. H.
  Lebesgue 5 (2022).
- [LBMB22b] Le Boudec–Matte Bon, Triple transitivity and non-free actions in
  dimension one, J. Lond. Math. Soc. (2) 105 (2022).

Their Proposition 4.7 was not read. The arXiv API returned nothing from MSI.

## 2. What landed

- `homeo-circle-three-arc-commutator-word-is-mixed-identity`: an explicit word
  `[[s_12, s_21], s_33]`, with `s_ij = [a_i, x a_j x^-1]` and supports in three
  disjoint arcs. It is a mixed identity of any orientation-preserving circle
  group; the interval analogue is `[s_12, s_21]`. Nontriviality is checked
  junction by junction in the free product normal form.
- `thompson-t-mixed-identity-problem-is-decidable`: `J_k(F)` and `J_k(T)` are
  recursive for all `k`. The certificate:
  1. a dyadic trajectory configuration;
  2. an extension lemma, since finite partial injections preserving the order or
     cyclic order extend to `F` or `T`;
  3. finitely many combinatorial types;
  4. `Z[1/2]`-feasibility, by Smith normal form plus Fourier–Motzkin.
- `thompson-t-relative-automorphism-actor-kernel-is-recursive`: the kernel of
  `Aut_T(T * F_n)` acting on `Hom_T(T * F_n, T)` is recursive.
- `fp-simple-group-with-nonrecursive-mixed-identities` (OPEN), with Attempts.
- `a2-pair-with-non-removable-kernel-exists` (OPEN): the negation of Question 5.9
  part 1, named in the Question 5.9 node's `refuted_by`.
- Route `non-removable-a2-kernel-from-nonrecursive-mixed-identities`: the
  `k`-variable transvection reduction.

## 3. Where hardness can and cannot sit (heuristic)

- **Words see constants only along trajectories of length |w|.** Undecidable
  long-orbit phenomena of individual elements do not transfer, e.g. torsion via
  Turing-machine elements in Brin–Thompson groups. Those groups are MIF anyway.
- **Hardness has to live in the quantifier.** It would come from which finite
  partial behaviours elements of `Γ` can realize. Flexible actions with finitely
  generated piecewise-linear data make that set decidable.
- **Non-MIF finitely presented simple groups known here all act on the circle**
  (T and variants [HL]). A counterexample needs a different mechanism for mixed
  identities, or circle dynamics that are rigid or not piecewise linear. No
  candidate is known.

## 4. Not done

- No construction, and no general decidability theorem.
- Leavitt unit groups: MIF status undecided, their mixed identities not examined.
- The torsion-free circle variants [HL] and the Higman–Thompson `T_(n,r)`: the
  extension lemma was not checked.

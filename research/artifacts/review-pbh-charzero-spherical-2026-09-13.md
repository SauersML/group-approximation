# Review: permutational Boone--Higman for characteristic-zero linear and spherical Artin groups

Lane `review-pbh`, 2026-09-13. This is an independent adversarial review from primary
sources. Each link gets PASS, FAIL or NIT.

## Scope

- 355212403: claim `char-zero-linear-groups-satisfy-permutational-boone-higman`
- 1660e31c9: route `char-zero-linear-pbh-via-polynomial-self-similar-hosts`
- b5774e942: claim `spherical-artin-groups-satisfy-permutational-boone-higman`
- dc131b160: route `spherical-artin-pbh-via-char-zero-linear-groups`
- 433083d11: route `e-type-artin-pbh-via-spherical-permutational-form`
- Also imported by the chain, and reviewed here for the first time:
  - part (a) of `fp-self-similar-subgroups-satisfy-permutational-boone-higman` (38595d4da);
  - its route `fp-self-similar-subgroups-satisfy-pbh-proof`.

The polynomial host links were already reviewed in
`research/artifacts/review-bh-polynomial-linear-2026-09-12.md` and were not re-audited:
- `char-zero-linear-groups-embed-in-polynomial-s-integer-groups`;
- `elementary-groups-over-polynomial-s-integers-are-fp`;
- `affine-extension-of-fp-elementary-group-is-fp`;
- `polynomial-parameter-affine-groups-are-self-similar`.

**Sources.** Line numbers refer to the text extracted on MSI, in
`/scratch.global/sauer354/bh-reviewer/`:
- `2503.21882.txt`: Belk--Fournier-Facio--Hyde--Zaremsky (BFFHZ), arXiv:2503.21882v2;
- `2405.09722.txt`: Zaremsky, arXiv:2405.09722;
- `2603.24687.txt`: Fournier-Facio--Wu--Zaremsky (FFWZ), arXiv:2603.24687v2;
- `0711.2372.txt`: Paris, arXiv:0711.2372;
- `2306.16356.txt`: Belk--Bleak--Matucci--Zaremsky (BBMZ), arXiv:2306.16356.

## Verdicts

| # | Link | Commit | Verdict |
|---|---|---|---|
| 1 | `char-zero-linear-groups-satisfy-permutational-boone-higman` | 355212403 | PASS |
| 2 | `char-zero-linear-pbh-via-polynomial-self-similar-hosts` | 1660e31c9 | PASS |
| 3 | `fp-self-similar-subgroups-satisfy-permutational-boone-higman` (a) and its route | 38595d4da | PASS |
| 4 | `spherical-artin-groups-satisfy-permutational-boone-higman` | b5774e942 | PASS |
| 5 | `spherical-artin-pbh-via-char-zero-linear-groups` | dc131b160 | PASS |
| 6 | `e-type-artin-pbh-via-spherical-permutational-form` | 433083d11 | PASS, with NIT 1 on its target |

No `invalidates:` is recommended.

## Check 1: the printed statement and definition

BFFHZ, l.120--122 (type (A)): "Given a group Γ acting faithfully on a set S, we say that
the action is of type (A) if: (i) The group Γ is finitely presented. (ii) The stabilizer
Stab_Γ(s) is finitely generated for all s ∈ S. (iii) The action has finitely many orbits
of pairs, i.e., the diagonal action of Γ on S×S has finitely many orbits."

BFFHZ, l.131--133: "Permutational Boone–Higman conjecture. Every finitely generated group
with solvable word problem embeds in a group admitting an action of type (A), and hence
in a finitely presented (simple) twisted Brin–Thompson group."

BFFHZ, l.137--139: "when we say it 'satisfies the permutational Boone–Higman conjecture'
we are implicitly saying it has solvable word problem, and explicitly saying it embeds in
a group admitting an action of type (A)."

FFWZ, l.130--132, Conjecture 1.5: "Every finitely generated group with solvable word
problem embeds in a group admitting an action of type (A2) (equivalently embeds in a
finitely presented simple twisted Brin–Thompson group)."

The claims use BFFHZ's terminology correctly. Finitely generated linear groups have
solvable word problem, and part 3 of
`boone-higman-type-a-class-closed-under-finite-extensions` also gives it. PASS.

## Check 2: the embeddings are permutational in the source's sense

The chain builds no type (A) action itself. It reaches (i) of BFFHZ Theorem C from (iii).

BFFHZ, l.168--178, Theorem C: "For a finitely generated group G (with solvable word
problem) the following are equivalent: (i) G satisfies the permutational Boone–Higman
conjecture, i.e., it embeds in a group admitting an action of type (A). (ii) G embeds in
a finitely presented (simple) twisted Brin–Thompson group. (iii) G embeds in a finitely
presented simple group that is highly transitive. (iv) G embeds in a finitely presented
simple group that is MIF. In particular, every finitely presented simple group that is
highly transitive, or more generally MIF, satisfies the permutational Boone–Higman
conjecture, as does every subgroup thereof."

**The mechanism.**
- Highly transitive implies MIF for finitely generated simple groups (Remark 3.5,
  l.728--730, citing [HO16, Theorem 5.9] and [LBMB22b, Proposition A.1]).
- BFFHZ, l.195--199, Theorem E: "For any finitely presented simple MIF group G, the
  group Aut_G(G ∗ F_n) (n ≥ 2) admits an action of type (A)". Theorem E "is the key to
  proving that (iv) implies (i) in Theorem C".

So every subgroup `H` of a finitely presented simple highly transitive envelope embeds in
a group with an action of type (A), in BFFHZ's exact sense. The chain also gets (ii), a
finitely presented simple twisted Brin–Thompson overgroup. That is FFWZ's parenthetical
form of Conjecture 1.5, so the claims read correctly under FFWZ's wording too. PASS.

## Check 3: the imported theorems against their sources

**Zaremsky's envelope** (`fp-self-similar-groups-embed-in-fp-simple-groups`).
- Zaremsky, l.29--30, Theorem 1.1: "Every finitely presented self-similar group embeds in
  a finitely presented simple group, and hence satisfies the Boone–Higman conjecture."
- Definition 2.1 (l.109--111): "A subgroup G ≤ Aut(T_d) is self-similar if its image in
  S_d ≀_d Aut(T_d) under the above isomorphism is contained in S_d ≀_d G."
- The proof, l.273--286: "our finitely presented group G admits a faithful self-similar
  representation into some Aut(T_d′) such that V_d′(G) has finite abelianization. Thus,
  the commutator subgroup [V_d′(G),V_d′(G)] has finite index in V_d′(G), hence is finitely
  presented by Citation 2.3. It is also simple by Citation 2.4 [...] we finish with
  embeddings G ↪ (G/H)≀H ↪ [V_d′(G),V_d′(G)]."

The envelope is therefore a finitely presented commutator subgroup of a
Röver–Nekrashevych group of a self-similar group. PASS.

**High transitivity of that envelope.** BFFHZ, Remark 3.5, l.736--738: "In particular
this includes Thompson's group V itself, along with all finitely presented commutator
subgroups of Röver–Nekrashevych groups Vn(G) [Nek18, Theorem 4.7]." This is listed among
the groups that are "obviously" highly transitive. So step 2 of
`fp-self-similar-subgroups-satisfy-pbh-proof` is covered verbatim by the source. The
elementary verification `rover-nekrashevych-groups-are-highly-transitive-proof` is
consistent with it. PASS.

**The host meets Definition 2.1.**
- `G = R^N ⋊ E_N(R)`, with `R = Z[1/m][t_1..t_k]`, acts on the rooted
  `p^(N+k)`-regular tree by residues of `(g(s)v + b(s), s)`.
- The action is faithful: a polynomial matrix identity holding on all of `Z_p^k` holds
  in `R`.
- The first-level states lie in `G` (`polynomial-parameter-affine-groups-are-self-similar`,
  already reviewed).
- So `G` is a finitely presented self-similar group in Zaremsky's sense. PASS.

**Linearity of spherical Artin groups** (`spherical-artin-groups-are-linear-over-q-x-y`).
- Paris, l.2192: "K = Q(x,y). Note that E is finite if and only if Γ is of spherical
  type."
- Corollary 6.5 (l.2239 onward, Bigelow, Krammer, Digne, Cohen–Wales): "Suppose that Γ
  is of spherical type. [...] Then ˆΦ is injective."
- Crisp's embedding into products of A_n, D_n and E_k factors is at l.2160.

**Field of definition.** The chain needs only a finitely generated linear group over
some field of characteristic zero, and `Q(x,y)` qualifies.
- The Cohen–Wales form (coefficients in `Z[r^±1, t^±1]`, faithful after specializing to
  a real `r_0 ∈ (0,1)`) gives the same conclusion.
- If a generic matrix is the identity, so is its entrywise specialization. So a faithful
  specialization forces a faithful generic representation, consistent with Paris's
  `Q(x,y)` form.
- Either field suffices. PASS.

## Check 4: the graph computes as claimed

**How it was run.**
- Snapshot: `git archive` of origin/main 26189cfec (`research/`, `tools/`, `bin/`),
  unpacked on MSI.
- Command: `python3.12 tools/cairn.py why <id>`.
- The 3238 non-research artifact paths missing from the snapshot were stubbed.
- 33 `<rev>:<path>` pins stayed unresolved, since there was no `.git`. None is on these
  derivations.

**Results.**
- `char-zero-linear-groups-satisfy-permutational-boone-higman` computes
  [ESTABLISHED via char-zero-linear-pbh-via-polynomial-self-similar-hosts]. Every leaf on
  the derivation is ✓:
  - the polynomial embedding;
  - `E_N` finitely presented, via the Steinberg citation;
  - the affine extension;
  - self-similarity;
  - `fp-self-similar-subgroups-satisfy-permutational-boone-higman`, via the Zaremsky
    citation, high transitivity and the BFFHZ Theorem C citation.
- `spherical-artin-groups-satisfy-permutational-boone-higman` computes
  [ESTABLISHED via spherical-artin-pbh-via-char-zero-linear-groups].
- `e-type-artin-groups-satisfy-permutational-boone-higman` computes
  [ESTABLISHED via e-type-artin-pbh-via-spherical-permutational-form].
- `fp-self-similar-subgroups-satisfy-permutational-boone-higman` computes
  [ESTABLISHED via fp-self-similar-subgroups-satisfy-pbh-proof].

PASS.

## Check 5: subsumption and novelty

**What the literature says.**
- FFWZ, l.145--148: "the Boone–Higman conjecture is known for many families of groups,
  e.g., Q-linear groups [Sco84, Zar25a] [...]; in all these cases, the groups not only
  satisfy (BH) but even (PBH)." So transcendence degree 0 is known, and the claim's
  credit section says so.
- BFFHZ, l.67--68: "the Boone–Higman conjecture remains open for the exceptional type
  spherical Artin groups".
- BBMZ, l.925--930: item (13) "remains open for many classes of Artin groups, including
  those of exceptional spherical type".

**arXiv search, 2026-09-13, from MSI.** The API was rate-limited, so the scan used the
arxiv.org search page with all fields, newest first. It covers titles, abstracts and
authors, not full text.
- "Boone-Higman" gives 12 results. The newest three are:
  - 2609.01868 (Almeida–Dantas–de Oliveira-Tosti): permutational wreath products
    `Z^d ≀_X G` over contracting self-similar `G` embed in finitely presented simple
    groups. It covers neither linear groups nor Artin groups.
  - 2603.24687 (FFWZ).
  - 2506.02319 (Fournier-Facio–Kropholler–Lyman–Zaremsky): for countable linear groups,
    every oligomorphic action on an infinite set has a finite subset whose stabilizer is
    not of type FP∞. This does not conflict with the chain. The type (A) actor there is
    `Aut_E(E ∗ F_n)`, and type (A) asks for finitely generated point stabilizers and
    finitely many orbits of pairs, not FP∞ stabilizers of all finite subsets.
- "permutational Boone" gives 2 results, neither about linear or Artin groups.

No printed PBH (or BH) result for all characteristic-zero linear groups or for the
exceptional spherical Artin groups was found. The credit wording in both claims ("no
priority is claimed beyond that root's") is appropriate.

**Repo scan.** The nodes whose titles mention permutational BH together with linear,
Artin or self-similar groups are:
- B̃_n and C̃_n;
- the E-reduction;
- the number-field part (b);
- the global-field soluble products;
- the five commits reviewed here.

None duplicates the new claims. PASS.

## Nits (no status change)

1. **Stale status line.** `e-type-artin-groups-satisfy-permutational-boone-higman` still
   says **OPEN**, and its Attempt 2 says "Why this claim stays open". The graph now
   computes ESTABLISHED through 433083d11. The owner should update the status line and
   close Attempt 2.
2. **Unquoted statement tail.** `permutational-boone-higman-conjecture` gives the
   statement as "read through a summarizing fetch". It is now verified verbatim (BFFHZ
   l.131--133), but the printed text continues "and hence in a finitely presented
   (simple) twisted Brin–Thompson group". Its "Known positive inputs" could list the
   characteristic-zero linear and spherical Artin claims.
3. **Graph-stale open cases.** The scope section of
   `aut-free-groups-satisfy-permutational-boone-higman` and the premise of
   `spherical-artin-boone-higman-reduces-to-e6-e7-e8` still describe the exceptional
   types as open. That is accurate for the literature but stale inside the graph.
4. **Two orbit conditions.** For a faithful action on `S` with `|S| ≥ 2`, BFFHZ's
   condition (iii), finitely many orbits on S×S, is equivalent to Zaremsky's finitely
   many orbits of two-element subsets, used in
   `type-a-action-gives-boone-higman-for-subgroups`.
   - The diagonal orbits are the orbits on `S`.
   - A 2-subset orbit splits into at most two orbits of ordered pairs.
   - Infinitely many orbits on `S` give infinitely many 2-subset orbits `{s_1, s_i}`.

   No fix is needed.
5. **The name (A2).** FFWZ name the condition (A2). The claims are also correct under
   that name, through Theorem C (ii).
6. **Crisp read secondhand.** Crisp's embedding is read through Paris only, as the
   trust section of `spherical-artin-groups-are-linear-over-q-x-y` already records.
7. **Envelope embedding not re-derived.** The embedding of the envelope in
   `Aut_E(E ∗ F_n)` was taken from the statements of Theorems C and E, not re-derived.

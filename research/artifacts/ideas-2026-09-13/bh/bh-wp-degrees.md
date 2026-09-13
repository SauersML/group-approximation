# Idea lane bh-wp-degrees: word-problem complexity of finitely presented simple groups

Target: `boone-higman-conjecture`, through its necessary consequence
`fp-simple-groups-with-arbitrarily-complex-word-problem` (OPEN). This file is
exploration only. It claims nothing established and edits no node.

## The complexity notion

- Fix a recursive non-decreasing `T`. `F(T)` is the class of languages decidable
  in time `C*T(C*n) + C*n + C` for some constant `C`, as in (UWB1) of
  `uniform-wp-bound-excludes-bh-universal-targets`. Changing the finite
  generating set is a linear-time substitution, so membership of a group's word
  problem in `F(T)` is a property of the group.
- "Degree" here means a complexity class, not a Turing degree. Every finitely
  presented simple group has Turing-degree-zero word problem
  (`simple-envelope-forces-solvable-word-problem`).
- Already on main:
  - the walls `complexity-bounded-host-classes-are-not-universal` and
    `uniform-wp-bound-excludes-bh-universal-targets`;
  - the two-sided bounds (TBO1)/(TBO2) of
    `twisted-brin-thompson-wp-equals-actor-orbit-problem`;
  - the Röver–Nekrashevych bound (RN1) of
    `rover-nekrashevych-word-problem-reduces-to-self-similar-group`;
  - the open premises `type-a-actors-with-arbitrarily-hard-word-problem` and
    `fp-self-similar-groups-with-arbitrarily-hard-word-problem`.
  Nothing below repeats those routes.
- Source check for the root's "What is known": Birget, arXiv:1902.03852, abstract
  checked 2026-09-13, "the word problem of the Brin-Thompson group nV over a finite
  generating set is coNP-complete for every n ≥ 2". This matches the quote in
  the root node.

## W1. Dehn-function screen — survives as a screen only

- **Idea.** In a finitely presented group with Dehn function `D`, a word of length
  `l` is trivial iff it has a van Kampen diagram of area at most `D(l)`.
  Enumerating those diagrams decides the word problem in time `2^(O(D(l) + l))`,
  with constants depending on the presentation. This is the standard enumeration
  bound, argued by hand here. So a family of finitely presented simple groups
  that beats every recursive `T` must also have Dehn functions not bounded by any
  single recursive function.
- **Would prove.** Nothing constructive. It is a necessary screen on candidate
  hosts, and it rules out a refutation of the root through a uniform Dehn bound.
- **Kill test.** Do finitely presented simple groups with large Dehn functions
  exist, and does a large Dehn function force a hard word problem?
- **Result.**
  - Zaremsky, arXiv:2305.15176 (abstract checked): "We construct examples of
    finitely presented simple groups whose Dehn functions are at least
    exponential ... Our examples arise from Röver-Nekrashevych groups, using
    carefully calibrated self-similar representations of Baumslag-Solitar
    groups." So the screen is passable, and a uniform Dehn bound is false.
  - Those hosts stay easy. (RN1) bounds them by one exponential over the input's
    word problem, and Baumslag–Solitar groups have polynomial-time word problems
    (Britton reduction; standard, not re-checked).
  - Dison–Einstein–Riley, arXiv:1509.02557 (abstract checked), solve the word
    problem of the hydra groups in polynomial time even though their Dehn
    functions are Ackermannian.
  - So Dehn growth is necessary, not a lever.
- **Verdict:** survives as a screen. Its refutation half is killed.

## W2. Normal-generation certificates (Kuznetsov) as a lever — killed

- **Idea.** In a simple group, `w != 1` iff every generator is a product of
  conjugates of `w^(±1)`, which is why recursively presented simple groups have
  solvable word problem. Try to make finitely presented simple groups hard by
  making those certificates long: a fast-growing normal-generation length.
- **Would prove.** A construction target independent of Dehn functions.
- **Kill test (by hand).** In a finitely presented group, every certificate
  `x = prod g_i w^(±1) g_i^(-1)` must itself be verified. That is a triviality
  search, governed by the same diagram enumeration as W1. The triviality half
  alone already decides the word problem within the W1 bound. So certificate
  length never pushes the complexity past the W1 bound, and it gives no separate
  handle on lower bounds.
- **Verdict:** killed as a lever for finitely presented hosts. It matters only for
  recursively presented simple groups.

## W3. This week's hosts on main — killed as a method for the root

- **Idea.** Reuse the chains that just put every finitely generated linear group
  (any characteristic), every spherical Artin group and every finitely generated
  metabelian group into B_A. If their envelopes were hard, the root would follow.
- **Kill test.**
  - Finitely generated linear groups over any field have logspace word problem:
    Lipton–Zalcstein 1977 in characteristic 0, Simon 1979 in characteristic p.
    This was read through summaries of Lohrey's papers, e.g. arXiv:2202.04060;
    the originals were not re-read.
  - The polynomial hosts `R^n ⋊ E_n(R)` are linear. The metabelian chain lands in
    finite products of linear groups (the quasi-linear route), so every input is
    polynomial time.
  - The envelopes add one exponential: (RN1) for the Zaremsky/Röver–Nekrashevych
    hosts, (TBO2) for twisted Brin–Thompson hosts.
  - The whole class these chains produce therefore lies under one recursive bound,
    about `2^poly`. By `complexity-bounded-host-classes-are-not-universal` it can
    never contain every decidable input or witness the root.
- **Would prove.** A clean constraint. A universal construction must leave
  "quasi-linear inputs in linear hosts" and must consume the input's algorithm.
- **Verdict:** killed as a method. Kept as a screen.

## W4. An easy actor with a hard stabilizer — killed (collapses to FP19, or is circular)

- **Idea.** By (TBO1), the orbit problem is the word problem plus point-stabilizer
  membership, and it reduces to the word problem of `SV_G`. So an actor with an
  *easy* word problem but *hard* stabilizer membership already gives a hard
  simple host.
  - Mikhailova fiber products `P_phi <= F_2 × F_2`, for `phi: F_2 -> Q` with `Q`
    finitely presented, have membership problem equivalent to the word problem
    of `Q`. This is standard and was not re-checked.
  - `F_2 × F_2` itself is easy.
- **Kill test (by hand).**
  - The coset action on `(F_2×F_2)/P_phi` has kernel containing
    `ker phi × ker phi`, so faithfulness forces the action of `Q×Q` on `Q` by
    `(a,b)·x = a x b^(-1)`.
  - Against the four conditions of `type-a-action-gives-boone-higman-for-subgroups`:
    this action is faithful iff `Q` is centreless; the stabilizer of `1` is the
    diagonal `≅ Q`; and the orbits of two-element subsets `{1, y}` correspond to
    conjugacy classes of `y`. So it is of type (A) iff `Q` is finitely presented,
    centreless and has finitely many conjugacy classes. Then `OP ≡ WP(Q)`.
  - This is the conjugacy-finite special case already recorded under
    `every-wp-group-embeds-in-fp-conjugacy-finite-group`. Even with no
    hardness requirement, it needs a positive answer to Makowsky's question FP19:
    "Is there an infinite finitely presented group with finitely many conjugacy
    classes?" (Shpilrain's problem list, checked; no status given there). The
    repo's kernel lane map records that no such group is known.
- **Second variant.** Take a permutational wreath product `Q ≀_X A` of a hard `Q`
  over an easy type (A) actor `A`, acting on `X × Q`. Pairs inside one fibre
  have one orbit per element of `Q` up to inversion. So the orbit count is
  infinite unless `Q` already carries a type (A) action on the fibre, which is
  exactly `type-a-actors-with-arbitrarily-hard-word-problem` again.
- **Verdict:** killed as a new route. "Easy actor plus hard stabilizer" collapses
  to FP19 or to the existing premise.

## W5. Compression amplification driven by distortion — unclear, leaning killed

- **Idea.**
  - Thompson's groups have PSPACE-complete compressed word problems
    (Bartholdi–Figelius–Lohrey–Weiß, arXiv:1909.13781, abstract checked).
  - Suppose a Thompson-like finitely presented simple host contained elements
    acting as exponent operators through Ackermannian-distorted subgroups. Hydra
    groups have finite-rank free subgroups of Ackermannian distortion (Dison–Riley,
    arXiv:1002.1945, abstract through a search summary).
  - Then short host words would encode Thompson words of Ackermann length, and
    the host's word problem would inherit a super-compressed word problem for
    `V`. A hierarchy theorem for that compressed problem would give
    unconditional hardness beyond every primitive recursive bound.
- **Would prove.** A stepping stone past Birget's coNP ceiling: a finitely
  presented simple group whose word problem is unconditionally outside elementary
  recursive time.
- **Kill test.**
  - Does huge distortion force a hard word problem? No. Dison–Einstein–Riley
    (arXiv:1509.02557, abstract checked) give polynomial-time solutions for the
    hydra groups, "by computing efficiently with enormous integers which are
    represented in compressed forms by strings of Ackermann functions". Distortion
    is not hardness.
  - Straight-line compression buys at most one exponential, since PSPACE ⊆ EXP.
  - The exponent-operator germs are not finite-state. That is necessary
    (`rational-homeomorphism-subgroups-have-exponential-wp`), but no
    finite-presentation mechanism is known for such germs.
- **Next test.** Is the word problem of `V` with power-tower-compressed exponents
  provably non-elementary, or does it have a hydra-style shortcut? A shortcut
  kills W5.
- **Verdict:** unclear.

## Summary

- **Survive:** W1, as a screen (Dehn growth necessary, not sufficient), and W5,
  unclear, with a concrete next test.
- **Killed:**
  - W2: certificates are no lever for finitely presented hosts.
  - W3: this week's linear, metabelian and spherical hosts sit under one recursive
    bound.
  - W4: an easy actor with a hard stabilizer collapses to FP19 or to the existing
    hard-actor premise.

Sources checked in this lane:
- arXiv:1902.03852, arXiv:2305.15176, arXiv:1909.13781 and arXiv:1509.02557 (abstracts);
- the FP19 entry of the Shpilrain problem list.

Taken from search summaries only:
- arXiv:1002.1945;
- Lipton–Zalcstein and Simon (through Lohrey's papers).

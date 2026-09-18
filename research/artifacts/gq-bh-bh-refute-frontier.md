# Red-team frontier for Boone–Higman (bh-refute, 2026-09-18)

This is a map, not a claim. A disproof of `boone-higman-conjecture` is exactly a subgroup-closed class
`P` such that
- **(S1)** `P` contains every finitely presented simple group, and
- **(S2)** `P` misses some finitely generated group with solvable word problem

(`hereditary-approximation-disproofs-of-boone-higman`, item 1). Every such `P` must also miss a
simple Kazhdan FA decidable group `K` lying inside a finitely presented decidable group `C`
(`bh-separators-must-omit-nested-decidable-hosts` §1). So `P` has to "see" finite presentation
and simplicity together.

## 1. Families of candidate separators

| family | invariant | (S1) | (S2) witness | status | node |
|---|---|---|---|---|---|
| approximation | sofic, MF | fails at `L^x` (nonsofic) / full-MF-radical group | — | **dead** | `hereditary-approximation-disproofs-of-boone-higman` |
| approximation | hyperlinear | open: (H1) no infinite f.p. simple group is HS-stable | open: (H2) needs a nonhyperlinear decidable group | open on both sides | same node, item 5 |
| decision problems | hereditary torsion / membership / conjugacy problem | fails at `2V` / `V` / `V` | — | **dead** | `bh-separators-must-omit-nested-decidable-hosts` §2 |
| decision problems | Turing degree | both sides degree 0 | — | **dead** | same, §2 |
| complexity | WP time bound `T` (`P_T`) | open, expected false | every `T` (`complexity-bounded-host-classes-are-not-universal`) | open; (S1) is the negation of `fp-simple-groups-with-arbitrarily-complex-word-problem` | same, §3 |
| complexity | Kuznetsov profile `(δ_S, ν_S) <= F` | reduces to `P_T` | as above | reduces to the row above | same, §3 |
| coarse geometry | property A (exactness) | open | Osajda RF decidable non-exact group | open; (S1) only | `exactness-separates-boone-higman-iff-fp-simple-groups-exact` |
| coarse geometry | coarse embeddability in Hilbert space (CE) | open, weaker than the exact row | decidable Osajda LPS monster `M` | open; (S1) only | `coarse-embeddability-separates-boone-higman` |
| K-theory | Baum–Connes with coefficients (BCC) | open | `M` (HLS02 via Osajda Cor. 3.3) | open; (S1) only; heredity cited, not re-read | `baum-connes-with-coefficients-separates-boone-higman` |
| Haagerup | a-T-menability | fails at infinite f.p. simple groups with property (T), e.g. Kac–Moody lattices of large thickness (Caprace–Rémy simplicity; Dymara–Januszkiewicz (T); literature context, not pinned here) | — | **dead** | cf. `fp-simple-kac-moody-lattices-are-mif` |
| isolation | "embeds in an isolated group" | **holds automatically** (f.p. simple groups are isolated) | open: the negation of CGP Question 4 (`every-decidable-group-embeds-in-an-isolated-group`) | open; the only row whose (S1) is free, so all the difficulty is in (S2) | `boone-higman-iff-isolated-hosts-and-local-boone-higman` |
| torsion | f.g. bounded-exponent subgroups are finite | open: no f.p. simple group is known to contain an infinite f.g. group of bounded exponent | `B(2,665)` | open; this is the obstruction side of BBMZ 5.3(6), owned by bh-free-12 | `free-burnside-groups-satisfy-boone-higman`, `almost-automorphism-torsion-subgroups-are-rf` |

In the table, "(S1) only" means (S2) is proved. The whole difficulty of a refutation through that
row is then a theorem about **all** finitely presented simple groups.

## 2. Positive tests Boone–Higman must pass (the open negations of (S1))

If the conjecture holds, finitely presented simple groups exist that are:
1. beyond every recursive word-problem bound (`fp-simple-groups-with-arbitrarily-complex-word-problem`; owned by bh-free-02);
2. non-exact (`fp-simple-nonexact-group`);
3. not coarsely embeddable, indeed coarsely containing an expander, and failing BCC (the CE and BCC nodes, item 2);
4. containing an infinite f.g. group of bounded exponent, e.g. `B(2,665)` (bh-free-12);
5. hyperlinear-nonsofic or nonhyperlinear, depending on (H1)/(H2).

These can all be realized by **one** group: the free product of the witnesses is finitely
generated and decidable. So Boone–Higman predicts a single finitely presented simple group with
properties 1–4 at once, for each recursive bound. Each item is a concrete construction problem
weaker than the conjecture. A construction for any one of them kills that refutation route
permanently.

## 3. Routes killed at the universal step by §1

- Exact host classes: linear, hyperbolic, cubulated of finite dimension, finite asymptotic
  dimension (exactness node).
- CE host classes, including all **Haagerup** hosts: `V`, `V_{n,r}`, SFT full groups, and groups
  acting properly on CAT(0) cube complexes (CE node, item 4). None of these can contain `M`.
- Residually finite, self-similar and almost-automorphism host classes for bounded-exponent inputs
  (bh-free-12).

## 4. Ideas tried and found to reduce (recorded so they are not retried)

- **Quantitative approximation profiles** (sofic or hyperlinear approximation size as a function
  of radius and error). A computable profile bound decides the word problem by search, so a
  profile separator is a complexity separator plus the corresponding approximation separator.
  Nothing new.
- **Isolation in the space of marked groups.** Every f.p. simple group is isolated. Whether every
  decidable group embeds in an isolated group is OPEN (CGP Question 4). So isolation is a live
  separator of the reverse type: (S1) is free, and refuting it needs a decidable group with no
  isolated overgroup (table row "isolation"). By `boone-higman-iff-isolated-hosts-and-local-boone-higman`,
  Boone–Higman is equivalent to CGP Q4 together with local Boone–Higman.
- **Uniform (effective) Boone–Higman.** A recursion-theorem diagonal against a compiler
  `e ↦ (S_e, φ_e)` forces only one thing: on some *invalid* index the compiler outputs a
  non-simple `S`. So there is no refutation of uniform Boone–Higman without adding a certificate of
  simplicity to the output. The diagonal: relators `w_k ∈ J` iff `φ(w_k) ≠ 1`, decided by
  dovetailing Kuznetsov's two searches. It is total exactly when `S` is simple.
- **Relative simplicity / maximal kernels.** This is the CK maximal-kernel route
  (`boone-higman-via-ck-maximal-kernel`) and gives nothing new for refutation.

## 5. What a genuinely new separator must look like

It must be subgroup-closed. It must hold for:
- `2V`, `V ⊇ F_2 × F_2`;
- the nonsofic `L^x`;
- groups containing `BS(1,2)` and Grigorchuk's group;
- infinite f.p. simple Kazhdan groups.

It must fail on the nested pair `K <= C`. By §1 and §4 it cannot be:
- a decision-problem property;
- a Turing degree;
- a resource bound;
- sofic, MF or Haagerup.

The live candidates are therefore coarse-geometric or operator-algebraic properties that no
finitely presented simple group is known to lack: hyperlinearity, exactness, CE, BCC, and the
bounded-exponent torsion property. Proving (S1) for any one of them is a theorem about all
finitely presented simple groups. No proof technique for such a theorem is known. The
nonsoficity of `L^x` shows that finitely presented simple groups can be analytically wild.

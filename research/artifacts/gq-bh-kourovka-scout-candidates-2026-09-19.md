# Kourovka candidates for new lanes (lane bh-kourovka-scout, 2026-09-19)

**Source and scope.**
- **Read at source:** Kourovka Notebook arXiv:1401.0300v46 (1 September 2026), pages 146–189,
  i.e. the whole 20th issue and the whole 21st issue. The local copy is
  `gq/src/bh-ref-kourovka-a/kourovka-1401.0300.pdf`.
- **Earlier issues:** scanned on 09-18 by bh-kourovka (`gq-bh-bh-kourovka-problems.md`) and
  not re-scanned here.
- **Checks.** For each problem below, main was searched with `git grep` on `research/` for an
  existing node. The arXiv checks are noted per item.
- **Problem texts** are quoted verbatim from the PDF pages.

## Results of this lane

| No. | Problem | Result |
|---|---|---|
| 20.33 (A. Bauer; signed J. Grochow) | Relativized Higman embedding theorem: a universal f.g. `G_X` for every oracle `X` | **Yes.** Literature answer credited to Ziegler 1980, via Scott arXiv:2404.11524v1 Thm 5.2.2. Node `kourovka-20-33-higman-relativizes-by-ziegler`; referee PASS `kourovka-20-33-ziegler-answer-review` (279d915221). |
| 21.119 (E. Schesler) | Kernels of type F_n, not F_{n+1}, on finite-index subgroups | **Open, constraints proved.** Node `kourovka-21-119-answers-need-infinite-vcd` (lane proof, unreviewed). Any answer is `F_∞`, has no torsion-free finite-index subgroup of finite cd, and is not commensurable with Thompson's `F`. Owned by this lane. |

## Candidates for fresh lanes (no node on main)

### 20.47 (A. Le Boudec, N. Matte Bon), p. 154

> Let G = F_n be a finitely generated free group. Let X be a compact G-space on which the
> G-action is faithful, minimal, and strongly proximal. Does it follow that the action is
> topologically free?

The definition in 20.46 on the same page: "A group action on a compact space is said to be
*topologically free* if the set of points with trivial stabilizer is dense."

**Notes.**
- **Lane observation (unreviewed): yes when the action is extremely proximal.**
  - Suppose `g ≠ 1` fixes an open `U` pointwise. Then `supp(g)` is a proper closed set.
  - Extreme proximality gives `h` with `h(supp g) ⊆ U`. Then `k = hgh⁻¹` has support inside
    `Fix(g)`, so `k` commutes with `g`.
  - In `F_n`, maximal cyclic subgroups are malnormal. So `h` lies in the maximal cyclic
    subgroup containing `g`, and `k = g`. Then `supp(g) ⊆ Fix(g)`, a contradiction.
  - So a counterexample needs a strongly proximal action that is not extremely proximal.
- **Free boundary.** The action on the Furstenberg boundary is free, since `F_n` is
  C*-simple (Kalantar–Kennedy, Breuillard–Kalantar–Kennedy–Ozawa). The question concerns its
  other boundary factors.
- **First step for a lane:** read Le Boudec–Matte Bon's papers on confined subgroups and
  micro-supported actions for what is already proved.
- **Related work:** the (RA) topologically-free versus free results on main (bh-ra-*).

### 21.44 (S. Eberhard), p. 174

> Let W_n = A_5 ≀ ⋯ ≀ A_5 be the n-times iterated permutational wreath product of A_5 in its
> natural action (so W_n acts on 5^n points), and let W = lim← W_n be the inverse limit
> (infinite iterated wreath product of A_5). Does W contain a finitely generated dense
> subgroup of subexponential growth?

**Notes.**
- A web search summary says arXiv:2604.15303 (*Diameter bounds for arbitrary finite groups
  and applications*) proves that no such subgroup has growth `≤ exp(n^{1/40})`. Not read;
  read it first.
- **Candidate tools:** Grigorchuk-type or Šunić-type branch groups with `A_5` labels, and
  Nekrashevych's fragmentations. The difficulty is that density needs the whole of `A_5` at
  every vertex, while every known intermediate-growth mechanism uses 2-groups or solvable
  labels.

### 20.110 and 20.111 (M. Vannacci), p. 163

> 20.110. Are there residually finite hereditarily just infinite groups that are
> a) amenable but not solvable?
> b) amenable but not elementary amenable?
> c) of intermediate word growth?
> d) of intermediate subgroup growth?
> All examples that we know are either linear (hence Tits Alternative applies), or have a
> quotient with property (T) (hence cannot be amenable).

> 20.111. Are there residually finite hereditarily just infinite groups admitting a
> self-similar action on a rooted tree that are not linear?

**Notes.**
- By Wilson's trichotomy, just-infinite groups are branch or virtually a direct power of a
  simple or hereditarily just-infinite group. Branch groups are never hereditarily
  just-infinite, so the Grigorchuk-group examples do not apply.
- A lane should look for non-branch, non-linear residually finite groups without property
  (T), e.g. suitable self-similar groups that are not weakly branch.

### Lower priority

- **21.116 (E. Schesler):** "Is every branch group boundedly acyclic?" It needs
  bounded-cohomology tools that no lane has.

## Already owned or on main (do not reassign)

- **Our results:**
  - 21.73 and 21.74(b),(c): settled negatively.
  - 21.74(a): decidable on V.
  - 21.75: bh-free-37.
  - 20.44: reduced to totally consumable groups.
- **21.41:** node `torsion-free-fp-metabelian-self-similar-group-contains-z-wr-z`, OPEN.
  Kochloukova–Luiz conjecture NO. It is adjacent to bh-kd2p.
- **21.45 and 21.46:** bh-kourovka-2146 owns 21.46.
- **21.140:** crux `basilica-hnn-extension-is-fp-infinity`.
- **21.146:** node `zaremsky-1-01-type-fn-groups-embed-in-type-fn-plus-1`.
- **20.7:** the BH root.
- **21.143–21.145** (Thompson's F: automaticity, Brin–Sapir, quasi-isometry): well-known
  problems, not recommended.

# Lane hl-bh-groupoid-embedding — 2026-09-13

Task: execute idea 1 of `research/artifacts/ideas-boone-higman-2026-09-13.md`
(input-encoded Cuntz–Krieger / shift-of-finite-type full groups as universal
Boone–Higman hosts), or land its obstruction.

## Verdict

Refuted as a universal route. Three new claims:

- `sft-topological-full-groups-have-the-haagerup-property`: citation of Matui's
  zipper-action theorem.
- `sft-topological-full-groups-have-exponential-word-problem`: direct proof, a
  single-exponential word problem for every finitely generated subgroup.
- `input-encoded-sft-groupoid-hosts-are-not-universal`:
  - some two-generated decidable group embeds in none of these groups, over all
    graphs at once;
  - no infinite Kazhdan group embeds in any of them, Deligne's lattice included.

The Boone–Higman conjecture itself is untouched.

## Source pins (verbatim)

H. Matui, *Topological full groups of one-sided shifts of finite type*,
arXiv:1210.5800. The e-print `tfgossftarXiv.tex` (modified 7 May 2013) is in
`/scratch.global/sauer354/hl-bh-groupoid-embedding/src/matui/`.

- **Abstract:** "The \'etale groupoid $G$ arising from a one-sided irreducible
  shift of finite type is a typical example of a purely infinite minimal
  groupoid. For such $G$, $[[G]]$ is thought of as a generalization of the
  Higman-Thompson group. We prove that $[[G]]$ is of type F$_\infty$, and so in
  particular it is finitely presented."
- **Definition 2.3** (l.396–409), part 2: "The set of all
  $\alpha\in\Homeo(G^{(0)})$ for which there exists a compact open $G$-set $U$
  satisfying $\alpha=\pi_U$ is called the topological full group of $G$ and
  denoted by $[[G]]$."
- **Basic G-sets** (l.1783–1789): "For words $\mu$ and $\nu$ with
  $t(\mu)=t(\nu)$, we define a compact open $G$-set $U_{\mu,\nu}$ by
  $U_{\mu,\nu}=\{(x,\lvert\mu\rvert-\lvert\nu\rvert,y)\in G\mid
  \sigma^{\lvert\mu\rvert}(x)=\sigma^{\lvert\nu\rvert}(y),\ x\in C_\mu,\ y\in
  C_\nu\}$. The subsets $U_{\mu,\nu}$ form a base for the topology of $G$."
- **Theorem simple2** (l.1466–1470): "Suppose that $G$ is purely infinite and
  minimal. Then any non-trivial subgroup of $[[G]]$ normalized by the commutator
  subgroup $D([[G]])$ contains $D([[G]])$. In particular, $D([[G]])$ is simple."
- **Subsection "The Haagerup property"** (l.2054–2066): "As in Section 6.1, we
  let $G$ be the \'etale groupoid arising from a one-sided irreducible shift of
  finite type $(X,\sigma)$. [...] this is a corollary of B. Hughes's theorem
  \cite[Theorem 1.1]{H09GGD}, which states that any locally finitely determined
  group of local similarities on a compact ultrametric space has the Haagerup
  property."
- **Theorem Haagerup** (l.2109–2112): "The action
  $\phi:[[G]]\curvearrowright\Omega$ is a zipper action. In particular, $[[G]]$
  has the Haagerup property."
- **Start of its proof** (l.2113 onward): "There exist admissible words
  $\mu_1,\mu_2,\dots,\mu_k$, $\nu_1,\nu_2,\dots,\nu_k$ such that
  $t(\mu_i)=t(\nu_i)$ for all $i=1,2,\dots,k$ and $W$ equals the disjoint union
  $\bigcup_{i=1}^kU_{\mu_i,\nu_i}$."
- **Theorem finite** (l.3245–3248): "The group $[[G|Y]]$ is of type F$_\infty$.
  In other words, the group $[[G|Y]]$ is finitely presented and is of type
  FP$_\infty$."

## Why idea 1 dies

1. **Fixing the graph was never the point.** The idea log already noted that a
   fixed graph gives a low-complexity host. The new point is uniformity: every
   element of every such full group is a finite table of canonical prefix
   replacements. So the word problem of any finitely generated subgroup runs in
   time `C*2^(C*n)`, with `C` depending on the graph and the tables. Under
   `complexity-bounded-host-classes-are-not-universal` that one recursive bound
   `T(l) = 2^l` covers all graphs at once, so choosing the graph from the input
   gains nothing.
2. **Kazhdan inputs are excluded independently.** Matui proves `[[G]]` has the
   Haagerup property, so every Kazhdan subgroup is finite. Deligne's lattice,
   the universal test input, never embeds, whatever the complexity.

## Test inputs asked for

- **Z² and BS(1,2):** they embed in Thompson's V (standard; not re-pinned here)
  and so in these hosts, but only through canonical similarities. Part 1 shows
  no embedding into these hosts can be anything else, rational or not, because
  every element is a canonical similarity table.
- **Deligne's lattice Γ̃:** embeds in none (part 2).

## Exact gap for groupoid hosts

A groupoid full-group host for Boone–Higman must at once:

- use elements that are not finite tables of prefix replacements over a single
  finite coding, so the complexity wall doesn't apply;
- have local groupoids with non-residually-finite vertex groups able to carry
  Kazhdan inputs with infinite center. That is circular by
  `deligne-lattice-eventually-similar-hosts-are-circular` whenever the
  eventually-similar framework applies;
- be finitely presented, for which the known theorems (Matui for shifts of
  finite type, and the contracting self-similar cases) all land inside the
  excluded classes.

The live shape is therefore a non-expansive groupoid, not a shift of finite
type: an infinite graph, a substitution or minimal subshift that isn't amenable,
or a groupoid with non-rational germs. No finite-presentation theorem for such
full groups is recorded on main. Idea 12 of the idea log (decidable-edge HNN
towers) is untouched by this lane.

## Checks

- `cairn why` on the three new claims, on a fresh MSI clone: see the lane report.
- The foreign `cairn check` errors on main (missing
  `a2-kernel-removal-iff-image-satisfies-pbh`; missing BowenChapman `.lean`
  artifact paths) are not from this lane.

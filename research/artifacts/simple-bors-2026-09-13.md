# Simple Birget–Ol'shanskii–Rips–Sapir: sources, one exclusion, the BS(1,2) test case (2026-09-13)

Lane `solve-bh-simple-bors`. The target is
`np-word-problem-groups-embed-in-fp-simple-polynomial-dehn-groups`: every
finitely generated group with word problem in NP embeds in a finitely presented
**simple** group with polynomial Dehn function. It came from approach A3 of
`research/artifacts/ideas-2026-09-13/bh/bh-simple-subgroup-fp.md`.

Sources were fetched as arXiv e-prints on the MSI login node into
`/scratch.global/sauer354/simple-bors/` and read from their TeX.

## 1. Verbatim source lines

- **BORS**, arXiv:math/9811106 (`main.tex`).
  - l.228: "Therefore if a finitely generated group $G$ is a subgroup of a finitely presented group with polynomial isoperimetric function then the word problem in $G$ is in NP (i.e. it can be solved by a non-deterministic Turing machine with polynomial time function)."
  - l.231: "the word problem of every finitely generated matrix group over a field of rational numbers can be solved in at most quadratic time by a deterministic Turing machine."
  - l.235–236, Theorem 1.1: "Let $G$ be a finitely generated group with word problem solvable by a non-deterministic Turing machine with time function $\le T(n)$ such that $T(n)^4$ is superadditive [...]. Then $G$ can be embedded into a finitely presented group $H$ with isoperimetric function equivalent to $n^2T(n^2)^4$ in such a way that $G$ has bounded distortion in $H$. In particular, the word problem of a finitely generated group is in NP if and only if this group is a subgroup of a finitely presented group with polynomial isoperimetric function."
- **Birget**, arXiv:1902.03852.
  - l.42: the word problem of `nV` "over a finite generating set is {\sf coNP}-complete for every $n \ge 2$".
  - l.91–94: "The Theorem implies that if ${\sf NP} \ne {\sf coNP}$ then the Dehn function of $nV$ (for $n \ge 2$) has no polynomial upper bound; more strongly, $nV$ cannot be embedded into a finitely presented group with polynomially bounded Dehn function (by \cite{SBR, BORS})."
  - l.2887, l.2905: completeness is under many-one and bounded conjunctive polynomial-time reductions.
- **Belk–Zaremsky**, arXiv:2001.04579.
  - l.155: "When $S$ is infinite, the group $\SVG$ is ``large'' in the sense that it contains $sV$ for all~$s\in \N$."
- **Zaremsky**, arXiv:2305.15176.
  - Abstract l.102: "We construct examples of finitely presented simple groups whose Dehn functions are at least exponential. [...] Our examples arise from R\"over--Nekrashevych groups, using carefully calibrated self-similar representations of Baumslag–Solitar groups."
  - l.177–178: "Let $G$ and $H$ be finitely presented groups [...]. Suppose $H$ is a quasi-retract of $G$. Then $\delta_H \preceq \delta_G$." (citing Alonso)
  - l.258: "Let $G\le\Aut(\tree_d)$ be a finitely generated, persistent, weakly diagonal, rational, self-similar group. Then $V_d(G)$ is virtually simple by virtue of $[V_d(G),V_d(G)]$ being simple and finite index, and there exists a quasi-retraction $V_d(G)\to G$."
- **arXiv:2410.23088**, abstract l.19: "We prove that Thompson's group $T$ and, more generally, all the Higman--Thompson groups $T_n$ have quadratic Dehn function."
- **arXiv:2605.09763**.
  - l.48: "cyclic subgroups are undistorted in $V,$ so any subgroup of $V$ must also have undistorted cyclic subgroups." (secondary for `V`; the primary wasn't re-read)
  - l.54–57: "all cyclic subgroups of $V\!\Ac$ are undistorted".

## 2. The exclusion that lands as a theorem

`twisted-btb-groups-poly-dehn-only-if-np-eq-conp`, ESTABLISHED:
- **Statement.** A finitely presented twisted Brin–Thompson group on an infinite set with polynomially bounded Dehn function forces `NP = coNP`.
- **Proof.** Belk–Zaremsky l.155 gives `2V <= SV_G`; Birget l.91–94 does the rest.
- **Credit.** Birget's remark; the twisted-envelope form is a one-line corollary.
- **Consequence.** Under `NP != coNP`, no type (A) actor, however well chosen, gives a polynomial-Dehn simple host through twisted Brin–Thompson envelopes.

## 3. What the other families do

| family of fp simple groups | Dehn function | can it hold `BS(1,2)`? |
|---|---|---|
| twisted Brin–Thompson `SV_G`, `S` infinite | not polynomial unless NP = coNP (§2) | irrelevant: excluded as polynomial hosts |
| Röver–Nekrashevych `[V_d(G),V_d(G)]`, G with Zaremsky's four properties | `≽ δ_G` (quasi-retraction l.258 + l.177–178) | needs a self-similar host containing `BS(1,2)` with polynomial `δ_G`; Zaremsky's `BS(1,n)` hosts give `≽ exp`; the polynomial affine hosts on main contain it, with Dehn functions and the four properties unchecked |
| `T`, `T_n` | quadratic (arXiv:2410.23088) | no: cyclic subgroups of `V` undistorted (l.48 of 2605.09763), `a` in `BS(1,2)` exponentially distorted |
| `V` | polynomial upper bound per a search summary (Guba), not source-checked | no, same reason |
| `VA` (Belk–Hyde–Matucci) | not checked | no: cyclic subgroups undistorted (2605.09763 l.54–57) |
| CAT(0) simple lattices | quadratic | no, by the solvable subgroup theorem (not read at primary source here) |

## 4. Where the S-machine tool stands

The BORS hosts are S-machine groups built by HNN towers. This lane found no
simple version and no fp simple overgroup of an S-machine group with a known
Dehn bound.

Two more routes are ruled out:
- **1-dimensional Thompson tails.** Through Röver–Nekrashevych, the tail
  dominates the host's Dehn function and needs a residually finite
  self-similar host.
- **Higher-dimensional tails.** Twisted envelopes contain `2V`, so §2 excludes
  them.

A simple polynomial-Dehn host therefore has to come from a construction outside
both Thompson-like families. None is known to this lane.

## 5. Novelty check

- **Web search.** Queries on "finitely presented simple group" + "polynomial
  Dehn function" + "word problem NP" + BORS found only BORS itself, its
  survey follow-ups, and Wagner arXiv:2509.17841 (quasi-isometric Higman
  embeddings). None states or asks the simple version.
- **Wagner.** The abstract was not located in the extracted e-print (figure
  files only listed), so its exact statement is not quoted here.
- **Verdict.** Search not exhaustive.

## 6. Verdict

- **Partial.** The simple BORS statement is recorded as an OPEN root.
- **ESTABLISHED.** The twisted Brin–Thompson route is excluded under `NP != coNP`.
- **Test case.** `BS(1,2)` is open: no fp simple group with polynomial Dehn function containing it is known in the checked literature.
- **Most concrete next test.** The Dehn function of a polynomial affine self-similar host containing `BS(1,2)`, and whether it has Zaremsky's four properties. Either answer decides the Röver–Nekrashevych route for this input.

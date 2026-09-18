# Exactness as a Boone--Higman separator (c-pz3, swarm-0917, 2026-09-18)

Lane: transplanter, family operator-algebras, slot `boone-higman-conjecture`.
Files written by this lane:
- `decidable-residually-finite-non-exact-group-exists` with route `decidable-residually-finite-non-exact-group-proof`;
- `exactness-separates-boone-higman-iff-fp-simple-groups-exact` with route `exactness-separates-boone-higman-proof`;
- `fp-simple-nonexact-group` (OPEN) with route `fp-simple-nonexact-group-via-boone-higman`.

## 1. Sources read at source this session (verbatim)

### 1.1 Osajda, *Residually finite non-exact groups*, GAFA 28 (2018), arXiv:1703.03791

The e-print was downloaded again and `rfneg_arXiv.tex` extracted on 2026-09-18. Line numbers refer to that file.

- l.319: "By $G_i$ we will denote the  finitely presented group given by the graphical presentation $G_i=\langle S \; | \; \hth{1}, \, \hth{2} , \ldots, \hth{i} \rangle$."
- l.320–322: the quotient maps are $\qij{i}{j}\colon G_i \twoheadrightarrow G_j$, and the maps to finite groups are $\phij{i}{j}\colon G_i \to F_j$, "with $\phij{i}{i}$ denoted $\phij{i}{}$". Also "$G=\varinjlim (G_i,\qij{i}{j})$, with $\qij{i}{\infty} \colon G_i \to G$, and $\phij{\infty}{i} \colon G \to F_i$ being the induced maps."
- l.329: "(C) $\phij{j}{}(g)\neq 1$, for every $j$ and every $g\in B_{j}(1,\mr{Cay}(G_{j},S))\setminus \{1\};$"
- l.330: "(D) $\phij{l}{j}\circ \qij{k}{l}=\phij{k}{j}$, for all $j\leqslant k \leqslant l$."
- l.396 (every $G_{i+1}$): "acts geometrically on a CAT(0) cubical complex. Hence, by results of Wise \cite{Wise-quasiconvex} and Agol \cite{Agol2013}, it is residually finite." The induction basis says the same for $G_1$: "acts geometrically on a CAT(0) cubical complex. Therefore, by results of Wise \cite{Wise-quasiconvex} and Agol \cite{Agol2013} it is residually finite."
- l.425–426: "$\mr{Cay}(G,S)$ contains a sequence of $D$--regular graphs of growing girth, and hence $G$ is non-exact, by \cite{Willett2011}."
- l.429–434, the residual finiteness proof: "Take a non trivial element $g\in G$. Let $i$ be such an integer that $g\in B_{i}(1,\mr{Cay}(G,S))$. Then there exists $g'\in G_i$ such that $\qij{i}{\infty}(g')=g$, and $g'\in B_{i}(1,\mr{Cay}(G_i,S))$. For the homomorphism $\phij{\infty}{i}\colon G \to F_i$ into the finite group $F_i$ we have $\phij{\infty}{i}(g)=\phij{\infty}{i}\circ \qij{i}{\infty}(g')=\phij{i}{}(g')\neq 1$, by $(D)$ and $(C)$."

### 1.2 Willett, *Some notes on property A*, arXiv:math/0612492

The e-print `PropertyA.tex` was downloaded on 2026-09-18.

- l.494: "Property A is invariant under coarse equivalence."
- l.540–542: "if $X$ has property A and there exists a coarse embedding of $Y$ into $X$, then $Y$ has property A too; in particular, property A is inherited by subspaces."
- l.544–546: "one of Yu's main motivations for introducing property A was that it implies coarse embeddability into Hilbert space".
- l.1607 (Lemma): "If $G$ has property A, and $H$ is a subgroup of $G$, then $H$ has property A."
- l.1136: "The vertex set of any tree $\mathcal{T}$ (i.e. graph with no loops) has property A."
- l.1310–1317 (Corollary): for metric spaces $X,Y$ with property A and a product metric restricting to the fibre metrics and dominating the max metric, "Then $X\times{}Y$ has property A."
- l.1451: "Any metric space with finite asymptotic dimension also has property A."
- The list of groups known to have property A, l.1963–1980:
  - "Groups that are \emph{hyperbolic in the sense of Gromov}."
  - "groups that act properly cocompactly by isometries on a (finite dimensional) \emph{CAT(0) cube complex} have property A." (Campbell--Niblo)
  - "Any countable subgroup of $GL(n,F)$ for any $n$ and any field $F$." (Guentner--Higson--Weinberger)
  - "Any discrete subgroup of a connected Lie group."

### 1.3 Equivalence with exactness

Already verbatim in `research/artifacts/sk-free-1-exactness-2026-09-13-part1.md` §3.
- Osajda 1703.03791 l.119–120: "A finitely generated group is non-exact if its reduced C*-algebra is non-exact. Equivalently, it has no Guoliang Yu's property A".
- Osajda 1406.5015 l.166: "For countable discrete groups, Property A is equivalent to [...] the exactness of the reduced $C^{\ast}$--algebra".

### 1.4 Context only, not load-bearing

Sapir, *Aspherical groups and manifolds with extreme properties*, arXiv:1103.3873. The abstract was read through a summarizing fetch on 2026-09-18: "There exists a 4-dimensional closed aspherical manifold M such that the fundamental group π₁(M) coarsely contains an expander, and so it has infinite asymptotic dimension, is not coarsely embeddable into a Hilbert space".
- By Willett l.544–546 such a group has no property A. So finitely presented non-exact groups exist.
- The open content of `fp-simple-nonexact-group` is simplicity together with finite presentation.
- The word problem of Sapir's group was not checked, so it is not used as a Boone--Higman input.

## 2. The derivation of the word problem

Let $w$ be a word over $S^{\pm 1}$ of length $\ell$. Put $n = \max(\ell, 1)$ and let $g' \in G_n$ be the image of $w$.

1. $g' \in B_n(1, \mathrm{Cay}(G_n,S))$.
2. If $g' = 1$ in $G_n$, then $w = 1$ in $G$. This holds because $G$ is the quotient of $G_n$ by the remaining relators, via $q^n_\infty$.
3. If $g' \neq 1$ in $G_n$, then by (C), $\varphi_n(g') \neq 1$. The induced map satisfies $\varphi^\infty_n \circ q^n_\infty = \varphi_n$ (l.434). So $\varphi^\infty_n(q^n_\infty(g')) \neq 1$, hence $w \neq 1$ in $G$.

So **$w =_G 1$ iff $w =_{G_n} 1$ whenever $|w| \le n$.**

This is the residual-finiteness argument of l.429–434, read as a reduction, with the radius taken equal to the word length.

**Uniformity.**
- By `recursive-residually-finite-non-exact-groups-exist-proof` (steps 2–3), $i \mapsto \widehat\Theta_i$ is computable when the input sequence is recursive. The same route uses fundamental cycles at every base vertex (review fix F1) to give a finite relator set for $G_i$. So $n \mapsto$ (finite presentation of $G_n$) is computable.
- Each $G_n$ is finitely presented and residually finite (l.396 and the basis).
- The McKinsey procedure of `fp-residually-finite-groups-have-solvable-word-problem-proof` is uniform in the finite presentation. It runs the consequence enumeration in parallel with the search for a finite permutation quotient that separates the word, and it halts on every word because $G_n$ is residually finite.

So $G$ has solvable word problem.

**Nothing new is needed from the paper.**
- (C) and (D) are proved there for all indices.
- The only effectivity used is the one already in the recursive node.

## 3. Novelty check (bounded)

- Grepped `research/*.md` for `word problem|decidab` in all `*exact*`, `*osajda*`, `*property-a*` and `recursive-residually-finite-*` nodes. The only hit is the part-2 artifact's use of McKinsey inside the *construction*. No node states that Osajda's group, or any non-exact group, has solvable word problem.
- Grepped for `boone` together with `exact|property A`. No Boone--Higman node uses exactness as an invariant.
- `hereditary-approximation-disproofs-of-boone-higman` treats soficity, MF-ness and hyperlinearity. Exactness is not contained in any of these as far as is known, and it is absent there.
- Live bus feed (cone `boone-higman-conjecture`, 2026-09-18): no exactness lane.

## 4. Kill scope and flags

- **Unconditional kill at step "all decidable groups embed in members of an exact class".** The inputs are the Osajda group, or its decidable simple Kazhdan LEF host.
- **Instances.**
  - Linear groups over commutative rings: the graph node `commutative-ring-linear-groups-have-property-a`.
  - Linear groups over fields, Gromov hyperbolic groups, and groups acting properly cocompactly on finite dimensional CAT(0) cube complexes: Willett's list (§1.2), which is a secondary source for Guentner--Higson--Weinberger, Roe and Campbell--Niblo. The primaries were not re-read.
- **Products of locally finite trees.** A group acting properly cocompactly on $T_1 \times T_2$ is coarsely equivalent to $V(T_1) \times V(T_2)$ with the $\ell^1$ metric, by the Švarc--Milnor lemma (classical, not quoted here). That product has property A by Willett l.1136 and l.1317. This covers the uniform lattices in products of closed tree automorphism groups that act cocompactly on the trees. It is the geometry every non-linear uniform example in Caprace's survey has, according to the sibling Bader--Shalom lane (not landed; see §5).

## 5. Consequence for the sibling Bader--Shalom lattice-host lane

A sibling worktree drafts a route. Its prerequisite P1 asks every decidable simple group to embed in a cocompact lattice `Γ < G_1 × G_2` with dense projections.
- The decidable simple Kazhdan LEF host of the Osajda group is not exact. So P1 forces `Γ` to be non-exact.
- Every factor pair whose lattices act properly cocompactly on a product of locally finite trees, or on a finite dimensional CAT(0) cube complex, is therefore excluded unconditionally.
- The draft excludes products of properly cocompact CAT(0) factors only conditionally, on an unpinned Dehn-function bound. For the cube and tree cases the conditional kill becomes unconditional.
- This is recorded here in text only, because that node is not on this worktree's base.

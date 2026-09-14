# Finitely presented intermediate growth: deficiency and Golod–Shafarevich pins (2026-09-14)

Lane hl-fp-intermediate-growth.
- Ershov survey TeX fetched on MSI under
  `/scratch.global/sauer354/hl-fp-intermediate-growth/src/1206.0490/main.tex`.
- Kochloukova's paper read from the EMS Press PDF.
- Earlier pins: `fp-intermediate-growth-pins-2026-09-13.md`, `hl-intermediate-growth-pins-2026-09-13.md`.

## Ershov, *Golod–Shafarevich groups: a survey*, arXiv:1206.0490 (Internat. J. Algebra Comput. 22 (2012))

- Definition, l.949–950: "An abstract group $G$ is called a {\it Golod-Shafarevich} group (with
  respect to $p$) if its pro-$p$ completion $G_{\phat}$ is Golod-Shafarevich."
- Theorem `GS_strong`, l.1075–1081:
  - "(a) Let $G$ be a finitely presented pro-$p$ group such that $r(G)\leq d(G)^2/4$. Then $G$ is
    infinite. If in addition $r(G)< d(G)^2/4$ and $d(G)>1$, then $G$ is Golod-Shafarevich."
  - "(b) Let $\Gamma=\la X|R \ra $ be a finitely presented abstract group, and let
    $d_p(\Gamma)=\dim_{\Fp}(\Gamma/[\Gamma,\Gamma]\Gamma^p)$. If
    $|R|<d_p(\Gamma)^2/4-d_p(\Gamma)+|X|$ and $d_p(\Gamma)>1$, then $\Gamma$ is Golod-Shafarevich
    (with respect to $p$)."
- Proposition `gs:filtered`(a): "Assume that there exists a real number $\tau\in (0,1)$ s.t.
  $1-|U|\tau+H_R(\tau)\leq 0$. Then $A$ is infinite-dimensional and $Hilb_A(\tau)$ diverges. If
  $1-|U|\tau+H_R(\tau)< 0$, the sequence $\{a_n\}$ (defined above) has exponential growth."
- Proposition `prop:BaGr`, l.1133, credited to \cite{BaGr}: "Golod-Shafarevich abstract groups
  have uniformly exponential growth." The proof ends: "Each such product lies in the $\Fp$-span of
  $B_X(n)$, the ball of radius $n$ with respect to $X$ in $\Gamma$. Hence $|B_X(n)|\geq a_n$."
- Just after that proof: "It is now known that Golod-Shafarevich groups are uniformly non-amenable
  ~\cite[Appendix~2]{EJ2} (which strengthens the assertion of Proposition~\ref{prop:BaGr})".

## Kochloukova, *Some Novikov rings that are von Neumann finite and knot-like groups*, Comment. Math. Helv. 81 (2006), 931–943

- Theorem 1 (p. 932): "Let $G$ be a finitely generated group, $\chi\colon G\to\mathbb Z$ a non-zero
  discrete character of $G$. Then every matrix ring $M_n(\widehat{\mathbb ZG}_\chi)$ is von Neumann
  finite."
- Theorem 3 (p. 933): "Let $G$ be a non-trivial discrete group with a finite $K(G,1)$ CW-complex $Y$
  of dimension $n$ such that the Euler characteristics of $Y$ is zero. Suppose that $N$ is a normal
  subgroup of $G$ containing the commutator subgroup such that $N$ is of homological type
  FP$_{n-1}$ and $G/N$ is cyclic-by-finite. Then a) $N$ is of homological type FP$_n$; b) $G/N$ has
  finite virtual cohomological dimension vcd$(G/N)$ = cd$(G)$ − cd$(N)$. In particular either $N$
  has finite index in $G$ or $N$ has cohomological dimension cd$(G)-1$."
- p. 933, after Theorem 3: "the condition in Theorem 3 on the Euler characteristic cannot be removed
  as there is an example of a group $G$ of cohomological dimension 2 and type FP$_\infty$ with a
  finitely generated normal subgroup $N$ such that $G/N\simeq\mathbb Z$ but $N$ is not free [3, Thm.
  B and Remark 5.4]. The deficiency of this group $G$ is not 1."
- p. 934, proof of Corollary 2: "otherwise cd$(G) = 1$ and by the Stallings theorem $G$ is free
  [20]". Reference [20]: J. R. Stallings, On torsion-free groups with infinitely many ends, Ann. of
  Math. (2) 88 (1968), 312–334.
- Corollary 2 (p. 934): "Let $G$ be a knot-like group with a finitely generated commutator subgroup
  $G'$. Then $G'$ is free, i.e. the Rapaport conjecture holds."
- Corollary 3 (p. 934): "Let $G$ be a finitely presentable group with def$(G)>0$ and such that $G'$
  is finitely generated and perfect. Then $G$ is isomorphic to $\mathbb Z$ or $\mathbb Z^2$." Its
  proof: "Indeed let $N$ be a subgroup of $G$ containing $G'$ and such that $G/N\simeq\mathbb Z$. As
  $G'$ is finitely generated $N$ is finitely generated and by Theorem 3 cd$(N)\le 1$, so $N$ is a
  free group, possibly trivial."

## What this lane landed

1. Imports:
   - `golod-shafarevich-deficiency-test-and-exponential-growth`;
   - `kochloukova-euler-zero-cyclic-quotient-kernels-have-cd-drop`.
2. `fp-subexponential-growth-forces-sqrt-mod-p-betti-bound`. A finite presentation `⟨X|R⟩` of a
   group of subexponential growth has `|X| − |R| ≤ 1`. Every finite-index `U` with `d_p(U) ≥ 2`
   satisfies `(d_p(U) − 2)² ≤ 4[G:U](|R| − |X| + 1)`. For deficiency one, `d_p(U) ≤ 2`.
3. `intermediate-growth-groups-have-deficiency-at-most-zero`. A group of intermediate growth has no
   presentation of positive deficiency. If it has a finite 2-dimensional `K(G,1)` with `χ = 0`,
   every finite-index subgroup has finite abelianization.

Novelty: none claimed. Each step directly combines pinned theorems. In the sources read we found no
explicit statement of item 3, but we did not search the literature exhaustively.

## Route taken for item 3

- Deficiency ≥ 2: the Golod–Shafarevich test applies to the presentation itself.
- Deficiency 1:
  - Subexponential growth gives amenability, and hence `b₁^(2) = 0`.
  - The presentation complex has `χ = 0`, so it is aspherical by the landed L² criterion.
  - Some surjection `G → Z` exists, and its kernel is finitely generated by Rosset's theorem (landed
    node).
  - Kochloukova's Theorem 3 with `n = 2` gives `cd(N) = cd(G) − 1 ≤ 1`, so the kernel is free.
  - A finitely generated free group has polynomial or exponential growth, a contradiction.

## Where both tools stop: deficiency zero

- A balanced presentation complex has `χ = 1`. For an infinite amenable group with a finite
  `K(G,1)`, Euler–Poincaré and the vanishing of ℓ²-Betti numbers force `χ = 0`. So the complex is
  never aspherical, and Kochloukova's hypothesis `χ(Y) = 0` is not available from the presentation.
- The Golod–Shafarevich count gives only `d_p(U) ≤ 2 + 2√[G:U]` for balanced presentations. That
  bound does not bite on the known intermediate-growth groups: in branch groups `d_p` of
  finite-index subgroups grows roughly like the logarithm of the index.
- `Z³ = ⟨a,b,c | [a,b],[b,c],[a,c]⟩` is balanced with polynomial growth, so balanced presentations
  are not excluded by growth-type-free arguments.
- Next questions:
  - (a) must a type-F group of intermediate growth of dimension ≥ 3 have finite virtual first Betti
    number? Theorem 3 still gives `cd(N) = cd(G) − 1` and `N` of type `FP_n`, but no freeness.
  - (b) does a balanced finite presentation of a group of intermediate growth force some
    finite-index subgroup to satisfy the Golod–Shafarevich test?

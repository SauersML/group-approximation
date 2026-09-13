# BS(1,2) in a finitely presented simple group with polynomial Dehn function: the Röver–Nekrashevych test (2026-09-13)

Lane `solve-bh-poly-dehn`. It tests the Röver–Nekrashevych route for the
`BS(1,2)` case of `np-word-problem-groups-embed-in-fp-simple-polynomial-dehn-groups`.
Sources were fetched as arXiv e-prints on the MSI login node, into
`/scratch.global/sauer354/poly-dehn/` (Cornulier–Tessera) and
`/scratch.global/sauer354/simple-bors/x_2305.15176/` (Zaremsky), and read from
their TeX.

## 1. Verbatim source lines

**Cornulier–Tessera, arXiv:1003.0148** (`BaumQ7.tex`)
- l.73 (abstract): "we embed the solvable Baumslag-Solitar groups in finitely presented metabelian groups with quadratic Dehn function."
- l.126–132: "Consider the two commuting matrices $A=\begin{pmatrix} n & 0 \\ 0 & n \\ \end{pmatrix}$, $B=\begin{pmatrix} 2 & 1 \\ 1 & 1 \\ \end{pmatrix}$ ($B$ can be replaced by any matrix in $\GL_2(\mathbf{Z})$ with two real eigenvalues not of modulus one). Define the group $$\Gamma_n=\mathbf{Z}[1/n]^2\rtimes_{(A,B)}\mathbf{Z}^2.$$"
- l.133: "Clearly, $\Gamma_n$ is finitely generated, since we can ``go up" in $\mathbf{Z}[1/n]^2$ by conjugating by $A$. Moreover, it contains an obvious copy of $\BS(1,n)$, namely $(\mathbf{Z}[1/n]\times\{0\})\rtimes(\mathbf{Z}\times\{0\})$."
- l.135–136, Theorem `gaga`: "The group $\Gamma_n$ is finitely presented with quadratic Dehn function."

**Zaremsky, arXiv:2305.15176** (`main.tex`)
- l.114: "Presumably, close relatives like the Higman--Thompson groups $T_d$ and $V_d$, which are virtually simple, also have polynomial Dehn functions, using similar arguments."
- l.128: "we suspect that the Dehn function of any $V_d(G)$ should be bounded above by some combination of the Dehn functions of $V_d(\{1\})$ and $G$, and this could perhaps be approached by looking at the action of $V_d(G)$ on a simply connected, cocompact truncation of the Stein--Farley complex of $V_d(G)$ (see, e.g., \cite{skipper21}). In any case, this is all beyond the scope of the present paper."
- l.181: "Thus, we get that Dehn functions are a quasi-isometry invariant of finitely presented groups."
- l.204–205, Definition: "An element of a self-similar group is \emph{rational} (or \emph{finite-state}) if it has finitely many states. Call the group itself \emph{rational} if every element is rational."
- l.208: "If every generator of the group is rational, then the same is true of every element, so it suffices to check rationality on the elements of some choice of generating set."
- l.229–230, Definition: "Call a self-similar group $G\le\Aut(\tree_d)$ \emph{weakly diagonal} if there exists a generating set $S$ for $G$ such that for all $s\in S$ with wreath recursion $s\leftrightarrow\rho_d(s)(s_1,\dots,s_d)$, each $s_i$ satisfies that $s_is^{-1}[G,G]$ has finite order in the abelianization $G/[G,G]$."
- l.240: "$\iota_w(h)$ is conjugate in $V_d(G)$ to $\iota_{w'}(h)$, via conjugation by an element of $V_d$, for any $h\in V_d(G)$ and any non-empty $w$ and $w'$."
- l.245–246, Definition: "Call a self-similar group $G\le \Aut(\tree_d)$ \emph{persistent} if for all $g\in G$, in the wreath recursion $g\leftrightarrow\rho_d(g)(g_1,\dots,g_d)$ we have $g_d=g$."
- l.249–250, Lemma: "For any self-similar group $G\le \Aut(\tree_{d-1})$, there is a faithful, persistent, self-similar action of $G$ on $\tree_d$. If the action on $\tree_{d-1}$ is rational then so is the action on $\tree_d$. If the action on $\tree_{d-1}$ is weakly diagonal then so is the action on $\tree_d$."
- l.258, Corollary: "Let $G\le\Aut(\tree_d)$ be a finitely generated, persistent, weakly diagonal, rational, self-similar group. Then $V_d(G)$ is virtually simple by virtue of $[V_d(G),V_d(G)]$ being simple and finite index, and there exists a quasi-retraction $V_d(G)\to G$. If $G$ is finitely presented, then so is $V_d(G)$ and we have $\delta_G\preceq \delta_{V_d(G)}$."

## 2. The host: parameter hosts fail, Cornulier–Tessera's host works

- **Polynomial parameter hosts with k >= 1 are not rational.** In the action of
  `polynomial-parameter-affine-groups-are-self-similar`, the state map
  substitutes `t -> a + p t`. So the elementary matrix `E_12(t)` has states
  `E_12(a_1 + p a_2 + ... + p^(j-1) a_j + p^j t)` along a path of length `j`.
  These are pairwise distinct, since the coefficient of `t` is `p^j`. So there
  are infinitely many states, and Zaremsky's Corollary does not apply to these
  hosts.
- **Cornulier–Tessera's `Gamma_2` works.** It acts affinely on `Z_3^2`. Its
  states keep the linear part and move integral translations inside a bounded
  box, so it is rational. Translations are commutators, since
  `[(2I,0),(I,v)] = (I,v)`, so it is weakly diagonal. It has quadratic Dehn
  function and contains `BS(1,2)`. See
  `cornulier-tessera-host-is-rational-weakly-diagonal-self-similar`.

## 3. The envelope

`S = [V_10(Gamma_2), V_10(Gamma_2)]` is finitely presented and simple, and it
contains `Gamma_2`, hence `BS(1,2)`.
- The embedding sends `g` to the product of `ι_w(g)` over `N` disjoint cones,
  where `N` is the order of the finite abelianization.
- `δ_S ≃ δ_(V_10(Gamma_2)) ≽ n^2`.

See `bs12-lies-in-fp-simple-rn-envelope-of-quadratic-dehn-host`.

## 4. What remains

`bs12-embeds-in-fp-simple-group-with-polynomial-dehn-function` follows from two
open upper bounds:
- `rover-nekrashevych-dehn-polynomial-in-host-and-vd`, which is Zaremsky's
  stated suspicion at TeX l.128;
- `higman-thompson-vd-has-polynomial-dehn-function` at `d = 10`.

`δ_V ≼ n^6` is on main for `d = 2`, from an unrefereed preprint. Nothing checked
here covers `d >= 3`.

## 5. Notes

- **Novelty.** Not searched: the session's web-search budget was exhausted. No
  novelty is claimed. The host lemma and the diagonal embedding are elementary.
- **Cairn.** `cairn check` was not run on MSI. Structural checks were done
  locally before landing: ids are at most 64 characters, `requires:` and
  `distinct_from:` name existing claims, and every artifact path exists.

# Polynomial Dehn functions of V_d: Lorrain's method, a projection reduction, and the remaining square-word gap (2026-09-13)

Lane `solve-vd-dehn-filling`. Targets:
- `higman-thompson-vd-has-polynomial-dehn-function`, needed at `d = 10`;
- `rover-nekrashevych-dehn-polynomial-in-host-and-vd`.

Verdict: partial. Neither target is settled. New nodes:
- `vd-dehn-bounded-by-standard-square-word-area` (reduction; its route needs two OPEN imports);
- `vd-expansion-cube-complex-is-cat0` (OPEN import);
- `cat0-cube-loops-bound-quadratic-square-diagrams` (OPEN import);
- `vd-standard-square-words-have-polynomial-area` (OPEN);
- route `vd-poly-dehn-via-square-word-projection` into the target.

A peer lane (session 01BmDA5RLRss4R7McN3D7Dwk, `thompson-v-has-quadratic-dehn-function`, artifact `zp-thompson-v-dehn-function-2026-09-13.md`) works on the sharp quadratic bound for `V = V_2`. None of its nodes were edited here.

## 1. Lorrain's d = 2 method, pinned from the TeX source

Source: arXiv:2608.03813 e-print, fetched on MSI as `Dehn_function_of_V_sextic.tex` (4638 lines).

- **Presentations.** §1.1 (l.86–153) uses Guba's finite presentation of `V` on `x_0, x_1, c_1, π_0`. Letters `x_n, c_n, π_n` are defined by conjugation, e.g. `π_n = π_1^(x_0^(n-1))`, and the infinite presentation `𝒱` guides which relators get diagrams.
- **Strategy.** §1.4, l.323–325, verbatim: "it is much easier to reduce words over the infinite presentations than over the finite ones. Therefore, we will find ways to realise van Kampen diagrams for the relators of $\mathscr{T}$ and $\mathscr{V}$ over the finite presentations of $T$ and $V$."
- **Normal form.** l.4022–4033 quotes Guba [GubaFTV, Theorem 3]: any word of length `n` equals `p π c_(n+1)^m q^(-1)` with MP-words `p, q` of complexity `<= n`, an irreducible π-word of rank `<= n`, and `0 <= m <= n+2`.
- **Recursion.** Theorem `thm:Dehn_function_of_V` (l.4039 on) cuts `w` in halves, normalizes both halves inductively, and merges. The merge cost is `O(n^6)`, which gives `δ_V ≼ n^6`.
- **What is d-specific.** Everything in §2–§4 (l.326–3975) is explicit diagrams over this particular finite presentation: relations in T, relations in V with x-, c- and π-letters, and the π-word rewriting over `S_∞`.
  - Running the method for `d = 10` needs a `d`-ary Guba normal form theorem with complexity bounds, plus `d`-ary analogues of the merge lemmas.
  - No source found here provides either. The rest of the recursion is `d`-independent.

## 2. A projection reduction replacing the level-by-level push-down

The earlier Attempt (lane solve-bh-rn-dehn) pushed a CAT(0) filling down through descending links. That argument multiplies costs level by level. Projecting instead through a canonical map `r` from vertices of the expansion cube complex `K_d` to `V_d` loses only a polynomial factor:

- `r([φ]) = φ ∘ o_v ∘ s_n^(-1)`: lexicographic order of the pieces, then a standard `n`-leaf tree code.
- Upward edges become finitely many standard words per height `n`, and squares become finitely many standard square words `Q_n`.
- A loop of length `L` fills in `K_d` with `<= L^2/8` squares at heights `<= k_0 + (d-1)L/2`.
- Projecting every square gives `δ_(V_d)(L) <= C·L + C·L^2·max_{n <= k_0 + C·L} A_d(n)`.
- Boundary conversion costs `O(L)`, because `r(g·x) = g·r(x)·ε(g,x)` with `ε` ranging over finitely many permutation elements at bounded height.

Full argument: `vd-dehn-square-word-projection-proof`. Imports still to check at source:
- Farley's CAT(0) cube complex for `V_d`. The Topology 2003 and IMRN 2003 papers aren't on arXiv, and the arXiv API was rate-limited.
- The minimal disc diagram lemma for CAT(0) cube complexes (Sageev 1995 / Wise). Sageev's PCMI notes, fetched, give the hyperplane facts but not the diagram lemma.

Why polynomial loss is intrinsic: vertex stabilizers are `S_n`, whose orbit spreads grow like `n log n` in `V_d`. So no equivariant bounded-spread projection exists, and a quadratic bound cannot come from this argument alone.

## 3. The remaining gap

`vd-standard-square-words-have-polynomial-area`: square words commute two disjoint splits at the standard tree, conjugated by leaf permutations. It suffices to give polynomial area over a finite presentation for:
1. the Coxeter relators on leaves of standard trees;
2. the split–permutation intertwining relators.

Cone transport disposes of every relator supported in one cone, and of Coxeter relators defined by comb-shift conjugation. The open part is far commutation `[π_1, π_m]` with polynomial-cost conversion between definitions. That is the `d`-ary analogue of Lorrain §3.3 and §4.

## 4. The Röver–Nekrashevych target

Not attempted beyond a remark, recorded under Attempts of `rover-nekrashevych-dehn-polynomial-in-host-and-vd`:
- The projection argument should run on the Skipper–Witzel–Zaremsky complex for `V_d(G)`, with `G`-labels on pieces.
- Square words then pick up `G`-relators on leaves, with area controlled by `δ_G`.
- The distortion estimate `(a)` still has to be proved: conjugate `ι_w(G)` to a standard cone at cost `O(|w|)`, then use Zaremsky's quasi-retraction (arXiv:2305.15176 l.258).

### 4a. Zaremsky's quasi-retraction, pinned (arXiv:2305.15176 e-print, `main.tex`, fetched on MSI)

- **Corollary `cor:simple_and_qr`, verbatim:** "Let $G\le\Aut(\tree_d)$ be a finitely generated, persistent, weakly diagonal, rational, self-similar group. Then $V_d(G)$ is virtually simple by virtue of $[V_d(G),V_d(G)]$ being simple and finite index, and there exists a quasi-retraction $V_d(G)\to G$. If $G$ is finitely presented, then so is $V_d(G)$ and we have $\delta_G\preceq \delta_{V_d(G)}$."
- **Its proof** takes the quasi-retraction from Skipper–Witzel–Zaremsky, Proposition 5.5, which was not read here.
- **Lemma `lem:v_simple`:** "$\iota_w(h)$ is conjugate in $V_d(G)$ to $\iota_{w'}(h)$, via conjugation by an element of $V_d$, for any $h\in V_d(G)$ and any non-empty $w$ and $w'$."
- **Consequence for distortion estimate (a).** The quasi-retraction controls the root copy of `G`, i.e. `|g|_G <= C|g|_{V_d(G)} + C`. Transport to `ι_w(G)` costs `O(|w|)` in the conjugator. But passing between `ι_1(g)` and root `g` goes through the wreath recursion `g = ρ(g) ι_1(g_1) ⋯ ι_d(g)` (persistence), whose states `g_i` need not be shorter than `g`. So the estimate isn't immediate from the corollary: it needs the explicit retraction of SWZ Proposition 5.5, which is still unproved here.

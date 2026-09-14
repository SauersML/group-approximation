# sk-expanders-limits: the finite models are expanders that converge to G_X (proposal)

Lane sk-expanders-limits, 2026-09-13. Line numbers refer to `sk/manuscript-disk-1646.tex` (md5 7b3dc4ec…).

## 0. Findings

1. **The brief's claim is already established on main.**
   - Node: `finite-simple-groups-converge-to-simple-kazhdan-group` (route `-proof`), for every `q`.
   - Content: the primitive return-word models `SL_(3N_k)(F_q)` converge to `EL_3(R)` in the space of marked groups, and their `PSL` quotients converge to `S`. All of them are marked quotients of the Kazhdan group `EL_3(F_q<t_1..t_(|A|+2)>)`, so they form uniform expanders.
   - Reviews: PASS after a correction (the marking for non-prime `q`) in `ex-review-groups-2026-09-12-part8.md` §8.6. The primitive-root step passed in `ex-pestov91-second-review-2026-09-13.md` N5.
   - Main also has a degree-four variant: `primitive-binary-words-give-four-regular-simple-expanders` and `four-regular-simple-expander-limits-encode-word-graphs`. I found no sk or ex review of those two.
   - I re-derived the `q = 2` case independently for this proposal (§2). No error.
2. **The earlier version on main carried this.** b965d63ba had it as Corollary (4), with Proposition `prop:marked` (`sk/manuscript-main-b965d63ba.tex` l.459–492, 693–695, 727–734). The Codex cut removed it. That version gave no Kassabov credit.
3. **Credit.**
   - Expander families `SL_(3l)(F_p)` built as quotients of `EL_3(Z<x_1,x_2>)` are due to Kassabov: arXiv:math/0502237v1 p. 5 ("These two observations allow us to consider the groups SL_{3l}(F_p) as quotients of EL_3(Z⟨x_1, x_2⟩)"), Theorem 9, p. 6.
   - Journal version: Invent. Math. 170 (2007) 297–326, doi:10.1007/s00222-007-0064-z, checked through Crossref.
   - Property (T) for `EL_3(F)` over the free algebra `F` is EJZ Theorem 1.1, which the note already cites.
   - The expansion is therefore not new. What is new is the limit: these expanders converge to an infinite simple Kazhdan group.
   - Every marked limit of finite groups is LEF, so this is a strengthening of the LEF clause, and its novelty is that of the main theorem (see sk-novelty).
4. **New this lane: an explicit constant** (landed, unreviewed).
   - EJZ §6.1 (arXiv v2 TeX l.2443–2447) proves `κ(EL_n(R), Σ) >= 1/(8(12√(2d)+2√(3n)+36√2))`, where `Σ` is the set of elementary matrices over `1, x_1, …, x_d`.
   - This `Σ` is exactly the note's generating set (l.94–95), with `d = |A|+2`.
   - So `G_X` and every model `SL_(3N)(F_2)` have Kazhdan constant `> 1/(8(12√(2(|A|+2))+6+36√2))`. For the Fibonacci subshift this is `> 1/727`, and the model Cayley graphs have spectral gap `> 3·10^(-8)`.
   - Nodes: `ejz-elementary-groups-explicit-kazhdan-constant` (+`-citation`), `subshift-el3-models-explicit-kazhdan-constant` (+`-proof`).
5. **Verdict for the note.**
   - Worth one paragraph: the finite models are finite simple groups, they converge to `G_X`, and their Cayley graphs are expanders.
   - Recommended: Option A, which replaces l.146–152. It turns the partial homomorphisms into honest homomorphisms from one Kazhdan group. That also settles the imprecision flagged independently by sk-referee-1 (P11) and sk-referee-2 (P3).
   - Fallback: Option B, an addition on top of their fix.
   - The explicit constant (Option C) should stay in Cairn: the reader gains no step, and the number is far from sharp.

## 1. Proposals

### Option A (recommended): honest homomorphisms, LEF, finite simple models and expanders
(a) Current l.146–152:
```latex
For a finite subset of $G$, include the entries of its elements,
their inverses, their differences, and all intermediate sums and
products needed for matrix multiplication. The resulting model is an
injective partial homomorphism into $\GL_{3N}(\F_2)$. Thus $G$ is LEF.
The regular permutation actions of these finite groups give sofic
models; their permutation matrices give hyperlinear models
\cite{Pestov}.
```
Replacement:
```latex
Let $N$ be the least period of $y$; it is at least the number of words
of length $2k+1$ in $X$. The ring homomorphism $\psi$ from the free
algebra $F=\F_2\langle t_+,t_-,t_a:a\in A\rangle$ to $M_N(\F_2)$ with
$\psi(t_\pm)=P^{\pm1}$ and $\psi(t_a)=D_y(e_a)$ is onto. Indeed the
rotations of $y$ are distinct, so products of the matrices
$P^iD_y(e_a)P^{-i}$ give every diagonal matrix unit. So $G$ and
$\EL_3(M_N(\F_2))=\SL_{3N}(\F_2)$ are quotients of $\EL_3(F)$ with
compatible generators. A word of length $n$ in these generators has
entries of degree at most $n$ in $F$, so for large $k$ the previous
paragraph shows that it is trivial in $G$ exactly when it is trivial in
$\SL_{3N}(\F_2)$. So these finite simple groups converge to $G$ in the
space of marked groups, and $G$ is LEF. Since $\EL_3(F)$ has
property~\textup{(T)}~\cite{EJZ}, their Cayley graphs form a family of
expanders, as in~\cite{Kassabov}. LEF groups are sofic, and sofic groups
are hyperlinear~\cite{Pestov}.
```
Bibliography, inserted between `GM` and `MorseHedlund`:
```latex
\bibitem{Kassabov}
M.~Kassabov, \emph{Universal lattices and unbounded rank expanders},
Invent. Math. \textbf{170} (2007), 297--326.
\doi{10.1007/s00222-007-0064-z}.
```
(b) The proof text is the replacement itself. The one standard fact left implicit is that the Cayley graphs of the quotients of a Kazhdan group, with the images of a fixed finite generating set, form an expander family as the orders grow. Here `|SL_(3N)(F_2)| → ∞` because `N → ∞`.

(c) Length: +9 source lines in the text and +4 in the bibliography. It supersedes P11 (+2) and P3 (+1), so the net cost over those fixes is about +7 text lines.

(d) Trade-off: stronger (finite simple approximants and uniform expansion), and the LEF step uses honest homomorphisms. It costs one paragraph, the notion "space of marked groups", and one bibliography item. The reader must trust no new fact: EJZ is already cited.

(e) Status: `finite-simple-groups-converge-to-simple-kazhdan-group` is established and reviewed PASS twice. I re-derived it in §2. The Pestov citation for LEF ⇒ sofic ⇒ hyperlinear follows sk-referee-2 P3; take its exact theorem numbers from there.

### Option B (fallback): add to whichever LEF paragraph the editor keeps
(a) Insert after l.149, or after the P3/P11 replacement:
```latex
Let $N$ be the least period of $y$; it is at least the number of words
of length $2k+1$ in $X$. The rotations of $y$ are distinct, so products
of the matrices $P^iD_y(e_a)P^{-i}$ give every diagonal matrix unit, and
with $P$ they generate $M_N(\F_2)$. So the finite groups are
$\EL_3(M_N(\F_2))=\SL_{3N}(\F_2)$. Marked by the images of the
generators of $G$, they converge to $G$ in the space of marked groups.
They are quotients of the Kazhdan group
$\EL_3(\F_2\langle t_1,\dots,t_{|A|+2}\rangle)$~\cite{EJZ} with
compatible generators, so their Cayley graphs form a family of
expanders~\cite{Kassabov}.
```
Plus the same bibliography item.

(c) +10 text lines, +4 bibliography lines. (d) Stronger at the cost of one paragraph, and it leaves the partial-homomorphism argument in place. (e) As in Option A.

### Option C (not recommended for the note): the explicit constant
Text, if wanted, after Option A or B:
```latex
Explicitly, the Kazhdan constant of $G$ and of these finite groups for
these generators is at least $1/(8(12\sqrt{2(|A|+2)}+6+36\sqrt2))$
\cite[\S6.1]{EJZ}; for the Fibonacci subshift it exceeds $1/727$.
```
(c) +3 lines. (d) It gives a number, but no step of the note uses it and the bound is far from sharp. (e) `subshift-el3-models-explicit-kazhdan-constant`, established from arXiv v2; the journal equation numbering was not checked.

### Notation to coordinate with the editor
- sk-referee-1 (its note on l.137) renames the window index `k` to `ℓ`. The `2k+1` above must follow that convention.
- `\SL` and `\EL` are already defined in the preamble (l.13, l.15). `t_\pm` needs no new macro.

## 2. Independent derivation (q = 2)

- **Models.**
  - `y` has least period `N`. `N` is at least the number of `(2k+1)`-words of `X`, and that number tends to infinity: a subshift with at most `C` words of every length has at most `C` points.
  - `P^iD(e_a)P^{-i} = diag_m(1[y_(m-i) = a])`. The product over `i ∈ [0,N)` with `a_i = y_(n-i)` is `diag_m(1[y_(m-i) = y_(n-i) for all i])`, which is `δ_(m≡n)` because the rotations are distinct.
  - With `P`, every matrix unit `E_(n,m) = δ_n P^(n-m)` lies in the image. So `ψ` is onto.
  - `EL_3(M_N(F_2)) = E_(3N)(F_2)`: a transvection between different blocks is `e_pq(E_ab)`, and one within a block is a commutator through a third block (as at l.210–214). This equals `SL_(3N)(F_2) = GL_(3N)(F_2)`.
- **Agreement on balls.**
  - A word of length `n` evaluates in `EL_3(F)` to a matrix with entries of degree `≤ n`.
  - Each monomial maps under `π` to `f u^j` with `f` of window within `[-n,n]` and `|j| ≤ n`, and under `ψ` to the same product of `D`'s and `P`'s.
  - For `k ≥ n` and `N > 2n`, l.137–144 give `φ_y(π(p)) = ψ(p)`, and `φ_y(π(p)) = 0` iff `π(p) = 0`.
  - Apply this to the entries of `word − I`: the word is `1` in `G` iff it is `1` in `SL_(3N)(F_2)`. That is marked convergence.
  - LEF follows: for words of length `≤ n`, the assignment is well defined, injective, and multiplicative on products of length `≤ n`.
- **Expanders.**
  - `κ(SL_(3N)(F_2), Σ_N) >= κ(EL_3(F), Σ) > 0`, because a unitary representation of a quotient is a representation of `EL_3(F)` with the same invariant vectors.
  - For the regular representation on `ℓ²_0` and a symmetric set `S`, `<(I−M)v,v> = (2|S|)^(-1) Σ_s ||sv−v||² >= κ²/(2|S|)`.
  - `|S| ≤ 6(|A|+3)` is fixed and the orders grow, so the Cayley graphs form an expander family.

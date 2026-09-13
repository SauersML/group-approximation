# Labbé's substitution: verbatim imports, and polynomial pattern complexity of Ω_U

Lane `un-labbe-ring`, 2026-09-13. Status: import read from source; theorem ESTABLISHED (unreviewed).

Source: S. Labbé, *A self-similar aperiodic set of 19 Wang tiles*, arXiv:1802.03265. The TeX source
(`article1.tex`, e-print dated 2019-07-11) was fetched on MSI with `curl https://arxiv.org/e-print/1802.03265`
and read there. Line numbers below refer to that file. Notation as in the source: `U` is the 19-tile set, `Ω_U`
its Wang shift, `ω = α∘β∘γ`, and `shape(w) ∈ N^2` for a 2-dimensional word `w`.

## 1. Verbatim statements used

1. **Theorem 1** (l.295): "The Wang shift $\Omega_\U$ is self-similar, aperiodic and minimal."
2. **Definitions** (l.883–891): "We say that a $d$-dimensional morphism $\omega:\A\to\A^{*^d}$ is
   \emph{expansive} if for every $a\in\A$ and $K\in\N$, there exists $m\in\N$ such that
   $\min(\shape(\omega^m(a)))>K$. We say that $\omega$ is \emph{primitive} if there exists $m\in\N$ such that
   for every $a,b\in\A$ the letter $b$ occurs in $\omega^m(a)$."
   A 2-dimensional morphism satisfies (l.822) "$\omega(u\odot^i v) = \omega(u)\odot^i \omega(v)$."
3. **Theorem** `thm:exist-homeo` (l.1394): "Let $\T$ be a Wang tile set and let $\Omega_\T$ be its Wang shift.
   If there exists a subset $M\subset\T$ of markers in the direction $\be_i\in\{\be_1,\be_2\}$, then there exists
   a Wang tile set $\S$ and a $2$-dimensional morphism $\omega:\Omega_\S\to\Omega_\T$ such that
   $\omega(\S)\subseteq (\T\setminus M)\cup \left((\T\setminus M)\odot^i M\right)$ which is recognizable in the
   Wang shift $\Omega_\S$ and surjective up to a shift, i.e.,
   $\omega(\Omega_\S)\cup\sigma^{\be_i}\omega(\Omega_\S)=\Omega_\T$."
4. **Propositions** `prop:wecandesubstituteU` (l.1782) and `prop:wecandesubstituteV` (l.1947): "There exists a tile
   set $\V$ of cardinality 21 and a $d$-dimensional morphism $\alpha:\Omega_\V\to\Omega_\U$ that is recognizable
   in $\Omega_\V$ and $\alpha(\Omega_\V)\cup\sigma^{\be_2}\alpha(\Omega_\V)=\Omega_\U$." The same holds with
   "$\W$ of cardinality 19", "$\beta:\Omega_\W\to\Omega_\V$" and "$\sigma^{\be_1}$". Both proofs apply
   Theorem `thm:exist-homeo`, with markers in directions `e_2` and `e_1` respectively.
5. **Lemma** `lem:homeoUtoW` (l.2109): "$\U$ and $\W$ are equivalent Wang tile sets. The map $\gamma:\U\to\W$
   defines a $d$-dimensional morphism $\gamma:\Omega_\U\to\Omega_\W$ which is a bijection."
6. **Lemma** `lem:omega-is-primitive` (l.2188): "The morphism $\omega$ is primitive." Its proof: "whose $7$-th power
   $M^7$ is positive. Therefore $M$ is a primitive matrix and the morphism is primitive."
7. **Proposition** `prop:pre-main` (l.2269): "The $d$-dimensional morphism $\omega:\Omega_\U\to\Omega_\U$ defined as
   $\omega=\alpha\circ\beta\circ\gamma$ is expansive, recognizable in $\Omega_\U$ and satisfies
   $\Omega_\U = \omega(\Omega_\U) \cup\sigma^{\be_1}\omega(\Omega_\U) \cup\sigma^{\be_2}\omega(\Omega_\U)
   \cup\sigma^{\be_1+\be_2}\omega(\Omega_\U)$." Its proof: "$\omega$ is primitive and sends at least one letter to
   a $2$-dimensional word of shape $(2,2)$. Thus it is expansive."
8. **Corollary** `cor:OmegaU-is-aperiodic` (l.2313): "$\overline{\omega(\Omega_\U)}^{\sigma}=\Omega_\U$,
   $\Omega_\U$ is self-similar and aperiodic."
9. **Lemma** `lem:existence-omega-representation` (l.973): for a $d$-dimensional morphism $\omega:X\to Y$ of
   subshifts, "$Y=\overline{\omega(X)}^{\sigma}$" iff "$\L_Y=\overline{\omega(\L_X)}^{Fact}$".
10. **Lemma** `lem:50tiles-2x2-in-OmegaU` (l.2334): "$\L(\X_\omega)\cap \U^{(2,2)} = \L(\Omega_\U)\cap
    \U^{(2,2)}=S$". The displayed set `S` (`article1_all_2x2_factors.tex`) has 50 entries, counted on MSI.
11. **Proposition** `prop:OmegaU-is-self-similar` (l.2346): "$\Omega_\U$ is minimal. More precisely,
    $\Omega_\U=\X_\omega$ where $\omega=\alpha\beta\gamma$."
12. **Cover step**, from the proof of `lem:substitutive-equivalent-conditions` (l.1103–1112), for a language with
    $L=\overline{\omega(L)}^{Fact}$: "Let $z\in L$. Since $\omega$ is expansive, let $m\in\N$ such that the image
    of every letter $a\in\A$ by $\omega^m$ is larger than $z$, that is, $\shape(\omega^m(a))\geq\shape(z)$ for all
    $a\in\A$. We have $z\in\overline{\omega^m(L)}^{Fact}$. By the choice of $m$, $z$ can not overlap more than two
    block $\omega^m(a)$ in the same direction. Then, there exists a word $u\in L$ of shape $(2,\dots,2)$ such that
    $z$ is a subword of $\omega^m(u)$."

## 2. Theorem (polynomial complexity)

Let `p(n) = |L(Ω_U) ∩ U^((n,n))|` be the number of `n × n` patterns of `Ω_U`. For every `n >= 1`,
`p(n) <= 50 · 4^(8⌈log_2 n⌉ + 1) <= 50 · 4^9 · n^16`.

So `p` is polynomial, and `m ↦ m^2 p(2m+1)` grows polynomially, hence subexponentially.

## 3. Proof

**Step 1: images of letters have shape at most (2,2).** By Theorem `thm:exist-homeo` (item 3), applied in item 4:
- `α` sends every letter of `V` to a letter of `U` or to a domino in direction `e_2`;
- `β` sends every letter of `W` to a letter of `V` or to a domino in direction `e_1`;
- `γ` sends letters to letters (item 5).

So `β(γ(u))` has shape `(1,1)` or `(2,1)`. By the concatenation rule (item 2), `α` of a letter has shape `(1,1)` or
`(1,2)`, and `α` of a horizontal domino has shape `(2,h)` with `h ∈ {1,2}`. Hence `shape(ω(u)) <= (2,2)`
coordinatewise for every `u ∈ U`.

**Step 2: shapes of iterates.** Let `x ∈ L(Ω_U)` have shape `(w,h)`. `ω` maps legal words to legal words (proof of
item 9, "(i)⇒(ii)", with `X = Y = Ω_U` by item 8). By the concatenation rule, the image of `x` is obtained column
by column: all images of letters in one column have a common width, and the width of `ω(x)` is the sum over the `w`
columns of these widths. The same holds for rows and heights.
- By Step 1, `shape(ω(x)) <= (2w, 2h)`. So `shape(ω^m(a)) <= (2^m, 2^m)` for every letter `a` and `m >= 0`.
- By item 6, every letter occurs in `ω^7(a)` for every `a`. By item 7, some letter `b_0` has
  `shape(ω(b_0)) = (2,2)`. The column of `ω^7(a)` containing `b_0` contributes width 2 to `ω^8(a)`, and every
  column contributes at least 1. Hence `shape(ω^8(a)) >= (2,2)` for every letter `a`.
- Applying the column rule to `ω^8` (a composite of 2-dimensional morphisms on legal words, whose letter images
  all have both sides `>= 2`): `shape(ω^8(x)) >= (2w, 2h)`. Hence `shape(ω^(8j)(a)) >= (2^j, 2^j)` for all
  letters `a` and `j >= 0`.

**Step 3: cover and count.** Put `L = L(Ω_U)`. By items 8 and 9, `L = \overline{ω(L)}^{Fact}`. Fix `n >= 1` and
`m = 8⌈log_2 n⌉`. By Step 2, `shape(ω^m(a)) >= (n,n)` for every letter `a`.

By the cover step (item 12), every `z ∈ L ∩ U^((n,n))` is a subword of `ω^m(u)` for some `u ∈ L ∩ U^((2,2)) = S`,
and `|S| = 50` (item 10). By Step 2, `ω^m(u)` has shape at most `(2^(m+1), 2^(m+1))`, so it has at most
`4^(m+1)` subwords of shape `(n,n)`. Hence

`p(n) <= 50 · 4^(m+1) = 50 · 4^(8⌈log_2 n⌉ + 1) <= 50 · 4^9 · n^16`. ∎

**Sanity checks.**
- `n = 1`: the bound is `200 >= 19`.
- The exponent 16 is an artifact of the crude doubling period (8 steps). The argument uses only an expansive,
  primitive 2-dimensional morphism with bounded letter images and a self-similar language.

## 4. What is not claimed

- **Sharp order `p(n) = O(n^2)`.** Expected, not proved here. Two routes:
  1. Linear repetitivity of `Ω_U`, which needs the widths and heights of `ω^m(a)` to grow at comparable rates
     uniformly over letters (balance). The source does not state this.
  2. A face count of the arrangement of translates of the polygonal Markov partition boundary
     (`labbe-shift-is-a-toral-rotation-coding`, items 5 and 6). By minimality every pattern occurs in a generic
     tiling, so `p(n)` is at most the number of faces.

  Neither is needed downstream.
- **Recognizability** is imported (item 7) but not used in the count. The count uses only the cover step, which
  holds for any self-similar language of an expansive primitive morphism.

## 5. Consequence recorded (not a new route)

With `subexponential-complexity-zd-subshift-rings-have-rank-models` (un-open-4, unreviewed), `LC(Ω_U, F_q) ⋊ Z^2` has
a unital rank model over `F_q` with no further input. That discharges the rank-model assumption carried by
`rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group` for Labbé's ring. The remaining half there is
non-matriciality: `labbe-wang-shift-crossed-product-is-not-exactly-matricial`, whose exact torus form is
`torus-quantum-tilings-decide-matriciality-of-sft-rings`.

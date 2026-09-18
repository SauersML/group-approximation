---
rg: 2
id: thompson-f-not-co-amenable-in-known-hosts-proof
kind: route
title: Push the fixed-point measure (T, V) or the hyperfinite Lebesgue orbit relation (Lodha--Moore, Monod) of F up to the host
target: thompson-f-is-not-co-amenable-in-its-known-nonamenable-hosts
requires:
  - co-amenable-subgroups-transfer-hyperfinite-orbit-relations
  - thompson-f-interval-orbit-relation-is-hyperfinite
  - thompson-f-is-a-subgroup-of-lodha-moore-group
---

**Lemma E (Eymard, proved in place).** Let `H ≤ G` be co-amenable with invariant mean `m` on
`G/H`. Let `X` be a compact `G`-space and `μ` an `H`-invariant Borel probability on `X`. Then
`X` carries a `G`-invariant Borel probability.

*Proof.*
- For `φ ∈ C(X)` set `Pφ(gH) = ∫ φ(g x) dμ(x)`. This is well defined because `μ` is
  `H`-invariant, and `‖Pφ‖_∞ ≤ ‖φ‖_∞`.
- `P(φ ∘ k)(gH) = Pφ(kgH)`, so `ν(φ) = m(Pφ)` is a positive, unital, `G`-invariant functional
  on `C(X)`.
- By Riesz, `ν` is a `G`-invariant Borel probability. ∎

**Lemma I (invariant measures of `F` on the interval).** Let `x_0(t)` be `t/2` on `[0,1/2]`,
`t − 1/4` on `[1/2,3/4]`, and `2t − 1` on `[3/4,1]`. Then `x_0 ∈ F` and `x_0(t) < t` on
`(0,1)`. Let `K ⊂ (0,1)` be compact.
- Iterates of `x_0` push `max K` to `0`, so `x_0^N(K) ⊂ (0, min K)` for some `N`.
- Since `x_0` is increasing, the sets `x_0^{jN}(K)` for `j ≥ 0` are pairwise disjoint.
- For an `F`-invariant probability `μ` they have equal mass, so `μ(K) = 0`.

Hence every `F`-invariant Borel probability on `[0,1]` is supported on `{0,1}`.

**Case 1 (circle hosts).**
- An `F`-invariant probability on `S^1` pulls back to `[0,1]`, so by Lemma I it is `δ_0`.
- If `F` were co-amenable in `G`, Lemma E applied to `δ_0` would give a `G`-invariant
  probability. It is `F`-invariant, hence equal to `δ_0`, so `G` fixes `0`. Contradiction.
- `T ∋ (t ↦ t + 1/2 mod 1)` does not fix `0`.

**Case 2 (Cantor hosts).**
- The binary-value map `β : 2^N → [0,1]`, `β(ξ) = Σ ξ_i 2^{-i}`, is continuous. For prefix
  replacement `s_i ξ ↦ t_i ξ` it satisfies `β(s ξ) = β(s) + 2^{-|s|} β(ξ)`. So it intertwines
  `F` on `2^N` with the dyadic piecewise-linear `F` on `[0,1]`.
- An `F`-invariant probability `μ` on `2^N` has `β_*μ` supported on `{0,1}`, by Lemma I. Since
  `β^{-1}(0) = {0^∞}` and `β^{-1}(1) = {1^∞}`, `μ` is supported on `{0^∞, 1^∞}`.
- A `G`-invariant probability `ν` from Lemma E is `F`-invariant, so
  `ν = aδ_{0^∞} + (1−a)δ_{1^∞}`. Its set of atoms `S ⊆ {0^∞, 1^∞}` is nonempty and
  `G`-invariant, so it contains a point whose whole `G`-orbit lies in `{0^∞, 1^∞}`.
- Hypothesis: `G·0^∞ ⊄ {0^∞, 1^∞}` and `G·1^∞ ⊄ {0^∞, 1^∞}`. This contradicts the previous
  step. (The hypothesis is sharp for the method: if some `G`-orbit stays inside the pair, the
  uniform measure on that orbit is `G`-invariant.)
- In `V`, the swap `v(0ξ) = 1ξ`, `v(1ξ) = 0ξ` maps `0^∞ ↦ 10^∞` and `1^∞ ↦ 01^∞`, both
  outside the pair.

**Imports for Cases 3–4, verbatim.**
- Y. Lodha, J. T. Moore, arXiv:1308.4250, TeX `vN_fp.tex`, fetched 2026-09-17.
  - l.290–294: "$E$ is \emph{$\mu$-amenable} if, after discarding a $\mu$-measure $0$ set, $E$
    is the orbit equivalence relation of an action of $\Zbb$. (This is not the standard
    definition, but it is equivalent by \cite{Connes}.)"
  - l.303–306: "If $\Gamma$ is a countable dense subgroup of $\PSL_2(\Rbb)$, then the action of
    $\Gamma$ on the real projective line induces an orbit equivalence relation which is not
    amenable with respect to Lebesgue measure."
  - l.329–336: "Since $K$ contains $\PSL_2(\Zbb)$ as a proper subgroup, it is dense in
    $\PSL_2(\Rbb)$ and hence by Theorem \ref{PSL2_nonamen}, the orbit equivalence relation of
    its action on the real projective line is not amenable with respect to Lebesgue measure.
    By Theorem \ref{amen_OE}, it is sufficient to show that $G_0$ induces the same orbit
    equivalence relation on $\Rbb \setminus \Qbb$."
  - The remaining lines l.337–346 verify that claim through the words `bca^{-1}c^{-1}a`, `aba`
    and `ba^{-3}`.
  - l.249–251 and l.259–262: `Φ : 2^N → R ∪ {∞}` "is one-to-one except at $\xi$ which are
    eventually constant", and it is two-to-one there. l.268–271: "Thurston observed that the
    functions $a$ and $b$ from the introduction become the generators $a$ and $b$ for
    Thompson's group $F$ defined above when ``conjugated'' by $\Phi$."
  - l.211–213: "The collection of all such functions from $2^\Nbb$ to $2^\Nbb$ defined in this
    way is \emph{Thompson's group $F$}."
- N. Monod, arXiv:1209.5229, TeX `vn_pnas3.tex`, fetched 2026-09-17.
  - l.206: "We define $G(A)$ to be the subgroup of $G$ given by all elements that are piecewise
    in $\psl2{A}$ with all interval endpoints in $P_A$. We write $H(A)=G(A)\cap H$".
  - l.310–312: "Now $H(A)$ is a countable group and $\Gamma:=\psl2A$ is a countable dense
    subgroup of $\psl2{\RR}$." and "Restricting to $\PP^1\setminus \{\infty\}$, we deduce from
    Proposition~\ref{prop:orbit} that the relation induced by the $H(A)$-action is also
    non-amenable."

**Step A (the relation of `F` on the line is hyperfinite).**
- Let `C ⊂ R` be the countable set of `Φ`-images of eventually constant sequences. Off
  eventually constant sequences both `Φ` and `β` are injective Borel maps, and prefix
  replacement preserves eventual constancy.
- So `h = β ∘ Φ^{-1} : R \ C → (0,1) \ Z[1/2]` is a Borel bijection. By l.268–271 it conjugates
  the action of `⟨a, b⟩` on `R \ C` into the prefix action of `F`, and by Case 2 into dyadic
  piecewise-linear maps in `F`.
- `a` and `b` are piecewise Möbius with finitely many pieces, so Lebesgue measure `λ` is
  `⟨a,b⟩`-quasi-invariant. Hence `h_*(λ|R\C)` is an `F`-quasi-invariant `σ`-finite Borel
  measure on `(0,1)`.
- By `thompson-f-interval-orbit-relation-is-hyperfinite`, `(R_F, h_*λ)` is hyperfinite.
  Transporting back and discarding the null set `C`, `R_{⟨a,b⟩}` is `λ`-hyperfinite on `R`.

**Case 3 (Lodha–Moore).**
- `G_0` is countable and acts on `R` by piecewise Möbius homeomorphisms, so `λ` is
  quasi-invariant.
- `F = ⟨a,b⟩ ≤ G_0` by `thompson-f-is-a-subgroup-of-lodha-moore-group`.
- Suppose `F` were co-amenable in `G_0`. Step A and
  `co-amenable-subgroups-transfer-hyperfinite-orbit-relations` make `R_{G_0}` `λ`-hyperfinite,
  hence `λ`-amenable in the Lodha–Moore sense by Connes–Feldman–Weiss (see the trust surface).
- By l.329–336 `R_{G_0}` agrees on `R \ Q` with the relation of `K`, which is not
  `λ`-amenable. Contradiction.

**Case 4 (Monod).**
- Let `A` be countable with `A ≠ Z` and `0 ∈ P_A`.
  - `PSL_2(Z) ≤ PSL_2(A)` is transitive on `Q ∪ {∞}`, and `P_A` is `PSL_2(A)`-invariant, so
    `Q ⊆ P_A`.
  - `a` and `b` are piecewise in `PSL_2(Z)`, since `t/(1−t)` and `3 − 1/t` have integer
    matrices of determinant 1. They fix `∞` and have rational breakpoints, and `PSL_2(Z)` maps
    `Q` to `Q`. So every element of `⟨a,b⟩` has rational breakpoints and lies in `H(A)`.
  - `A` is dense: a subring of `R` other than `Z` contains an irrational or some `1/q` with
    `q ≥ 2`.
- If `F` were co-amenable in `H(A)`, Step A and the transfer lemma would make `R_{H(A)}`
  hyperfinite on `P^1 \ {∞}` for the Lebesgue class. This contradicts l.312. ∎

**Trust surface.**
- The different standard definitions of `μ`-amenability of a countable relation agree:
  - Borel-amenable on a conull set, as in the transfer lemma;
  - hyperfinite on a conull set;
  - generated mod null sets by one automorphism, the Lodha–Moore definition;
  - an invariant measurable field of means, the Monod definition.

  This agreement is the Connes–Feldman–Weiss theorem, anchored verbatim by Elek–Timár l.299 and
  Lodha–Moore l.294. The implication "hyperfinite ⇒ generated by one transformation mod null
  sets" is the standard form of it and was not re-read.
- The orbit identity for `G_0` is used exactly as Lodha–Moore sketch it.

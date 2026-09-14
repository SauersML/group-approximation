# Kervaire--Laudenbach with torsion: the pivot-letter case of the two-level chain (2026-09-14)

Lane `hl-kl-howie-overlap`. The target was gap 1 of
`research/artifacts/hl-howie-systems-2026-09-13.md`: pairs of equations sharing
unknowns in the square system over a torsion-free subgroup of finite index.

**Verdict: partial.**
- Landed `kl-pivot-letter-words-inject-over-torsion-free-by-finite`
  (ESTABLISHED; elementary plus the Klyachko import).
- Landed `kl-two-level-words-over-torsion-free-by-cyclic` (OPEN).
- Kervaire--Laudenbach with torsion stays OPEN. No counterexample was found, and
  no relative-asphericity certificate was built.

## 1. Pins

Sources fetched on MSI into `/scratch.global/sauer354/hl-kl-howie-overlap/src/`.

### 1.1 Klyachko--Mikheenko, arXiv:2204.01122 (`GR-E.TEX`)

- l.34--45: "Yet another Freiheitssatz: Mating finite groups with locally
  indicable ones", Anton A. Klyachko, Mikhail A. Mikheenko.
- l.163--172: "Brodskii--Howie--Short theorem [B80], [B84], [How82], [Sh81].
  The natural mappings C→(C*D)/<<w>>←D are injective if the groups C and D are
  locally indicable, and the word w∈C*D is not conjugate to an element of C∪D."
- l.206--217: "Freiheitssatz. If groups C and D are locally indicable, K is a
  GR*-group, and the image of a word w∈C*D*K under the natural homomorphism
  C*D*K→C*D is not conjugate to an element of C∪D, then the natural mappings
  C*K→(C*D*K)/<<w>>←D*K are injective." Followed by: "examples of GR*-groups are
  all hyperlinear groups, in particular, all free products of finite groups."
- l.486: "GR=GR*={all groups} (Howie's conjecture)."
- l.502--511: "Main theorem. Suppose that a group G contains a normal subgroup A,
  which is GR-group, and the quotient group G/A is locally indicable. Then an
  equation w(x,y,...)=1 is solvable over G if the G/A-content of w(x,y,...) is
  not conjugate to an element of G/A in (G/A)*F(x,y,...)."

**Relevance.** These results cover GR-by-locally-indicable coefficients. The
groups here are extensions in the other order: a torsion-free kernel with a
finite quotient, and a nontrivial finite group is not locally indicable. So the
Main theorem does not apply.

### 1.2 Klyachko--Mikheenko--Olshanskii, arXiv:2608.28045v2 (`UNI-RA-E.TEX`)

- l.38: "Solvability of unimodular equations in groups and Lie algebras".
- l.68--71, abstract: "Our results implies, in particular, that a finitely
  generated solvable group G is nilpotent if and only if it contains a solution
  to any unimodular equation, i.e., an equation of the form ∏g_ix^{n_i}=1, where
  g_i∈G and ∑n_i=±1."
- l.119--124: "in [K93] (see also [FeR96]), it was shown that any unimodular
  equation over torsion-free group has a solution in some overgroup; while it is
  unknown whether a similar assertion holds for arbitrary nonsingular equations."

This is about solutions *in* the group. It has nothing on overgroups of groups
with torsion.

### 1.3 Forester--Rourke, arXiv:math/0412274 (`multi4.tex`)

- l.89--91: "A long-standing conjecture [Ho] states that for any relative
  2–complex (L,K), if the exponent matrix is nonsingular, then π_1(K)→π_1(L) is
  injective."
- l.98--106: "Theorem. Let (L,K) be a layered relative 2–complex with π_1(K)
  torsion-free. If the exponent matrix is invertible over Z then (a)
  π_1(K)→π_1(L) is injective, and (b) the inclusion-induced map
  Zπ_1(L)⊗_{Zπ_1(K)}π_2(K)→π_2(L) is an isomorphism."
- l.108--112: "(L,K) is layered if L−K has equal numbers of 1– and 2–cells and L
  is formed from K by alternately adding 1–cells and 2–cells. In terms of the
  associated relative presentation it means that the generators and relators can
  be added alternately."
- l.157--164, Remark: "the exponent matrix hypothesis can be relaxed to allow
  layered relative 2–complexes for which each pair (K_{i+1},K_i) is amenable ...
  The result also solves the adjunction problem for systems of generators and
  relators which can be transformed, by a change of variables, into a layered
  amenable system."
- l.173--176: "Theorem. If (L,K) is relatively aspherical then every finite
  subgroup of π_1(L) is contained in a unique conjugate of π_1(K)."

### 1.4 Klyachko--Thom, arXiv:1509.01376 (`main.tex`)

- l.113: "Later, Howie [MR614523] proved the same result for locally indicable
  groups and conjectured it to hold for all groups -- we call that Howie's
  Conjecture. Again, Connes' Embedding Conjecture implies Howie's Conjecture --
  and more specifically, every hyperlinear group satisfies Howie's Conjecture."
- l.116: "Equations in one variable with at most three occurrences of the
  variable are solvable by a result of Howie [MR695646], which however also
  reduces this to the residually finite case and uses the results of
  Gerstenhaber-Rothaus. Similar results have been proved for non-singular
  equations with four [MR1002920] and five [MR2324624] occurrences of variables."

The MR items were not read. Their identification with the length-three,
length-four and length-five papers is unverified.

**Not read at source:** Howie 1981, Krstic 1985, and the length-four and
length-five papers. The arXiv API search returned nothing from MSI; the Klyachko
author feed was read for titles instead.

## 2. What is proved

Setting: `P = H<a>`, `H` torsion-free, `a` normalizes `H`, `a^n in H`. The word
is `w = t a V b` with `V in H * <t>` and `ab in H`.

Over the kernel `M = H * <t_0> * ... * <t_(n-1)>` of `P * <t> -> P/H`, the
rewritten conjugates form one cycle:

    r_i = t_i · V^(i+1)(t_(i+1)) · h_i,        t_n = a^n t_0 a^(-n).

The unknown `t_i` occurs exactly once in `r_i`. Eliminating `t_0, ..., t_(n-2)`
along the cycle leaves one equation `R` over `H`, of degree `1 - (-d)^n` with
`d = deg_t V`. At `d = 0`, Klyachko's theorem solves `R`.

When `n` is a power of `p`, this is the `|Lambda| = 2` case of
`kl-p-power-index-reduces-to-p-nonsingular-square-systems`, with a single letter
at the base level.

**Example.** Take `a^2 = 1` and

    w = t a t h_1 t^-1 h_2 t h_3 t^-1 h_4 t h_5 t^-1 h_6 a h_7,

with all `h_j in H`. The word has seven letters, shape `++-+-+-`, and six sign
changes. The returning sign-change coefficient `h_6 a h_7` has order 2 exactly
when `sigma(h_7 h_6) = (h_7 h_6)^(-1)`. The theorem injects `P` whatever `H` is.

## 3. Model test (MSI job 779197, `chaintest.py` in the artifact directory)

The test uses finite `P` with `H` normal. Torsion is allowed, since the rewriting
never uses torsion-freeness.
- `V` is random, of length at most 6, with exponents in `{±1, ±2}`.
- `g in H` is random, and `b` is forced so that `w(g) = 1`.
- It checks that the `Phi`-recursion from `s = a^(n-1) g a^(-(n-1))` returns
  `t_i = a^i g a^(-i)`, that `R(s) = 1`, and that every `r_i` vanishes.

Output, verbatim:

```text
S4: H=V4, a=(0123), a^2 in H, z!=1: n=2 z_is_1=False trials=400 failures=0
A4: H=V4, a=(012), n=3: n=3 z_is_1=True trials=400 failures=0
S4: H=A4, a=(01), n=2: n=2 z_is_1=True trials=400 failures=0
S5: H=A5, a=(01)(234)... n=2 via (01): n=2 z_is_1=True trials=400 failures=0
C8: H=<x^4>, a=x, n=4, z!=1: n=4 z_is_1=False trials=200 failures=0
S4: H=A4, a=(0123), z=(02)(13): n=2 z_is_1=False trials=400 failures=0
deg R for d=0: [1, 1, 1, 1, 1] formula [1, 1, 1, 1, 1]
deg R for d=-2: [-1, -3, -7, -15, -31] formula [-1, -3, -7, -15, -31]
deg R for d=1: [2, 0, 2, 0, 2] formula [2, 0, 2, 0, 2]
deg R for d=2: [3, -3, 9, -15, 33] formula [3, -3, 9, -15, 33]
deg R for d=-1: [0, 0, 0, 0, 0] formula [0, 0, 0, 0, 0]
TOTAL_FAILURES 0
```

(The label of the fourth case is loose: the element used is `a=(01)`.)

## 4. Why the pivot method needs two levels, and where the chain stops

**Two levels.** This is an observation, not a node. Suppose that after gauging,
the base level `x` carries a single letter and the level set is `Lambda ⊆ Q`.
- `rho_q` can eliminate only `y_(qx)`. The expression for it contains `y_(q λ)`
  for `λ in Lambda \ {x}`.
- Draw an edge `q -> q λ x^(-1)` for each such `λ`. Along a directed cycle that
  avoids the last equation `q_0`, the pivot unknown of the last equation
  eliminated reappears in its own equation after substitution. So it no longer
  occurs once, barring free cancellation.
- In `Q \ {q_0}`, every vertex has out-degree at least `|Lambda| - 2`, since at
  most one edge goes to `q_0`. For `|Lambda| >= 3` a directed cycle avoiding
  `q_0` therefore exists.
- So elimination down to one equation needs `|Lambda| = 2`. After localization
  that is the cyclic case of the claim.
- With `|Lambda| = 2` and `d != 0`, the last equation has degree
  `1 - (-d)^n != ±1`.

**The closing equation.** Adjunction along the cycle works step by step:
- From `H * <t_(n-1)>`, adjoin `t_(n-2)` through `r_(n-2)`, then `t_(n-3)`, and
  so on down to `t_0`.
- Each step is Klyachko, or Forester--Rourke 1.3, when the new unknown has
  exponent `±1`. Relative asphericity together with l.173--176 keeps each stage
  torsion-free, provided the relator is not a proper power.
- The final relator `r_(n-1)` introduces no new unknown. It is a pure constraint.

The change-of-variables remark in 1.3 does not apply. A layered system needs a
first equation in one unknown, while every `r_i` involves two.

## 5. Exact remaining gap

`kl-two-level-words-over-torsion-free-by-cyclic` asks for the two-level cycle at
every distribution of letters. The first open instance has the base level
carrying at least two letters, so no unknown can be eliminated. Beyond two
levels the gap is the general square system of `hl-howie-systems` section 4.

A relative-asphericity failure certificate over a finite group was not built. KL
holds over finite groups, so such a certificate would only show that the
asphericity route breaks; it could not produce a KL failure.

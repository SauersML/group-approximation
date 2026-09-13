# Idea lane bh-noncomm-hosts (2026-09-13)

Target: `boone-higman-conjecture`.

Lens: run the self-similar affine host technique over noncommutative
coordinate rings. The commutative version is what put every linear group in
B_A: `char-zero-linear-pbh-via-polynomial-self-similar-hosts`,
`positive-char-polynomial-affine-groups-are-self-similar`,
`char-p-linear-groups-satisfy-permutational-boone-higman`.

Status: exploration only. No node changed, and nothing is claimed established.

## Architectures on main

Main already has two ways to make `R^n ⋊ Γ` self-similar.

- **(P) Principal-ideal architecture.** `principal-ideal-affine-groups-are-self-similar`
  imports Zaremsky, arXiv:2405.09722, Example 4.7 with Corollary 4.5. It is stated
  for a unital ring `R`, not necessarily commutative, with a regular `x` such that
  `R/Rx` is finite and `∩ R x^k = 0`. The tree is the coset tree of the `Rx^k`.
  Commutatively this forces Krull dimension ≤ 1, and in characteristic 0 it forces
  a number field (`affine-self-similar-coordinate-rings-are-one-dimensional`).
- **(E) Evaluation / parameter architecture.** This is how
  `positive-char-polynomial-affine-groups-are-self-similar` escapes the
  one-dimensional obstruction. Coordinates are evaluated at points of a complete
  DVR `O`; states apply ring endomorphisms `σ_α` that substitute coordinates, and
  one variable plays the uniformizer.

Both need a rooted, finitely branching tree.

## Approach 1: (P) over free algebras, free group algebras and Leavitt algebras

**Idea.** Take `R = F_p⟨x_1..x_r⟩`, `F_p[F_r]` or `L_K(1,n)`, with `x` a regular
element generating a finite-index principal left ideal. Then Zaremsky's Example
4.7 makes `R^n ⋊ E_n(R)` self-similar. Every group embeds in the units of its
group ring, and the diagonal commutator trick of
`boone-higman-via-projective-ring-host` puts perfect unit subgroups inside `E_n`.
So these hosts could reach non-linear inputs.

**Would prove.** New Boone–Higman inputs beyond linear groups, through non-PI
hosts.

**Kill test.** Does `R` have a proper principal left ideal of finite codimension?

**Result: killed.**
- *Free algebras and free group algebras of rank r ≥ 2.* By the Schreier–Lewin
  formula (Lewin, Trans. AMS 145 (1969) 455–465, as quoted in the search results
  below), a left ideal `J` of codimension `d` is free of rank `d(r−1)+1`. A
  principal `J = Rx` with `x` regular is free of rank 1, so `d(r−1) = 0` and
  hence `d = 0`. There is no proper principal left ideal of finite index.
- *Leavitt algebras `L = L_K(1,n)`, n ≥ 2.* Hand proof. `L ≅ L^n` as left
  modules, so every left module `V` satisfies `V ≅ Hom_L(L,V) ≅ Hom_L(L^n,V) = V^n`.
  A finite-dimensional `V` is therefore 0. So `L/Lx` finite forces `Lx = L`, and
  the tree is trivial. For finite `K`, finite index means finite dimension.

So these rings, the natural non-PI candidates, cannot use architecture (P) at all.

## Approach 2: the general (P) collapse question

**Idea.** Find any finitely generated non-PI ring with a regular `x` such that
`R/Rx` is finite and `∩ Rx^k = 0`, and run (P) over it.

**Would prove.** The only way (P) could reach inputs that aren't linear over
commutative rings.

**Kill test.** Is such an `R` forced to be PI? If so, prime quotients embed in
matrix algebras over fields and the hosts' matrix groups are linear. Checked
so far:
- *Layers.* Right multiplication by `x^k` is injective and maps `R` onto `Rx^k`,
  so it induces `R/Rx ≅ Rx^k/Rx^{k+1}`. Hence `dim_{F_p} R/Rx^k = k·dim R/Rx`
  grows linearly (hand proof, over `F_p`).
- *PI from growth.* Small–Stafford–Warfield (Math. Proc. Cambridge Philos. Soc.
  97 (1985) 407–414; statement read from the search results below): affine
  algebras over a field of Gelfand–Kirillov dimension 1 are PI.

**Gap.** GK dimension ≤ 1 would follow from `F_j ∩ Rx^{Cj} = 0`, where `F_j` is the
span of words of length ≤ j. That bound is not proved: cancellation in sums can
make short elements highly x-divisible. The characteristic-0 case (Z-algebras)
also needs its own argument.

**Result: unclear.** Precise question: *f.g. `F_p`-algebra (or ring), `x` regular,
`R/Rx` finite, `∩ Rx^k = 0` ⇒ `R` is PI?* A yes means architecture (P) gives no
Boone–Higman inputs beyond matrix groups over commutative rings.

## Approach 3: (E) over noncommutative rings

**Idea.** Copy the parameter trick. Let `R` be noncommutative, evaluate coordinates
at matrix points `a ∈ M_d(O)^k`, and use states `σ_α: x_i ↦ α_i + u·x_i`. This is
where the commutative technique escaped one-dimensionality.

**Would prove.** Self-similar non-PI hosts.

**Kill test.** What does faithfulness force?

**Result: killed (hand proof).**
- Finite branching fixes the matrix size `d` of the parameter points.
- If `r ∈ R` vanishes at every point, translation by `r` acts trivially. So a
  faithful action forces `R ↪ ∏_a M_d(O) = M_d(C)` with `C = ∏ O` commutative.
- By the Amitsur–Levitzki theorem (classical, not re-read here), `M_d(C)`
  satisfies the standard identity `s_{2d}`, so `R` is PI.
- `E_n(R) ≤ GL_{nd}(C)` is linear over a commutative ring.

For reduced `C` that lands in inputs main already covers, through the quasi-linear
and char-0 / char-p permutational Boone–Higman claims. A small residual stays
unclear: f.g. subgroups of `GL_N` over non-reduced commutative rings that don't
embed in matrices over finite products of fields.

## Approach 4: ceiling for the whole lens (constraint)

**Idea.** Every architecture above gives a faithful action on a locally finite
rooted tree. So the host group is residually finite, and so is every subgroup of it.

**Would prove.** Nothing new. It bounds the lens.

**Kill test.** Hand proof: the level-`j` quotient maps separate points. Zaremsky
Theorem 1.1 hosts are finitely presented self-similar groups on finite-alphabet
trees, so they are residually finite.

**Result: survives as a constraint.**
- Tree-based host techniques reach only residually finite inputs.
- Decidable inputs that aren't residually finite need a non-profinite
  architecture.
- The lens's natural target is `fp-residually-finite-boone-higman` (BBMZ Problem
  5.3(12)). By approaches 1–3, even that needs architectures that are neither (P)
  nor (E) over PI rings. The Kharlampovich–Myasnikov–Sapir complex residually
  finite groups are the test inputs; see that node.

## Approach 5: tree-shift architecture over free algebras (the surviving shape)

**Idea.** Let `O = F_p⟨⟨x_1..x_r⟩⟩ ≅ F_p^{X*}`, meaning configurations on the
free-monoid tree. Every `v ∈ O^n` decomposes uniquely as
`v = v_∅ + Σ_i a_i x_i`, with `v_∅ ∈ F_p^n` and `a_i ∈ O^n`. The free algebra
`R = F_p⟨X⟩` is closed under this right division: `b = b_0 + Σ d_i x_i`, with
`d_i ∈ R`.

For `(M,b) ∈ R^n ⋊ GL_n(R)` acting by `v ↦ Mv + b`:
- `Mv + b = s + Σ_i (M a_i + d_i) x_i`;
- `s ∈ F_p^n` and `d_i` are the right quotients of `M v_∅ + b`.

So the state along direction `i` at digit `v_∅` is `a ↦ M a + d_i`, which lies in
`R^n ⋊ GL_n(R)`. The action is faithful, left multiplication commutes with right
division, and the rank is unrestricted. This escapes both the Schreier–Lewin kill
and the PI kill, because nothing requires a principal ideal or a fixed matrix size.

**Would prove.** Boone–Higman for subgroups of `GL_n(F_p⟨X⟩)`, a residually finite
but non-PI class, *if* a Zaremsky-type theorem gave finitely presented simple
envelopes for this kind of self-similarity.

**Kill tests.**
- **(i) Is it Zaremsky's Definition 2.1?** No. Definition 2.1 is about a rooted
  regular tree with states at boundary words. Here the group acts on labelled
  configurations of the `r`-ary tree, and states are indexed by (digit,
  direction). A new envelope theorem is needed, likely twisted-Brin–Thompson-like
  over `X*` with linear local rules. Novelty unchecked.
- **(ii) Finite presentation of `E_n(F_p⟨X⟩)`.** Gersten, "K-theory of free rings",
  Comm. Algebra 1 (1974) (statement from search results below): `K_n(R⟨X⟩) = K_n(R)`
  for regular right Noetherian `R`, so `K_2(F_p⟨X⟩) = 0` stably. Not checked: the
  unstable Steinberg kernel for fixed `n`, finite presentation of `St_n`, and Cohn's
  GE property for free algebras.
- **(iii) Payoff.** Which non-linear f.g. residually finite groups embed in
  `GL_n(F_p⟨X⟩)`? Unknown. The free algebra is residually finite-dimensional, so
  the class stays residually finite.

**Result: unclear.** It is the one genuinely new shape. Missing theorem:
*finitely presented simple envelopes for groups acting affinely on tree-shift
configuration spaces with right-division states*, together with a payoff theorem
placing interesting residually finite inputs in `GL_n(F_p⟨X⟩)`.

## Summary

| # | Approach | Verdict |
|---|---|---|
| 1 | (P) over free / free group / Leavitt algebras | killed (Schreier–Lewin; no finite-dimensional modules) |
| 2 | (P) over any non-PI ring | unclear (does finite residue force PI, via GK dimension 1?) |
| 3 | (E) parameter trick, noncommutative | killed (Amitsur–Levitzki ⇒ PI ⇒ linear over commutative rings) |
| 4 | Tree hosts only reach residually finite inputs | constraint |
| 5 | Tree-shift self-similarity over `F_p⟨X⟩` | unclear (needs a new envelope theorem) |

The lens-level obstruction is the noncommutative analogue of
`affine-self-similar-coordinate-rings-are-one-dimensional`. Digit and parameter
self-similar affine hosts over noncommutative rings collapse to PI rings, hence
to groups linear over commutative rings, except through the tree-shift
architecture of approach 5.

## Sources used for kill tests

- Search results for the Schreier–Lewin formula, including
  https://arxiv.org/pdf/2601.00861 and
  https://www.researchgate.net/publication/305006476_Free_modules_over_free_algebras_and_free_group_algebras_The_Schreier_technique
- Small–Stafford–Warfield:
  https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/abs/affine-algebras-of-gelfandkirillov-dimension-one-are-pi/32FB64FD9C0C0E4BFD71DEEA581787DE
- Gersten, K-theory of free rings: https://www.tandfonline.com/doi/abs/10.1080/00927877408548608
- Repo nodes: `principal-ideal-affine-groups-are-self-similar`,
  `affine-self-similar-coordinate-rings-are-one-dimensional`,
  `positive-char-polynomial-affine-groups-are-self-similar`,
  `fixed-leavitt-hosts-cannot-be-universal-bh-containers`,
  `complexity-bounded-host-classes-are-not-universal`,
  `leavitt-tensor-elementary-host-criterion`, `fp-residually-finite-boone-higman`,
  `boone-higman-via-projective-ring-host`.

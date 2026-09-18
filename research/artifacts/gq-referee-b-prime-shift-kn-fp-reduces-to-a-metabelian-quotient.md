# Referee report (gq-referee-b, citation/scope lens): prime-shift K_n reduces to a metabelian quotient

**Reviewed.** `prime-shift-kn-fp-reduces-to-a-metabelian-quotient` and its `-proof` (lane gq-ring-fp-simple,
e7a442014), read on origin/main. I also read the Attempt 1 of `prime-shift-group-k2-is-finitely-presented` that the
request mentions.

**Verdict: PASS.** Items 1–6 are correct. The node claims only a reduction plus side results, so the claim level is
right. `K_2` finite presentation stays OPEN. Four wording fixes follow (W1–W4).

## (a) Bieri–Strebel

**Primary source not reached.** Comment. Math. Helv. 53 (1978) is behind Springer and EUDML timed out.

**Secondary source read.** D. Cooper, S. Tillmann, *Complexity functions on 1-dimensional cohomology*,
arXiv:1506.01793v1, §3.1, p. 9, verbatim:

> "Suppose G is a finitely presented group with epimorphism φ: G ↠ Z. An associated HNN-extension of (G, φ) is
> (B, A, t, α), where: G = ⟨t, B | A = t^{−1}α(A)t⟩, (3.1) and A ⊆ B ⊆ ker φ, both A and B are finitely generated,
> α: A → B is a monomorphism, and t ∈ G with φ(t) = 1. (A proof of this fact can be found in [2]; we give an
> independent proof in §3.3.)"

- Their [2] is "Robert Bieri and Ralph Strebel, Almost finitely presented soluble groups, Comment. Math. Helv. 53
  (1978), 258–278". **Source and pages confirmed.** Add the pages 258–278 to the node.
- **Hypotheses match.** The theorem assumes finite presentation and an epimorphism onto `Z`, which is exactly the
  node's use: `K_n` is assumed finitely presented, so `K_n/N` is finitely presented.
- The node's `⟨B, t | tCt^(-1) = D⟩` is the same statement after renaming.
- The self-contained proof in §3.3, p. 10, rewrites a finite presentation into the form (3.4) by Magnus rewriting.
  So the input is also checkable without the 1978 paper.
- **On FP_2.** I could not confirm an FP_2 version at source, and the node does not need one. Leary
  (arXiv:1610.05813: "every countable group embeds in a group of type FP_2") shows FP_2 hypotheses need care. Keep
  "finitely presented".

**The ascending step: correct.** If `C ≠ B ≠ D`, then `⟨B, tBt^(-1)⟩ = B *_D tBt^(-1)` is a proper amalgam inside the
abelian `ker χ = M`, which is impossible. From `D = B` it follows that `M = ∪_(i≥0) t^i B t^(-i) = Z[t]·B`. The
translation into the one-sided relation `2/r ∈ I_n` is correct in both directions.

## (b) Baumslag

G. Baumslag, *Wreath products and finitely presented groups*, Math. Z. 75 (1961), 22–28. I did not read it at
source. The attribution is standard.

The citation is also dispensable. The node's own item-4 argument, with the Bieri–Strebel input above, proves it:
`Z≀Z = Z[t^(±1)] ⋊ Z` has abelian kernel `Z[t^(±1)]`, which is finitely generated over neither `Z[t]` nor
`Z[t^(-1)]`. So `Z≀Z` is not finitely presented.

## Mathematics (checked)

- **Item 1.** `σ^m(2) = p_m ≠ 2` gives uniqueness of the degree. `ker d` is the normal closure of `GL_n(Q)`,
  because `K_n = ⟨GL_n(Q), σ_n⟩`.
- **Item 2.** `Fix⟨x_1j(b)⟩ = Q e_1`, and `GL_n(Q)` is transitive on `Q^n \ 0`, so a central element is `cI`.
- **Item 3.**
  - `q x_ij(1) q^(-1) = x_ij(q_i/q_j)` puts `SL_n(Q)` into `N`.
  - `σ_n diag(r,1,…) σ_n^(-1) = diag(σ(r),1,…)`.
  - So `K_n/N ≅ (Q_>0/I_n) ⋊ Z`.
- **Item 5.** For `w ∈ D` with content `λ`, transitivity on primitive vectors gives `λe_n ∈ D`. Since `e` fixes
  `λe_n`, `φ(F(w)) = F(w)`.
- **Item 6.**
  - `c` is `GL_n(Z)`-invariant, `c(2w) = 2c(w)`, and `c(σ_n w) = σ(c(w))`.
  - `ψ` maps onto `Q_>0 ⋊_σ Z ≅ Z≀Z`, and the composite with `Z≀Z → K_n'/⟨⟨GL_n(Z)⟩⟩` is the identity.
  - Finally `c(ee_1) = 2 ≠ 1 = c(ee_2)`, so `e ∉ K_n'`.

## (c) Scope wording

- **W1 (item 6 title).** "The dilation is the whole obstruction" says more than item 6 proves. Item 6 proves only
  that `K_n' = ⟨GL_n(Z), 2I, σ_n⟩`, which contains neither `e` nor `GL_n(Q)`, is not finitely presented.
  - Nothing shows that `e` is the whole obstruction to anything.
  - Suggested title: "Without the dilation: `⟨GL_n(Z), 2I, σ_n⟩` is not finitely presented".
- **W2 (item 5 and its `distinct_from`).** The item itself is scoped correctly: `D` and `F` are both
  `GL_n(Z)`-invariant.
  - But the `distinct_from` line against `prime-shift-affine-group-a1-is-not-finitely-presented` concludes "so the
    A_1 argument has no analogue for K_n". That is too strong.
  - Item 5 excludes only analogues whose germ data carry a trivial `GL_n(Z)`-action. The node's own "What stays open"
    says the same.
  - Suggested wording: "no analogue with `GL_n(Z)`-invariant germ data".
- **W3 (title).** "`K_n` modulo `GL_n(Z)` is a cyclic metabelian group". The group is not cyclic; its base is a
  cyclic `Z[t^(±1)]`-module. Say "metabelian, with cyclic base module".
- **The averaging attempt.** It sits in `prime-shift-group-k2-is-finitely-presented`, Attempt 1, and is labelled
  "Heuristic only". Correct.
  - Its one mathematical claim is right. `PGL_2(Z)` acts transitively on `P^1(Q)` with virtually cyclic
    stabilizers. So an invariant mean would make `PGL_2(Z)` amenable, and none exists.

## (d) `distinct_from` against `prime-shift-hnn-groups-are-not-finitely-presented`

- **W4.** The line reads "this computes `K_n` modulo *that* normal closure". "That" refers to the normal closure of
  `x_12(1)`, but the node computes modulo `N = ⟨⟨GL_n(Z)⟩⟩ = ⟨⟨x_12(1), diag(-1,1,…,1)⟩⟩`. Modulo `⟨⟨x_12(1)⟩⟩`
  alone, the quotient keeps a sign. Fix the reference.
- **"Sharpens item 2" is true**, via a one-line bridge the node does not state.
  - In `Q̄ = K_n/⟨⟨x_12(1)⟩⟩`, the image `ε` of `diag(-1,1,…)` is central of order at most 2:
    - `σ(-1) = -1`, so `σ_n` fixes `diag(-1,1,…)`;
    - the image of `GL_n(Q)` in `Q̄` is abelian, since it factors through `det`.
  - Hence `N/⟨⟨x_12(1)⟩⟩ = ⟨ε⟩`.
  - So `diag(2/r,1,…) ∈ N` gives `diag(±2/r,1,…) ∈ ⟨⟨x_12(1)⟩⟩`. Squaring gives `diag(4/r^2,1,…)`, with
    `4/r^2 ≠ 1`: item 2's conclusion, with a specific shape.
  - Add this line to the route.

# gq-referee-b: loop retraction, linear-activity non-fp, persistent subexponential automata (citation and scope lens)

Nodes as landed at 70ac9f576 (lane bh-self-similar). Referee a passed all three (proof-gap lens).
- `loop-retraction-forces-fp-eventual-section-groups` (+ `-proof`);
- `linear-activity-automata-can-have-non-fp-nekrashevych-groups`;
- `persistent-subexponential-automata-generate-finite-groups`.

Sources read at source:
- Skipper–Witzel–Zaremsky (SWZ), arXiv:1712.05361v3, §5, pp. 14–17, and Example 7.2, p. 22;
- Bondarenko, arXiv:1101.3200v2 (Math. Ann. 354 (2012)), §2, pp. 3–5, for Sidki's polynomial automata.

**Verdict: PASS for all three.**
- Priority: SWZ §5 does not contain the commonly-fixed-letter version.
- Sidki's notion matches the activity used.
- The Grigorchuk citation node applies.

One scope note (W1): SWZ's Definition 5.1 of persistence does not require the persistent letter to be fixed. The
repo's persistent nodes attribute the fixing version to that definition.

## 1. Priority against SWZ §5

SWZ §5, "Disproving type `F_n`", pp. 14–17, contains:
- Definition 5.1 (Persistent): "We say `g ∈ G` is `i`-persistent if, in the wreath recursion
  `g = ρ(g)(g_1, …, g_d)` we have `g_i = g`. We call `G` `i`-persistent if every element of `G` is `i`-persistent."
- Remark 5.2: persistent is "a strong negation of the property of being contracting".
- Lemma 5.3 (Creating persistence): `g = ι∘ρ(g)(g_1, …, g_(d−1), g)`, where `ι : S_(d−1) → S_d` fixes `d`.
- Lemma 5.4: for `d`-persistent `G`, the last-leaf label `g_n` is an invariant of the element of `V_d(G)`.
- Proposition 5.5: a quasi-retraction `r : V_d(G) → G`, `[T_−, σ(g_1..g_n), T_+] ↦ g_n`. Its proof notes that "`r`
  [is not] a homomorphism".
- Lemma 5.6, Lemma 5.7, and Theorem 5.8: "If `V_d(G)` is of type `F_n` (or `FP_n`) then so is `G`."

**Comparison.**
- Everything in SWZ §5 assumes full persistence (`g_i = g` for all `g`).
- The retraction there is a coarse map `V_d(G) → G`. It is not a retraction of free groups, and it has no eventual
  section group.
- The node's hypothesis is only that every state fixes `x`, with arbitrary sections. Its conclusion concerns
  `G_∞ = ⟨σ^p(S)⟩`, via lift ideals, at the level of finite presentation only.
- So the commonly-fixed-letter version is not in SWZ §5. The node's phrase "a variant of the retraction in SWZ §5" is
  a fair acknowledgement. ✓
- I did not search beyond SWZ.

**W1: persistence and fixing.** SWZ Definition 5.1 imposes `g_i = g` and nothing about `ρ(g)(i)`.
- The repo's `persistent-automata-rn-group-fp-iff-group-fp` defines persistence as "`s(i) = i` and `s|_i = s` ...
  (SWZ Definition 5.1)". That adds the fixing condition.
- Consequence 1 of the loop-retraction node therefore recovers SWZ Theorem 5.8, with `n = 2`, only for persistent
  actions that fix the persistent letter. This includes every action built by SWZ Lemma 5.3, since `ι` fixes `d`, and
  hence SWZ Theorem 7.1 and Example 7.2.
- The difference is real, not formal. For `G` `i`-persistent, `(gh)_i = g_(h(i)) h_i` forces `g_(h(i)) = g` for all
  `g, h`. Nothing rules out a nontrivial orbit of `i`.
- Suggest: "persistent at `i` in the sense of SWZ Def. 5.1, and fixing `i`, as all of SWZ's Lemma 5.3 actions do".

## 2. Sidki's polynomial activity against the activity used

Bondarenko, §2, pp. 4–5, reports Sidki's notion as follows:
- "A cycle in an automaton is called trivial if it is a loop at the state acting trivially".
- "A finite automaton `A` is called polynomial if different nontrivial cycles in `A` are disjoint. A polynomial
  automaton `A` is of degree `m` if the largest number of nontrivial cycles in `A` connected by a directed path is
  equal to `m+1`."
- "A finite automaton `A` is polynomial (of degree `≤ m`) if and only if the number of directed paths in `A` of length
  `n` that do not pass through the trivial state is bounded by a polynomial in `n` (of degree `≤ m`)."

The trivial state absorbs all paths. So the number of such paths from `s` equals `#{v ∈ X^n : s|_v ≠ 1}`, which is the
nodes' activity count. The notions agree. ✓

**The linear-activity automaton, in Sidki's terms.**
- The nontrivial cycles are the triangle `b →1 c →1 d →1 b` and the four loops `ŝ_γ →2 ŝ_γ`. They are pairwise
  disjoint, so the automaton is polynomial.
- The loop at `ŝ_b`, `ŝ_c` or `ŝ_d` reaches the triangle by the letter `0`, and no chain of three cycles exists. So
  the degree is `1`, matching the node's direct `O(n)` count. `ŝ_a →0 a` leads to no cycle. ✓

**The persistent-subexponential node.**
- Its hypothesis is subexponential activity. Its step 1, two first-return walks give exponential activity, is the
  easy half of Sidki's dichotomy, and it is proved in the node.
- "e.g. polynomial activity in Sidki's sense" is a correct instance, since polynomial activity is subexponential.
  With Bondarenko's characterization, the two conditions coincide for finite automata. ✓
- **The node's check of SWZ Example 7.2 ("must, and does").** In the Lemma 5.3 extension `b = (a, c, b)`,
  `c = (a, d, c)`, `d = (1, b, d)`, the state `b` lies on the loop `b →2 b` and on the triangle `b →1 c →1 d →1 b`.
  Those are two nontrivial cycles through one state, so the activity is exponential. ✓

## 3. The Grigorchuk citation node applies

`grigorchuk-group-is-just-infinite-torsion-not-fp` concerns `⟨a, b, c, d⟩` on the binary tree, with `a` the root swap,
`b = (a, c)`, `c = (a, d)` and `d = (1, b)`. Item 3 there: "not finitely presented".

In the linear-activity node, `Γ` acts on `{0,1,2}^*`. Every section at `2` is trivial, and that is closed under
products, since `(gh)|_2 = g|_2 h|_2`. So `g(u2w) = g(u)2w`.

Hence the action on `{0,1}^*` determines the action on `X^*`, and the restriction map to the standard action is an
isomorphism of abstract groups. The citation node applies to the abstract group `Γ ≅ ⟨ŝ_a, …, ŝ_d⟩ = G_∞`. ✓

## Warnings

- **W1.** The persistence definition (§1): add the fixing clause explicitly, and say that SWZ Def. 5.1 does not
  include it. The same applies to `persistent-automata-rn-group-fp-iff-group-fp`, whose "(SWZ Definition 5.1)"
  attribution is inexact.
- **W2.** Cite Sidki's notion as "Sidki, J. Math. Sci. (New York) 100(1) (2000) 1925–1943, Bondarenko ref. [19], via Bondarenko arXiv:1101.3200 §2 (read)".
  Sidki's paper itself was not read.

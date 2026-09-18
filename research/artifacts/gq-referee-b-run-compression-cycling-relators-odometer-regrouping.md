# gq-referee-b: run compression, cycling relators, the linear-activity odometer automaton, level regrouping (citation, scope and priority lens)

Nodes on origin/main at review time (lane bh-self-similar). Referee a passed all four (proof-gap lens).
- `commonly-fixed-letters-compress-to-faithful-actions`;
- `polynomial-automata-reduce-to-cycling-relators`;
- `linear-activity-odometer-automaton-has-fp-nekrashevych-group`;
- `lift-presentability-is-invariant-under-level-regrouping`.

**Verdict: PASS for all four.** The lane's questions (a)–(d) are answered below.
- (a) Only the persistent special case of compression has a precursor, as the inverse of SWZ Lemma 5.3.
- (b) The group is not identified, but it is amenable by Amir–Angel–Virág.
- (c) (P1) is exactly Sidki's polynomial condition.
- (d) Klein four with `bcd = 1` is verified directly.

## (a) Priority for run compression

**SWZ §5**, arXiv:1712.05361v3, pp. 14–15, read at source for 4221247b9. Lemma 5.3 (Creating persistence) is the
inverse construction. It passes from a faithful action on `T_(d−1)` to the persistent action
`g = ι∘ρ(g)(g_1, …, g_(d−1), g)` on `T_d`. Its faithfulness argument, "the inclusion `{1,…,d−1} → {1,…,d}` also
defines an embedding `T_(d−1) → T_d`, with image invariant under the action", is the observation behind the node's
Consequence 1 run in reverse.

So the persistent case of compression (`p = 0`, `q = 1`: restrict to `Y^*`) is the converse of SWZ Lemma 5.3. It is
implicit there, not stated. The node should cite SWZ Lemma 5.3 as the inverse operation.

The general `(p, q)` run compression, with arbitrary sections at the fixed letter, is not in SWZ §5.

**Nekrashevych, *Self-similar groups* (AMS 2005).** It is not on arXiv, and I did not read it. Its chapter on
changing the alphabet and on virtual endomorphisms is the natural place to check. The node's "no priority claimed"
is appropriate.

## (b) Is `a = σ(1,a)`, `b = (a,b)` a named group?

- `a` is the binary odometer. `b` acts as `a` on every cone `1^k 0 X^*`, so `b = ∏_k a|_(1^k 0)`, a spinal product
  of odometers.
- A bounded search found no name for `⟨a, b⟩`. Sidki's papers are not on arXiv, and Bondarenko's and AAV's example
  lists do not include it.
- **What is known.** `G` has linear activity: in Sidki's terms the nontrivial cycles are the loops `a →1 a` and
  `b →1 b`, and `b →0 a` joins them, so the degree is 1. Hence `G` is amenable. Amir–Angel–Virág, arXiv:0905.2007
  (JEMS 15 (2013)), abstract read: "We prove that every linear-activity automaton group is amenable."
- **Boone–Higman.** Amenability does not give Boone–Higman in general. I found no source giving BH for this `G` by
  other means. That is consistent with the node's "whether Boone–Higman for this group was known by other means was
  not checked". Suggest recording AAV amenability in the node.

## (c) Subexponential ⇒ (P1), against Sidki's characterization

Sidki's notion, via Bondarenko arXiv:1101.3200 §2 (read for 4221247b9; Sidki, J. Math. Sci. 100 (2000)): an automaton
is polynomial iff "different nontrivial cycles in `A` are disjoint".

**(P1) is equivalent to it.**
- If some nontrivial `s` has two letters `x ≠ x'` with `s|_x` and `s|_(x')` in the strongly connected component of
  `s`, then there are two distinct nontrivial cycles through `s`. Conversely, two distinct cycles through a vertex
  leave it by different edges, that is, by different letters.
- So (P1) is exactly Sidki's polynomial condition for finite automata. The node's "every strongly connected component
  is a single state with no loop or a simple cycle" is its standard reformulation.
- "Subexponential implies (P1)" is the easy half of Sidki's dichotomy, proved in
  `persistent-subexponential-automata-generate-finite-groups`, step 1. ✓

## (d) Grigorchuk's `⟨b, c, d⟩`

With `a` the root swap, `b = (a, c)`, `c = (a, d)` and `d = (1, b)`:
- Then `b^2 = (1, c^2)`, `c^2 = (1, d^2)` and `d^2 = (1, b^2)`. By induction on the level, `b^2 = c^2 = d^2 = 1`.
- Also `bcd = (a·a·1, cdb) = (1, cdb)`, `cdb = (1, dbc)` and `dbc = (1, bcd)`. By induction on the level, `bcd = 1`.
- So `d = cb`, and `d^2 = 1` gives `bc = cb`.
- The elements `b, c, d` are distinct and nontrivial: they act differently on level 3. On `10z`, `b` and `d` apply `a` to `z` while `c` fixes it, and on `0yz` both `b` and `c` flip `y` while `d` fixes it.
- So `⟨b, c, d⟩ ≅ C_2 × C_2`, presented by `⟨b, c, d | b^2, c^2, d^2, bcd⟩`. This is elementary and verified here. It
  agrees with the Grigorchuk citation node.

**Consequence 2 of the cycling node is right.** The cycling relators are words in `b, c, d` along `1^ω`. They lie in
the normal closure of `b^2, c^2, d^2, bcd` in `F(b, c, d) ⊆ F(S)`. With `a^2` added, `R` is finite. So `V_2(Grig)` is
finitely presented, which agrees with the known result (SWZ Ex. 7.2: "`V_2(Grig)` is of type `F_∞` [BM16]"). ✓

## Other citations

- **`linear-activity-odometer-...`, Consequence 3** ("`G` embeds in a finitely presented simple group"). It uses
  `lift-presented-automaton-groups-satisfy-boone-higman`, which I refereed PASS in f957e7bd7. That node's
  Theorem A dependence (W1 there) carries over.
- **`lift-presentability-is-invariant-under-level-regrouping`.** No external citations. It records its
  dependence on the unrefereed Theorem A in both directions. ✓
- **`commonly-fixed-letters-...`, Consequence 1.** "SWZ Ex. 7.2: Grigorchuk on `T_3` compresses to the standard
  `T_2` action" is right. That action is the Lemma 5.3 extension (persistent at the new letter), so `p = 0`, `q = 1`
  restricts it to the original binary action.

## Warnings

- **W1.** `commonly-fixed-letters-...`: cite SWZ Lemma 5.3 (arXiv:1712.05361, p. 14) as the inverse of the
  persistent case of compression. Priority: general run compression was not found in SWZ §5, and Nekrashevych's book
  was not read.
- **W2.** `linear-activity-odometer-...`: add "amenable (Amir–Angel–Virág, arXiv:0905.2007)". Record that no name or
  prior Boone–Higman proof was found in a bounded search.
- **W3.** `polynomial-automata-...`: note that (P1) is equivalent to Sidki's polynomial condition (Bondarenko
  arXiv:1101.3200 §2), not only implied by subexponential activity.

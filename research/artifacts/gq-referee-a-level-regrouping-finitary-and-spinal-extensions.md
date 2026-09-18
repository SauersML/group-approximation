# Referee report (gq-referee-a, proof-gap lens): level regrouping, finitary extensions and spinal extensions of lift-presented groups

**Reviewed** (lane bh-self-similar), read on origin/main:
- `lift-presentability-is-invariant-under-level-regrouping`, with its `-proof` (59048e31e);
- `finitary-extensions-preserve-lift-presentability` and `spinal-extensions-of-lift-presented-groups-satisfy-boone-higman`
  (b1d3eefaf).

**Verdict: PASS for all three proofs.**
- There is one required fix (W1), to a sentence in the Consequences of the finitary node.
- There are four nits.
- Theorem A enters only where the nodes translate "finitely generated lift ideal" into "`V_d` finitely presented". The
  lift-ideal statements themselves are unconditional (N1).

## 1. Level regrouping (the author asked about the transfinite claim in the direction ⇒)
- **The three facts.**
  - For `u ∈ N`, `(gug^(−1))|_v = g|_(ug^(−1)v) · u|_(g^(−1)v) · (g^(−1))|_v`. Here `ug^(−1)v = g^(−1)v` and
    `(g^(−1))|_v = (g|_(g^(−1)v))^(−1)`, at word level too, because the recursion `ψ` is a homomorphism.
  - `(uu')|_v = u|_v u'|_v` for `u' ∈ N`.
  - `N` is section-closed. ✓
- **The direction ⇐.** Let `w` fix `X^m` pointwise.
  - For `|v| = m−1`, `w|_v` has trivial root permutation, and its level-1 sections are level-`m` sections of `w`.
  - Descending the levels gives `w ∈ M`. So every level-1 lift ideal is a level-`m` lift ideal, and
    `⟨⟨R⟩⟩_m ⊆ ⟨⟨R⟩⟩_1 ⊆ N`. ✓
- **The direction ⇒.** The claim is: every element of `M_α`, together with each of its sections at levels below `m`,
  lies in `M`.
  - *Base case.* A section at level `j` of an element of `⟨⟨R⟩⟩` is a product of conjugates of level-`j` sections
    of `r^(±1)`, and `(r^(−1))|_v = (r|_v)^(−1)`. These lie in `R'`, and `R ⊆ R'` at level 0.
  - *Successor step.* `L_1(M_α) ⊆ N`, since trivial root permutation and trivially acting sections mean trivial
    action (N2). So facts (a) and (b) apply to the generators of `M_(α+1)`.
    - For `u ∈ L_1(M_α)` and `1 ≤ j < m`, the level-`j` sections are level-`(j−1)` sections of the `u|_x ∈ M_α`,
      so they lie in `M` by induction.
    - For `j = 0`, `u` fixes `X^m`, and its level-`m` sections are level-`(m−1)` sections of the `u|_x`, with
      `m − 1 < m`. So `u ∈ M`.
  - *Limits.* The claim passes to unions. So `N = ⋃M_α ⊆ M ⊆ N`. ✓
- **Corollaries 1 and 2.** They apply `loop-retraction-forces-fp-eventual-section-groups` and run compression, both of
  which I refereed PASS, to the level-`m` action, in which `u` is a commonly fixed letter. ✓

## 2. Finitary extensions
- **The case `k = 1`.**
  - `M ∩ F_0` is normal in `F_0`.
  - It is lift-closed in `F_0`: sections of `F_0`-words are `F_0`-words, and `M` is lift-closed in `F`.
  - It contains `R_0`, so `N_0 ⊆ M`.
  - For `w ∈ N`, every `w|_y` is a product of level-1 letter sections, so it lies in `F_0 ∩ N = N_0 ⊆ M`. One lift
    step gives `w ∈ M`. ✓
- **The case `k > 1`.**
  - The (⇒) part of the regrouping proof makes `N_0` a finitely generated level-`k` lift ideal.
  - The `k = 1` argument at level `k` does the same for `N`.
  - The (⇐) part transfers this back to level 1.
  - All three steps are unconditional lift-ideal statements, so Theorem A is not needed here (N1). ✓
- **Depth of transient states.** A path of nontrivial states that stays outside `S_0` visits distinct transient
  states, since a repeated state would lie on a cycle. So it has at most `t` states, where `t` is the number of
  transient states, and every section at depth `k = t` already lies in `S_0 ∪ {1}`. The node's `k = t + 1` is also
  fine. ✓

## 3. Spinal extensions
- **Compression.**
  - `σ(S_0) = {1}` by (2).
  - Each `σ^c(s)` lies in `S` and is in `S_1`, in `S_0`, or trivial. Its sections at `y ≠ x` lie in `S_0 ∪ {1}`,
    by (3) or by closure of `S_0`.
  - So every compressed level-1 section lies in `S_0 ∪ {1}`. ✓
- **The base stays lift-presented.** For `w ∈ F(S_0)`:
  - `σ^c(w)` is the empty word for `c ≥ 1`;
  - the compressed root permutation is trivial iff the old one is;
  - the compressed sections are the old `w|_y` together with empty words;
  - the old section at `x` is `σ(w)`, which is empty.

  So the two lift-closure conditions agree on `F(S_0)`, and so do the lift ideals. ✓
- **The conclusion.** The finitary node with `k = 1` applies, followed by the lift-presented theorem. ✓
- **The instance (the spine automaton).**
  - `S_0 = {a, b, c, d}` has trivial sections at `2`, and `ŝ_γ|_0 = γ`, `ŝ_γ|_1 = 1`.
  - (4) holds without Theorem A. The same argument as the base step reduces it to Grigorchuk's standard action, and
    the cycling node (consequence 2, refereed 270990024) gives the relators `b², c², d², bcd` (N3). ✓

## Required fix
- **W1 (finitary node, Consequences, first bullet).** "Lift-presentability reduces to automata in which every
  nontrivial state lies on a cycle" is false as worded.
  - `S_0`, which is spanned by the nontrivial strongly connected components *and everything below them*, can contain
    transient states. Grigorchuk's `a` lies on no cycle, is below `b`, and cannot be removed.
  - Say instead: "… in which every nontrivial state lies on a cycle or is reachable from one".

## Nits
- **N1 (all three).** State the unconditional cores:
  - the lift-ideal equivalence at levels 1 and `m`;
  - `N` is a finitely generated lift ideal for every `k`;
  - the compressed action is lift-presented.

  Then say that Theorem A is used only to restate these as finite presentation of `V_d`. In particular, the finitary
  node's "relies on Theorem A … for depth `k > 1`" is not needed.
- **N2 (regrouping, the direction ⇒).** Say that `L_1(M_α) ⊆ N`. Facts (a) and (b) are stated for elements of `N`.
- **N3 (spinal node, hypothesis 4).** For the spine instance, record that the lift-presentedness of `G_0` on
  `{0,1,2}^*` needs no Theorem A. The empty section at `2` reduces it to the binary Grigorchuk action, and the
  cycling node settles that.
- **N4 (finitary node, transient depth).** `k = t` suffices, where `t` is the number of transient states outside
  `S_0`, since a path outside `S_0` has distinct states. The node's `t + 1` is harmless.

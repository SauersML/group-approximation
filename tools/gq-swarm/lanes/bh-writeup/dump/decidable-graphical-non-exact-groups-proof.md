---
rg: 2
id: decidable-graphical-non-exact-groups-proof
kind: route
title: Build Osajda's labelled graph sequences by brute-force search, then run Dehn's algorithm on the finitely many components of girth below twice the word length
target: decidable-graphical-non-exact-groups-exist
requires: [haagerup-hosts-carry-no-weak-expander]
---

Sources, with labels read in the arXiv TeX sources on MSI:
- Osajda, arXiv:1406.5015 (`sclsiga200514.tex`): standing assumptions at the start of
  §`s:constr`, Theorem `l:c2LLL`, Remark `r:recurs`, Lemma `l:remb`, Theorem `t:mainex`,
  Corollary `c:Hilbert`, Lemmas `l:covpiece` and `l:plwg`, Theorem `t:main`.
- Gruber, *Groups with graphical C(6) and C(7) small cancellation presentations*,
  arXiv:1210.0178 (`2basics.tex`): Lemma `lem:graphical_basic`, Lemma
  `lem:graphical_simple`, and the observation after its Example `ex:cayley` that
  `C'(λ)` implies `Gr'(λ)`.
- Lyndon--Schupp, *Combinatorial Group Theory*, Ch. V, Greendlinger's lemma (Thm V.4.5)
  and Dehn's algorithm: textbook, not re-read.

**1. Recursive input graphs.**
- Osajda's standing assumptions: a sequence `(Θ_n)` of finite connected graphs of degree
  at most `D`, with girth `g_n → ∞`, `diam Θ_n ≤ A·g_n`, and
  `1 < ⌊λ g_n⌋ < ⌊λ g_(n+1)⌋`. Here `λ ≤ 1/24`.
- By Remark `r:recurs`, recursive sequences satisfying these exist, for example the
  expander Cayley graphs of `PGL_2(q)` of his §`s:discus`. These are `(p+1)`-regular with
  `p+1 ≥ 3`.
- The last assumption is reached by a computable subsequence, since girths of finite
  graphs are computable.

**2. Recursive labellings.** By Remark `r:recurs` (in the paper's text, not commented out):
- each stage `(Θ_1,l_1),…,(Θ_n,l_n)` of the construction of Theorem `l:c2LLL` extends to
  `(Θ_(n+1), l_(n+1))` by brute-force search, and likewise for `l'`;
- so for a recursive `Θ`, the product labelling `m` and the resulting graphical
  presentation are recursive.
The labelling is reduced, and Theorem `l:c2LLL` makes it `C'(λ)`: every piece `p → r_i`
has length `< λ·gi(r_i)`.

**3. Item 1.**
- Let `G_exp = <S | Θ>`, with an expanding recursive `Θ`.
- By Theorem `t:mainex` (which uses Lemma `l:remb`), each `Θ_n` embeds isometrically in
  the Cayley graph. By Corollary `c:Hilbert`, `G_exp` is not coarsely embeddable into
  Hilbert space. Property A implies coarse embeddability (Yu), so `G_exp` is not exact.
- An isometric embedding sends edges to edges and has fibres of size one. So it is a
  weakly embedded expander in the sense of `haagerup-hosts-carry-no-weak-expander`,
  which gives the no-Haagerup-host conclusion.

**4. Item 2.**
- Lemma `l:plwg` chooses iterated `Z/2`-homology covers `Θ̂_n → Θ_n` inductively, subject
  to Osajda's condition `(∗)`, and puts `Θ̃_n` = the `Z/2`-homology cover of `Θ̂_n`.
- `Z/2`-homology covers of finite graphs are computable finite graphs. Condition `(∗)` is
  a finite check, because the `Θ̃_j` with `j < n` are finite and `P(Θ̂_n) = P(Θ_n)`
  (Lemma `l:covpiece`). Osajda notes the choice is always possible.
- So a search over successive iterated covers terminates at each stage, and
  `(Θ̃, m̃)` is recursive.
- Theorem `t:main` then gives `G_PW = <S | Θ̃>` acting properly on a CAT(0) cube
  complex and without property A. The base `Θ` is `(p+1)`-regular with `p+1 ≥ 3`, as
  Willett's input requires there.

**5. Solvable word problem (both groups).** Let `Ψ = ⊔ Ψ_n` be either labelled sequence.
- **Pieces are small.** Every piece has length `< λ·gi(Ψ_n) ≤ λ|c|` for every simple
  cycle `c` of `Ψ_n` containing it. For `Θ̃` the pieces are essential pieces, counted
  modulo covering automorphisms, per Lemma `l:covpiece`. So `Ψ` is `Gr'(1/24)`-labelled.
  In particular it is `C(7)` in Gruber's graphical sense, since a simple cycle is not a
  union of fewer than 25 pieces.
- **Minimal diagrams.** By Gruber's Lemma `lem:graphical_simple`, if a word `w`
  represents 1 then it has a diagram `D` in which:
  - every face is labelled by a simple cycle of some `Ψ_n`;
  - every face is simply connected;
  - no interior edge originates from `Ψ`, so interior arcs are pieces, each shorter than
    `1/24` of the boundary of either adjacent face;
  - `D` is a `(3,7)`-diagram.
- **Greendlinger.** These are exactly the hypotheses under which the proof of
  Greendlinger's lemma (Lyndon--Schupp V.4.5) runs. So if `w` is cyclically reduced,
  nonempty and represents 1, some cyclic conjugate of `w` contains a subword `u` of the
  word `r` of a simple cycle `c` with `|u| > (1 − 3/24)|c| > |c|/2`.
- **Dehn's algorithm.** Such an `r` has `|r| < 2|u| ≤ 2|w|`, so it lies in a component
  with `gi(Ψ_n) ≤ |c| < 2|w|`. Girths are strictly increasing and computable, so these
  components are finitely many and computable from `|w|`. Each has finitely many simple
  cycles of length `< 2|w|`.
  - Replacing `u` by the complementary arc, of length `< |c|/2`, strictly shortens `w`
    and does not change its value.
  - Iterating with free and cyclic reduction therefore decides `w = 1`: `w = 1` iff the
    process reaches the empty word. (If it stops at a nonempty cyclically reduced word,
    the Greendlinger step shows that word is `≠ 1`.)

So both groups have solvable word problem. `∎`

**Scope.**
- Lyndon--Schupp V.4.5 is stated for classical `C'(1/6)` presentations. It is applied here
  to Gruber's graphical minimal diagrams, whose combinatorics (interior arcs are pieces
  shorter than `1/6` of each adjacent face) is all its proof uses. This transfer is the
  step a referee should check.
- No complexity bound is claimed. The brute-force labelling makes the algorithm very slow.

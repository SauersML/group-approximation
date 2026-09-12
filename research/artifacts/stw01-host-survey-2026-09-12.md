# STW Problem I: universal hosts, repo hosts, and the monotone-complete split (2026-09-12)

Lane `quasitrace`, second pass. The first pass is
`research/artifacts/stw01-awstar-normality-assessment-2026-09-12.md`.

## 0. Sources read (text extracted on MSI)

- Gow, *On the Quasitrace Problem and a Characterization of W*-algebras*,
  arXiv:2601.04431v2 (14 July 2026):
  - §1: Theorems A, B and C; Conjectures 1.1–1.4.
  - §4: Definition 4.8, Example 4.9, Corollary 4.10.
  - §6: Example 6.1, Proposition 6.2, Questions 6.3–6.5.
  - References [14] Christensen–Pedersen, [26] Hamana, [57] Wright.
- Arulseelan–Hanson, arXiv:2609.10218v1 (9 September 2026), pages 1–4.
- Willett, *Some notes on Property A*, arXiv:math/0612492v2:
  - Theorem 2.3.6 (extensions);
  - Theorem 2.3.11 (amalgamated free products);
  - the §2.3 list, including countable subgroups of `GL(n,F)` [GHW04];
  - Theorem 4.3.9 (property A iff `C*_r(G)` is exact).
- Predecessor artifact
  `research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md`,
  §§3, 4 and 8.

## 1. The universal host

Theorem 3.1 of the predecessor artifact proves that Problem I is equivalent to
linearity of bounded 2-quasitraces on `C*(F_2)`, and on `C*(Gamma)` for any
countable `Gamma` surjecting onto `F_2`. It was not a Cairn claim. It is now the
open claim `stw01-full-free-group-algebra-quasitraces-are-traces`, with the route
`stw01-problem-i-via-full-free-group-host` into the root, so the root's frontier
hole is decomposed.

The same argument gives two more universal forms.

- **Two positive contractions.** A non-trace quasitrace has a positive witness
  `a, b >= 0` with `sigma(a+b) != sigma(a)+sigma(b)`. This is predecessor
  Proposition 4.1: additivity on `A_+` is linearity. Scale `a, b` to contractions.
  Then `C*(1,a,b)` is a quotient of the unital full free product
  `C([0,1]) * C([0,1])`, the canonical generators lift `a` and `b` exactly, and
  the quasitrace pulls back.
- **RFD algebras.** Problem I trivially implies linearity for every unital RFD
  algebra. Conversely `C*(F_2)` is RFD (Choi 1980), so RFD linearity implies the
  universal test.

Consequence: a counterexample can always be taken RFD, and also, by
`stw01-traceless-separable-simple-reduction`, separable, simple, stably finite and
traceless. The two reductions produce different witnesses: restricting a
quasitrace to a subalgebra keeps it non-additive, but not simple or RFD.

## 2. Repo non-exact hosts

- **Kun–Thom nonsofic groups** (Theorem E pair `G`, wreath `W`, double `D`).
  - All have property A (Willett 2.3.6 and 2.3.11 with [GHW04]). So `C*_r` is
    exact, and Haagerup applies to every reduced algebra, subalgebra and quotient.
    Claim `stw01-kun-thom-reduced-group-algebras-are-qt-linear`.
  - Their full algebras are non-exact but have finite abelianization, so they are
    not universal tests.
- **Binary Leavitt unit group `L^x`.**
  - It is simple, so it has trivial abelianization and no free quotient.
  - Its exactness is not recorded in Cairn. If it is exact, `C*_r(L^x)` is
    excluded by Haagerup.
  - `C*(L^x)` is non-exact whenever `L^x` contains `F_2`.
  - No mechanism for a non-additive quasitrace on it is known.
- **Kazhdan full group C*-algebras** in general. Property (T) forces finite
  abelianization, so they are never universal tests via a free quotient. A
  counterexample there would still refute Problem I, but nothing in (T) produces
  or obstructs non-additivity: the Kazhdan projection only splits off the trivial
  character.
- **Non-MF constructions.** Non-MF-ness is an operator-norm embedding
  obstruction. Quasitrace linearity does not pass to subalgebras (the RFD envelope
  attempt), so neither MF nor non-MF status bears on linearity. No reduction is
  known in either direction.

## 3. The monotone-complete split of the crux

`stw01-quasitrace-crux-is-awstar-factor-w-star` records that Problem I is
equivalent to every type `II_1` AW*-factor having a large W*-corner. In a factor
every nonzero projection is faithful, and `M` is a corner of `M_n(pMp)` once
`tau(p) >= 1/n`. So "large W*-corner" can be read as "some nonzero W*-corner".

Gow §6 gives:
- a retract of the bidual is monotone complete (Proposition 6.2);
- a type `II_1` AW*-factor is W* iff it is a retract of its bidual (Corollary 4.10);
- Questions 6.3 and 6.4.

Only the type `II_1` factor case of Question 6.3 is needed, so Problem I is
equivalent to the conjunction of:
- `stw01-ii1-awstar-factors-are-monotone-complete` (Gow Question 6.4);
- `stw01-monotone-complete-ii1-awstar-factors-are-w-star` (no wild `II_1`
  factors).

The route is `stw01-problem-i-via-monotone-complete-ii1-factors`.

Where each half dies is recorded in the nodes. Both die at the same point: the
only canonical functional on a type `II_1` AW*-factor is its quasitrace, and every
attack needs its additivity. The type III wild constructions of Dyer, Takenouchi,
Hamana and Saitô–Wright rest on the absence of normal states, which cannot happen
in type `II_1`.

## 4. Status

Problem I stays OPEN. This pass adds:
- the universal-host decomposition of the root;
- the monotone-complete decomposition;
- exclusion of the repo's exact nonsofic hosts;
- recorded dead ends.

It contains no counterexample and no new positive case.

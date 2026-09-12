# Independent review: a surjunctive nonsofic group

Reviewer lane `review-surjunctive`, 2026-09-12. Adversarial review requested by
`gottschalk-positive` for the root `surjunctive-nonsofic-group-exists`.

## Verdict: PASS

The proofs hold as written. No gap, missing hypothesis or counterexample was
found. Two trust surfaces remain; they are listed under "Not verified" below.

## Scope reviewed

* `research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md` (Theorem 1,
  Corollary 2).
* `research/artifacts/finitary-split-extension-surjunctivity-2026-09-11.md`
  (Theorem 0, Lemma 5.1, Corollaries 6 and 7).
* `research/artifacts/surjunctivity-graph-folds-2026-09-11.md`, the peer node
  `graph-folds-over-surjunctive-groups-are-surjunctive`.
* The claim and route nodes wired into the root, and the literature inputs.

## 1. Theorem 1 (residually finite lamps over a surjunctive base)

Checked line by line.

* **Lemma 1.1 (transplant).** The identity `tau(pi^* y) = pi^*(tau_Omega y)`
  holds with the left-shift convention `tau(x)(l) = mu((x(l m))_m)`.
  Injectivity transfers because `pi` is onto.
* **Lemma 1.2 (density).** Pulled-back solutions agree with any target on a
  separated finite set; the image is closed by compactness.
* **Lemma 2.1 (separation).** `w' w^-1 = (n' n^-1, 1)` when the
  `G`-coordinates agree, and lies outside `N` otherwise. A finite-index
  normal `A_0` avoiding the finitely many nontrivial values exists because
  `A` is residually finite.
* **Coordinates and (2.1).** `H(n,g) = H(n',g')` iff `g = g'` and `n, n'`
  agree mod `A_0` on `S`; the right action multiplies fibre coordinates on
  the right by `A_0 n_1(g^-1 s)`.
* **Lemma 2.2.** `{g : g u = s} = G_s g_u`, so `Z_s` is a finite union of
  right `G_s`-cosets. For `k in G_U`, `(kg)^-1 s = g^-1 s` on `U`, so
  `tau_U` commutes with left `G_U`-translation.
* **Lemma 2.3 (slices).** When `nu_m(g)` is trivial on `U\V`, the product
  `a . nu_m(g)|_U` keeps the `U\V` coordinates fixed, and `tau_U` reads
  exactly as `tau_V` on the slice.
* **Lemma 3.1 (coset region).** `RP \ R` is a finite union of right
  `K`-cosets; the output at `k h_i` reads `y` at `k eta f` with `eta`
  independent of `k`. So `Psi` is a genuine automaton over `K`. Injectivity
  of `Psi` follows from injectivity of `rho` by a common extension off
  `R ⊔ E`; ontoness and the finite-memory form of `rho^-1` follow as stated.

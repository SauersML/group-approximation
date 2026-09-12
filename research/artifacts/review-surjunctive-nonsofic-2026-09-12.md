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

### Proposition 4.1 (peeling), the step most likely to break

* **(c).** Slicewise extensions of maps commuting with `G_(U')` commute with
  `G_U`, which is contained in `G_(U')`. So `rho_U` is an injective
  finite-memory map commuting with left `G_U`-translation.
* **(b), choice of `V`.** `g not in Q_U` gives some `s in U` with
  `g F_U` missing `Z_s`, so `V != U`.
* **(b) step 1.** For `U'` not inside `V`, a point `h in gP` in `Q_(U')`
  would give `h F_(U')` meeting `Z_s` for some `s in U'\V`, but
  `gP F_(U')` lies in `g F_U`. The inverse of a bijection that fixes a
  coordinate for every input also fixes it.
* **(b) steps 2-3.** Lemma 2.3 applies at every window point, because all
  windows lie inside `gP` (each `P_i` contains `1`). Nested slicing is
  associative.
* **(b), the induction on stages.** Since the order refines cardinality,
  every proper subset of `V` precedes `V` and no later subset lies in `V`.
  On the shrinking windows the partial composite equals the slicewise
  extension of the `V`-setting composite, which is `rho_V` at stage
  `j_V - 1`. Stage `j_V` returns `y`, and every later stage is the identity
  at `g`.
* **Bijectivity.** An intersection of right cosets of the `G_s`, `s in U`, is
  empty or a right coset of `G_U`, so `Q_U` is a finite union of right
  `G_U`-cosets. Commuting with `G_U` gives left-invariant rules. Lemma 3.1
  applies with `K = G_U` and the finite alphabet `B^(Abar^U)`.
* **Degenerate cases.** `Q_U = empty` gives `rho_U = id`; `G_U` of finite
  index is allowed; stabilizers may be infinite and the action need not be
  faithful or transitive. None of these affects the argument.

## 2. Theorem 0 and the doubles

* **Theorem 0.** The only points where the proof is not literally the
  wreath proof were checked:
  * `H_U = ker(q iota_(U,S) p_U)` gives `H_U\W ~= Q_U x G`, with (T) the
    correct transplant;
  * (A2) applied to the pair `(V, U)`, together with compatibility of the
    `iota`, gives `c^U_m(g) = c^V_m(g)` off the strata of `U\V`;
  * (A3) at `U` gives left `G_U`-equivariance;
  * slices over left cosets `c Q_V` do not depend on representatives,
    because every map in the induction commutes with left `Q_V`-translation.
* **Instance (I1).** (A1)-(A3) hold for `p_S` = restriction.
* **Lemma 5.1.** Checked:
  * `alpha` is an action;
  * `Phi` agrees on the two copies of `Gamma`;
  * `Psi` respects the conjugation relation;
  * `Psi Phi(ghat) = ghat` and `Phi Psi(e_(g x_0)) = e_(g x_0)`.

  Independently, the kernel of the fold map meets every vertex stabilizer
  trivially, so it acts freely on the Bass--Serre tree. The quotient graph
  has two vertices and `|G/Gamma|` edges, so the kernel is free of rank
  `|G/Gamma| - 1`, consistent with the basis `{e_x : x != x_0}`.
* **Instance (I2).** Letters of `alpha_g(w)` lie in `g(letters(w) ∪ {x_0})`,
  which gives (A2). A pointwise stabilizer of `S` preserves `X \ S`, which
  gives (A3).

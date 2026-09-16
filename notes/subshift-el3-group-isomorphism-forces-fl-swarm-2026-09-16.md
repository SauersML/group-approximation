# Attack on `subshift-el3-group-isomorphism-forces-flip-conjugacy` (swarm, 2026-09-16)

Agent: `swarm-subshift-el3-group-isomorphism`. Lock held on the target claim for this attack. Outcome: a reduction (the
group question is equivalent to a ring question, and Cartan uniqueness implies both without the recognition hypothesis),
a firewall against the `*`-automatic-diagonal mechanism over `F_2`, and a record of dead invariants. The target remains
OPEN.

## Setup

- `X, Y` infinite minimal subshifts, `R_X = LC(X,F_2) ⋊_T Z = ⊕_n D_X u^n`, `D_X = LC(X,F_2)`, `u f u^(−1) = f∘T^(−1)`.
- `G_X = EL_3(R_X)`.
- Established inputs used:
  - `subshift-el3-isomorphisms-are-standard-over-f2`: every isomorphism `G_X → G_Y` is `inn(k)∘M_3(φ)`, possibly after
    `γ_X`, with `φ: R_X → R_Y` a ring isomorphism;
  - `cantor-crossed-product-matrix-ring-iso-forces-soe`;
  - `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity` (items 1–5);
  - `corner-matrix-ring-isos-force-flip-conjugacy`;
  - `subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`.

## External gate (2026-09-16)

- WebSearch budget was exhausted, so the arXiv API (`export.arxiv.org/api/query`) was used.
- Queries covered ring isomorphisms of algebraic crossed products and Steinberg algebras, algebraic Cartan uniqueness,
  diagonal-preserving isomorphisms, and `ℓ^1` crossed products. Among them:
  - `"Steinberg algebra" AND isomorphism AND "orbit equivalence"`: 2 hits (1804.00396, 1706.00127), not relevant;
  - `"crossed product" AND "minimal subshift" AND ring`: 0 hits;
  - `"Cartan pair" AND uniqueness AND algebraic`: 5 hits, including 2505.24180 and 2411.15924.
- Abstracts read:
  - arXiv:2311.05694v2, B. Steinberg, *A note on projections in étale groupoid algebras and diagonal preserving
    homomorphisms*. The TeX source was read, including Theorem `t:main`.
  - arXiv:2303.10588v3, M. Amini, M. Moosazadeh, *Orbit equivalence of actions on Cartan pairs*.
  - arXiv:2505.00108v2, T. Roland, *On the involutive Banach algebra associated to topologically free dynamical systems*.
  - arXiv:2601.14907v1, K. Bardadyn, B. K. Kwaśniewski, *Banach algebra crossed products by inverse semigroup actions*.
  - arXiv:2607.06733v1, G. Boava, G. G. de Castro, D. Gonçalves, D. W. van Wyk, *Graded locally finite and just
    infinite Steinberg algebras*.
  - arXiv:2505.24180v1, L. O. Clark, L. D. Naingue, J. P. Vilela, *On graded quasi-Cartan pairs and twisted Steinberg
    algebras*.
  - arXiv:2411.15924v1, J. H. Brown, L. O. Clark, A. H. Fuller, *Intermediate subalgebras of Cartan embeddings in rings
    and C*-algebras*.
- Verdict: none of them treats ring isomorphisms of `LC(X,K) ⋊ Z` that do not preserve the diagonal. They cover:
  - `*`-isomorphisms over kind subrings of `C` (2311.05694);
  - diagonal-preserving or graded reconstruction (2505.24180, 2411.15924);
  - Banach `ℓ^1` algebras (2505.00108, 2601.14907);
  - graded structure (2607.06733);
  - Cartan-pair orbit equivalence (2303.10588).
  The question appears open. This is a bounded search, not a proof of novelty.
- Recalled from memory, NOT fetched, so treat as unverified:
  - Hadwin–Hoover, J. Funct. Anal. 77 (1988), semicrossed products;
  - Davidson–Katsoulis, J. reine angew. Math. 621 (2008);
  - de Jeu–Svensson–Tomiyama, J. Funct. Anal. (2012), `ℓ^1` crossed products;
  - Sugisaki (2003) on entropy within strong orbit equivalence classes;
  - the twisted Bass–Heller–Swan / Farrell–Hsiang sequence with vanishing twisted Nil terms for regular coherent rings;
  - Quillen's `K_*(F_q)`.
- The Boyle–Handelman (1994) quotation is the one already in `subshift-ring-isomorphism-preserves-soe-class-and-growth`.

## What was proved

### 1. Group rigidity is equivalent to ring rigidity

New open claim `subshift-crossed-product-rings-determine-flip-conjugacy`: does `R_X ≅ R_Y` force flip conjugacy?

- `subshift-el3-flip-rigidity-from-ring-rigidity` (target ⇐ ring claim + standardness). By standardness,
  `G_X ≅ G_Y` gives `R_X ≅ R_Y`; the ring claim then gives flip conjugacy.
- `subshift-ring-flip-rigidity-from-el3-flip-rigidity` (ring claim ⇐ target).
  - `M_3(φ)` sends `e_ij(r)` to `e_ij(φ(r))`, so it maps `EL_3(R_X)` onto `EL_3(R_Y)`.
- Formulation remarks, checked:
  - ring isomorphisms are `F_2`-linear;
  - `ι(Σ f_n u^n) = Σ u^(−n) f_n` is an involutive anti-automorphism, so anti-isomorphisms give isomorphisms. The
    computation is in the claim body.

### 2. Cartan uniqueness gives group rigidity with no recognition hypothesis

- `subshift-ring-flip-rigidity-from-cartan-uniqueness`: ring claim ⇐ `subshift-crossed-product-algebraic-cartans-are-conjugate`
  + item 4 of `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity`.
- With route 1 this gives the target from Cartan uniqueness alone.
- Item 5 of that node assumed "every group isomorphism carries `GL_3(D_X)` onto `GL_3(B)`". Standardness makes this
  unnecessary.
- The target's Attempts entry dies at Cartan uniqueness, with the proviso that `φ(D_X)` be an algebraic Cartan
  subalgebra. That proviso is automatic: the axioms of an algebraic Cartan pair are ring-theoretic, and ring isomorphisms are
  `F_2`-linear. The only genuinely open input is Cartan uniqueness, or more economically the ring claim.

### 3. Firewall: over `F_2` the kind-ring mechanism fails

- Steinberg, arXiv:2311.05694v2, Theorem `t:main`. For a subring `R ⊆ C` closed under conjugation, these are
  equivalent: (5) every `*`-isomorphism of Hausdorff ample groupoid algebras is diagonal preserving; (6) every unitary
  matrix in `GL_n(R)` is monomial. Such rings are "kind", a term from Carlsen, Adv. Math. 324 (2018), and the property
  is also in Johansen–Sørensen.
- `F_2` is not a subring of `C`, so the theorem does not apply. Its condition (6), for the trivial involution, fails.
  Exhaustive count, `experiments/subshift-el3-group-isomorphism-forces-fl-2026-09-16/f2_not_kind_firewall.py`:

  | n | symmetric idempotents | non-diagonal | orthogonal `A A^T = I` | non-monomial |
  |---|---|---|---|---|
  | 2 | 4 | 0 | 2 | 0 |
  | 3 | 10 | 2 | 6 | 0 |
  | 4 | 38 | 22 | 48 | 24 |

  `J_3` is a symmetric non-diagonal idempotent. `J_4 − I` is symmetric with `(J_4 − I)^2 = J_4^2 − 2J_4 + I = I` over
  `F_2`, and is not monomial.
- Inside `R_X`, with the involution `(f u^n)* = u^(−n) f`.
  - Choose a clopen `U` with `U, TU, T^2U, T^3U` pairwise disjoint. Such a `U` exists for every infinite minimal
    subshift: take a cylinder of a long word whose return times are all at least 4.
  - Put `e_ij = u^i 1_U u^(−j) = 1_(T^i U) u^(i−j)` for `0 ≤ i,j ≤ 3`.
  - `1_U u^m 1_U = 1_(U ∩ T^m U) u^m = 0` for `0 < |m| ≤ 3`, so `e_ij e_kl = δ_jk e_il`. Also `e_ij* = e_ji`.
  - Let `W = ⊔_i T^i U` and `w = Σ_{i≠j} e_ij + (1 − 1_W)`. Then `w* = w`, and `w^2 = Σ ((J_4 − I)^2)_ij e_ij + 1 − 1_W = 1`.
  - So `Ad(w)` is a `*`-automorphism of `R_X`. The element `w 1_U w = Σ_{i,k ∈ {1,2,3}} e_ik` has degree `−1`
    component `1_(TU) + 1_(T^2U) ≠ 0`, so it is not in `D_X`.
- The script checks `w^2 = 1` and the off-diagonal image on the orbit module of a Fibonacci Sturmian point, with
  `U = [101]` and return times 5..8. It prints OK. This is a sanity check; the proof is the algebra above.
- Consequence: an attack that tries (a) to arrange `φ` to be `*`-preserving and then (b) to invoke automatic diagonal
  preservation dies at (b) over `F_2`. It also dies at (a), since group and ring isomorphisms carry no involution data.
  This kills the approach only. It does not threaten Cartan uniqueness, because `Ad(w)(D_X)` is conjugate to `D_X`.

### 4. Dead invariants (computations recorded)

- **Hochschild homology.**
  - `HH_*(A ⋊ Z) = ⊕_n H_*(Z; HH_*(A, A u^n))` with `A = D_X`, which is a directed union of separable algebras `F_2^m`.
    The decomposition over the conjugacy classes of `Z` is the Feigin–Tsygan / Nistor crossed-product formula,
    recalled and not fetched.
  - For `n ≠ 0`, `HH_0(A, A u^n) = A / span{(a − α^n(a))x}` is the space of functions on `Fix(T^n) = ∅`, so it is 0;
    the higher groups vanish.
  - For `n = 0` this leaves `HH_0 = coinvariants = K^0(X,T) ⊗ F_2` and `HH_1 = invariants = F_2` (minimality), with
    `HH_(≥2) = 0`. So HH sees only `K^0 ⊗ F_2`.
- **Algebraic K-theory**, assuming vanishing twisted Nils (unverified, see above). `K_n(D_X) = C(X, K_n(F_2))`, and the
  sequence gives:
  - `K_0 = K^0`, `K_1 = Z`, `K_2 = 0`;
  - `K_(2i+1) = K^0/(2^(i+1) − 1)` for `i ≥ 1`;
  - `K_(2i) = Z/(2^i − 1)` for `i ≥ 1`.
  There are no extension problems, because one end is always 0. So the K-groups depend only on the group `K^0`.
- **Growth.** It sees the complexity class (`subshift-ring-isomorphism-preserves-soe-class-and-growth`), and nothing
  inside one strong orbit equivalence class of equal complexity. Sturmian and substitution candidates all have
  linear complexity.
- **Rank completion and rank functions.** They give the measure data of `K^0` only.

## Approaches tried and where each dies

1. **Orbit modules.**
   - `V_x = F_2^(Z)` with `f δ_n = f(T^n x) δ_n` and `u δ_n = δ_(n+1)` is simple with `End = F_2`.
   - A simple infinite-dimensional module has growth at least linear: `dim W^n v ≥ n + 1`. So "simple with linear
     growth" is a ring-invariant class of modules.
   - It also contains `R_X / R_X(u − 1) ≅ D_X`. That module is simple, since the invariant ideals of `LC(X,F_2)`
     correspond to invariant open sets. Its growth is `p_X(2n+1)`, linear for Sturmian `X`, and it has no joint
     `D_X`-eigenvector.
   - Where it dies: no ring-theoretic property found separates `D_X`-semisimple modules from the others. Even with
     recognition, one gets only a bijection of orbit sets, without topology.
2. **Semicrossed-product / `ℓ^1` rigidity.**
   - These recover `(X,T)` from the positive part `⊕_(n≥0) D_X u^n` (character space of a non-self-adjoint algebra)
     or from a norm.
   - Where it dies: `φ` need not respect the positive part. Recognising it inside `R_X` is at least as hard as the
     question.
3. **Corners, Morita equivalence, Kakutani moves.**
   - Spatial corner isomorphisms `e_U R_X e_U ≅ e_V R_Y e_V` plus a matching unit class give, by full-group
     equidecomposability of equal `K^0` classes, a diagonal-preserving isomorphism. See the tower argument in
     `corner-matrix-ring-isos-force-flip-conjugacy`.
   - Checked on towers over a common base with cohomologous roofs: this is the `cohomologous-roofs-give-conjugate-cantor-towers`
     mechanism.
   - Where it dies: nothing new appears. A counterexample must be non-spatial on every clopen corner.
4. **Counterexample via algebraic Elliott.**
   - Putnam's subalgebra has an algebraic analogue: `A_x = ∪` of the Kakutani–Rokhlin tower algebras (matrix units
     inside towers), an ultramatricial `F_2`-algebra with `K_0 = K^0(X,T)`.
   - For strongly orbit equivalent `X, Y`, algebraic Elliott gives `A_x ≅ A_y`.
   - Where it dies: extending that isomorphism to `u`. The C*-proof of `C(X)⋊Z ≅ C(Y)⋊Z` goes through A𝕋
     classification and perturbation. The algebraic analogue is blocked by the following lemma, proved here.
   - **Lemma (trivial centre of blocks containing `u`).** Let `X` be an infinite minimal subshift.
     - (i) The centraliser of `u` in `R_X` is `F_2[u, u^(−1)]`. If `r = Σ f_n u^n` commutes with `u`, then
       `u r u^(−1) = Σ (f_n∘T^(−1)) u^n = r`, so each `f_n` is `T`-invariant, hence constant by minimality.
     - (ii) Some letter `a` has `T^n[a] ≠ [a]` for all `n ≠ 0`. Otherwise every `[a]` is `T^(n_a)`-invariant. Put
       `N = lcm n_a`. Then `T^N` fixes every `T^j[a]`, so `x_(j+kN) = x_j` for every `x ∈ X` and all `j, k`, and `X`
       is finite.
     - (iii) `p(u) = Σ c_n u^n` commutes with `1_V` iff `T^n V = V` for all `n` with `c_n ≠ 0`, since
       `u^n 1_V = 1_(T^n V) u^n`. With `V = [a]` from (ii), `C_(R_X)(u, 1_[a]) = F_2`.
     - (iv) Hence every subalgebra `S ⊆ R_X` containing `u` and `1_[a]`, unital or not, has centre contained in
       `F_2`: a central element of `S` commutes with `u` and `1_[a]`. So `R_X` is not a directed union of subalgebras
       with infinite centre. In a directed union some member contains `u` and `1_[a]`, and so does every later member.
       In particular `R_X` is not a directed union of subalgebras `⊕ M_(n_i)(F_2[t, t^(−1)])` (finite sums). Those are
       the crossed products of the periodic models, and the natural algebraic analogue of the A𝕋 building blocks.
     - (v) The same holds for inductive limits with non-injective connecting maps. The image in `R_X` of a finite sum
       `⊕ M_(n_i)(F_2[t, t^(−1)])` is `⊕ M_(n_i)(F_2[t, t^(−1)]/I_i)`, because two-sided ideals of `M_n(A)` are `M_n(I)`.
       If the image contains `u`, it is infinite-dimensional, since `F_2[u] ⊆ R_X` is a polynomial ring (`R_X` is
       free over `D_X` on the `u^n`). So some `I_i = 0`, because `F_2[t, t^(−1)]/I` is finite-dimensional for `I ≠ 0`.
       Then the centre contains a copy of `F_2[t, t^(−1)]`, which contradicts (iv).
   - So no exact intertwining through circle-type blocks is available. A counterexample would need blocks with trivial
     centre, for example corners of other crossed products, and no such scheme is known.
5. **Candidate pairs.**
   - Sturmian: dead, since strong orbit equivalence among Sturmians is flip conjugacy.
   - Proper orderings on one stationary Bratteli diagram, i.e. substitutions with the same incidence matrix that are
     not flip conjugate: same `K^0`, linear complexity, and no separating invariant found. No non-spatial isomorphism
     is known either. This is the natural testbed for both directions.
6. **Unit normalisers.**
   - Over `F_2` the units normalising `D_X` should be exactly `[[T]]`. This is expected from the bisection support of
     normalisers in effective groupoid algebras, but it was not proved or checked here. `[[T]]` determines flip
     conjugacy.
   - `φ([[T_X]])` is an amenable subgroup of `R_Y^×` isomorphic to `[[T_X]]`. The group `R_Y^×` contains free subgroups
     (`SL_2(F_2[t])` in a corner), so amenability is a real restriction.
   - Where it dies: no ring-invariant characterisation of the full groups among amenable subgroups was found.

## Open sub-questions suggested

- Does one strong orbit equivalence class contain two minimal subshifts with inequivalent complexity growth? Positive
  versus zero entropy would do. If so, ring isomorphism is strictly finer than strong orbit equivalence among
  subshifts. `subshift-ring-isomorphism-preserves-soe-class-and-growth` explicitly does not claim this.
- Is `R_X` a directed union of subalgebras isomorphic to finite sums of `M_n(F_2[t, t^(−1)])`? No: see the lemma in
  approach 4. The remaining question is whether any building-block scheme with trivial-centre blocks gives
  non-spatial isomorphisms.
- Separate the rings of two non-flip-conjugate proper orderings on one stationary diagram by any ring invariant.

## Files

- `research/subshift-crossed-product-rings-determine-flip-conjugacy.md` (new open claim, with Attempts)
- `research/subshift-el3-flip-rigidity-from-ring-rigidity.md` (route)
- `research/subshift-ring-flip-rigidity-from-el3-flip-rigidity.md` (route)
- `research/subshift-ring-flip-rigidity-from-cartan-uniqueness.md` (route)
- `experiments/subshift-el3-group-isomorphism-forces-fl-2026-09-16/f2_not_kind_firewall.py` and `.out`

## Referee (2026-09-16)

What was checked.
- All four research nodes, this note, the script and its output were read in full, together with the imported nodes
  `subshift-el3-isomorphisms-are-standard-over-f2`, `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity`,
  `subshift-crossed-product-algebraic-cartans-are-conjugate` and `cartan-uniqueness-iff-orbit-cocycle-and-ring-rigidity`.
  All four are ESTABLISHED except the Cartan claim, which is OPEN. Every node id cited in the new files exists in HEAD.
  `git status` shows no unlisted solver files.
- Duplicates: `bin/cairn search --similar` and a grep over flip-conjugacy claims found no existing claim stating ring
  rigidity for every X. It is `(D2)` of `cartan-uniqueness-iff-orbit-cocycle-and-ring-rigidity`, quantified over all X.
  That node proves `(U) ⟺ (D1) ∧ (D2)` at one X and does not settle `(D2)`, so the new hole is honest.
- Route `subshift-el3-flip-rigidity-from-ring-rigidity`: correct. The standardness claim states `G_X ≅ G_Y ⟹ R_X ≅ R_Y`
  verbatim, including the graph-automorphism case.
- Route `subshift-ring-flip-rigidity-from-el3-flip-rigidity`: correct. `M_3(φ)(e_ij(r)) = e_ij(φ(r))` and `φ` is
  onto. The two routes form a deliberate equivalence cycle, which is permitted: the fixpoint is least, so the cycle
  does not self-justify.
- Route `subshift-ring-flip-rigidity-from-cartan-uniqueness`: condition (a) of item 3 is word for word the statement of
  `subshift-crossed-product-algebraic-cartans-are-conjugate` at X, and item 4 has exactly the hypothesis "(a) at X".
  The report's weakest-step worry is resolved. Removing the recognition hypothesis of item 5 through standardness is
  a genuine, if shallow, improvement: standardness landed 2026-09-14, after item 5 was written.
- Anti-automorphism `ι`: re-derived additivity, anti-multiplicativity and `ι² = id`.
- Firewall: re-derived `e_ij e_kl = δ_jk e_il`, `e_ij* = e_ji`, `w² = 1`, and that the degree −1 part of `w1_Uw` is
  `1_(TU) + 1_(T²U)`. Reran the script (single thread): identical output. Its counts are plausible by hand: the
  orthogonal matrices in `M_3(F_2)` are exactly the permutation matrices.
- Spot-checked arXiv:2311.05694v2 by fetching its TeX source. Theorem `t:main` concerns conjugation-closed subrings of
  C, with items (5) (`*`-isomorphisms diagonal preserving) and (6) (unitaries monomial). The name "kind" is taken from
  Carlsen, Adv. Math. 324 (2018) 326–335. Johansen–Sørensen call the same property "unique partition of the unit".
  The titles and authors of all seven listed arXiv ids match the arXiv API.
- Lemma in approach 4, re-derived: (i) invariant locally constant functions are constant; (ii) the lcm argument makes X
  periodic; (iii) compare coefficients of `u^n`; (iv) and (v) follow, using that ideals of a finite product of matrix
  rings are products of `M_n(I)` and that `F_2[t^{±1}]/I` is finite dimensional for `I ≠ 0`.
- K-theory arithmetic recomputed from the stated (unverified) twisted Bass–Heller–Swan sequence with Quillen's
  `K_*(F_2)`. It matches. HH arithmetic also matches, given the recalled crossed-product formula.

Changes made.
- Claim: the HH bullet in Attempts now says the crossed-product HH formula is recalled and unverified, as the K-theory
  bullet already did. The `distinct_from` entry for the Cartan claim now records the exact relation
  (Cartan uniqueness = this claim + (D1)).
- Route from Cartan uniqueness, and this note: rephrased the misreading of the target's Attempts. That entry dies at
  Cartan uniqueness being open, and only carries the Cartan-image proviso.

Verdict: sound. It is an honest reduction: the group question equals the ring question given established
standardness, and Cartan uniqueness implies both. The firewall and the dead-invariant record are correct at the
stated certificate boundaries. The target remains OPEN. Landed with small fixes.

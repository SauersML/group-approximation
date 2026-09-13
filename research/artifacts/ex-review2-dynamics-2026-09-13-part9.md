# EX review 2, dynamics: part 9. Wave-2 landings of ex2-ft-actor-models, ex2-bernoulli-exactification, ex2-rokhlin-liftable-positive, ex2-rokhlin-almost-cocycle, ex2-hecke-pair-positive

Lane `ex-verify2-dynamics`, wave 2. Statuses were recomputed at `4200f08d51`, and nodes were read at the landing
tips. Part 7 already passed `iid-density-iff-collapse-and-endomorphism-density`,
`bernoulli-isomorphism-from-approximate-right-inverses`, `bernoulli-maximizes-extension-class-norm` and
`gohla-thom-lattices-no-weakly-bernoulli-liftable-action`.

| node | lane | status | verdict |
|---|---|---|---|
| `hyperlinear-truncated-actor-covers-refute-vertex-rounding` (+ `-proof`) | ft-actor-models | established | PASS (conditional statement; nothing refuted) |
| `layered-weil-actor-models-non-roundable-and-normalizing` (+ `-proof`) | ft-actor-models | established | PASS in outline. Artifact §§4–5 read; the Kazhdan corner lemma and Lemma C come from the established `compressor-extension-makes-roundable-vertex-part-invariant`, not re-derived |
| `ornstein-weiss-map-has-no-approximate-right-inverses` (+ `-proof`) | bernoulli-exactification | established | PASS |
| `spectral-gap-refutes-exactification-on-nonamenable-groups` (+ `-proof`) | bernoulli-exactification | established | PASS at 66b3f0952f. The first landing (adb9f1fbdd) overclaimed the constant, and the lane corrected it itself |
| `bernoulli-shifts-are-von-neumann-day` (+ `-citation`) | bernoulli-exactification | established | PASS, verbatim (Bowen 1707.09573v4, `pdftotext` lines 99–100) |
| `nonamenable-bernoulli-automorphisms-never-dense` | bernoulli-exactification | OPEN | labelled correctly; model tests consistent |
| `treeable-free-actions-lift-across-finite-normal-extensions` (+ `-proof`) | rokhlin-liftable-positive | established | PASS |
| `amenable-free-actions-weakly-equivalent-to-bernoulli` (+ `-citation`) | rokhlin-liftable-positive | established | PASS, verbatim (Burton–Kechris 1611.07921, `bk1611.txt` lines 501–503) |
| `weakly-bernoulli-lift-iff-bernoulli-almost-lifts` (+ `-proof`) | rokhlin-liftable-positive | established | PASS |
| `weakly-bernoulli-lifts-over-amenable-free-product-bases` (+ `-proof`) | rokhlin-liftable-positive | established | PASS |
| `weakly-bernoulli-liftable-action-makes-extension-sofic` (+ `-proof`; artifact §8) | rokhlin-almost-cocycle | established | PASS |
| `bernoulli-expansion-iff-ultrapower-cocycle-superrigidity` (+ `-proof`) | rokhlin-almost-cocycle | established | PASS |
| `sofic-coset-actions-pass-to-marked-colimits` (+ `-proof`) | hecke-pair-positive | established | PASS (items 1–7) |
| `sl2-laurent-f2-degree-one-amalgam-is-virtually-coxeter` (+ `-proof`) | hecke-pair-positive | established | PASS |

**Firing.** Several of these lanes work next to famous targets: Pestov Q3.4 through the actor models, Seward's
positive-entropy question, and deciding soficity of the Hecke pairs. These all stay OPEN at `4200f08d51`:
- `hs-stable-vertex-rounding-for-every-model`, `kt-actor-model-with-totally-non-roundable-vertex`,
  `el-r-polynomial-vertex-not-flexibly-hs-stable`;
- `every-group-has-positive-rokhlin-entropy-action`, `zero-rokhlin-supremum-forces-bernoulli-collapse`,
  `iid-generators-dense-at-zero-rokhlin-supremum`, `zero-supremum-endomorphisms-have-approximate-right-inverses`;
- `weakly-bernoulli-liftable-actions-force-virtual-splitting`, `deligne-triple-cover-no-weakly-bernoulli-liftable-action`,
  `deligne-class-congruence-cosystole-bounded-below`;
- `function-field-rank-one-vertex-action-is-sofic`, `sl2-laurent-f2-amalgam-approximants-separate-the-vertex`.

The spectral-gap node states the three zero-supremum claims are *equivalent* to Seward's question. It does not refute
them, and it carries no `refuted_by`.

## 9.1 Actor models

**`hyperlinear-truncated-actor-covers-refute-vertex-rounding`.** The statement is an implication (under (H1), hyperlinear
truncations have finite vertex kernel) and is labelled so.
- *Step 1.* The truncated vertex groups converge to `Γ` in the space of marked groups: a vertex relation of length `ℓ`
  is a relator of `G` of length `<= L`. Shalom's openness gives a Kazhdan stage `L_0`, and later stages are quotients,
  so one Kazhdan pair serves all of them.
- *Step 2.* A failure of (FT)_δ gives counterexamples whose ultraproduct is a trace-preserving actor model. (H1) rounds
  it, with `x = P^*`, which is a contradiction.
- *Step 3.* Two words for one element of `G` differ by a relator of length `<= 2R`, and `w_gw_h` against `w_(gh)` by one of
  length `<= 3R <= L`. So the coordinates of `τ` are almost representations with near-regular trace.
- *Step 4.* `ρ(γ)y = τ(γ)yπ(q_Lγ)^*` is a unitary representation of `Γ^_L`, and `x` moves by `< κ_0||x||`, which
  gives an invariant vector.
- *Step 5.* Put `T = m^(−1)Σ τ(n_i)`. Then `τ(E) = τ(TE) <= ||T||_2τ(E)^(1/2)` and `||T||_2^2 = 1/m`, so `E = 0`.
- *Corollary.* Under (H1) and infinite vertex kernels, the `G_L` are finitely presented non-hyperlinear groups. Both
  inputs are open, and nothing fires.

**`layered-weil-actor-models-non-roundable-and-normalizing`.** At the affine symplectic ascending HNN pair (not the
Theorem E pair).
- *Vertex defects.* `c_j = p^(2j) <= ℓ^(1/2)`, since `p^(4L) <= ℓ`, so the scalar defects `e(c_jω/ℓ)` tend to 1.
- *HNN relation.* `φ~(v,0,A) = (pv,0,A) = s(φ(v,A))`. `S~_c∘φ~` has central character `e(p^2c/ℓ)`, so the intertwiner
  `U_(c_j)` exists by uniqueness of the Schrödinger representation and its Weil lift. The wrap-around layer costs
  `<= 2/√L`.
- *Trace.* `|tr S~_c(v,s,A)| <= ℓ^(−rank(A−1)/2)`, and the trace is 0 at `A = 1`, `v != 0`, which gives regular trace.
- *Total non-roundability.*
  - `σ(x_v)σ(x_w)σ(x_v)^*σ(x_w)^* = ρ(z)^(2ω(v,w))`, and `ρ(z)` is a continuous function of `ρ(z)^2` on the small arc.
    So projections of `R` commute with `ρ(Γ~)`.
  - The corner is pulled back from the Kazhdan cover with `Fix_z = 0`, so criterion (c) excludes rounding (part 1 §1.4).
- *Normalization.* The layers are irreducible with distinct central characters, so `R` is the layer algebra, and the
  shift permutes layers.
- *Scope.* The step "`P` is exactly representable" (the Kazhdan corner lemma) and `d(σ) >= κ` (Lemma C) are consumed
  from `compressor-extension-makes-roundable-vertex-part-invariant` and not re-derived here.

## 9.2 Bernoulli exactification

**`ornstein-weiss-map-has-no-approximate-right-inverses`: PASS.**
- *Law.* Linear forms in `δ(y)` are parity sums along a finite nonempty edge set of the coset forest, which has an
  odd-degree vertex. So `δ(y)` is i.i.d.
- *Almost invariance.* `(a^(−1)·z)_1 = z_a` and `f(Π(a^(−1)ω))_1 = f(Πω)_a`, so `||aΨ − Ψ||^2 = 4µ{f_1 + f_a != y_1}`.
- *Mean zero.* Flipping `z` on `F` fixes `Π` and negates `Ψ`, so `Ψ ∈ L^2_0`.
- *Spectral gap.* `L^2_0` of a Bernoulli shift is a sum of copies of `ℓ^2(F)`, because `F` is torsion-free and acts
  freely on finite nonempty supports. Kesten gives `4 − 2√3`.
- *Items 3–5.* Equal base entropy, invariance of ARI, the category isomorphism, then self-absorption
  `X_κ ≅ X_κ × X_(ρ_d)^n`.

**`spectral-gap-refutes-exactification-on-nonamenable-groups`: PASS at 66b3f0952f.**
- *Equivariance and forest.* `τ^(hu)_s(hg) = hτ^u_s(g)`. Sites correspond to points of the `F_2`-orbit, so the site
  graph is a union of Cayley trees for a.e. `u`, off the null `G`-saturation of non-free points. Distinct
  `(g, s)` give distinct edges.
- *Lift and almost invariance.* `Π(T~_sω) = c·Πω` by equivariance, and `(c·z)_1 = z_(τ_s1)`.
- *Odd sector.* `O(T_su) = c_s(u)·O(u)`. The set `P(u,S)` is constant along orbits, which gives a Borel fundamental
  domain, so the odd sector is `L^2(D) ⊗ ℓ^2(F_2)`. Kesten applies.
- *First landing.* adb9f1fbdd asserted `d(φ∘ζ, id) >= (2−√3)/4`. That is not justified: `φ∘ζ` reads the subrelation
  from the `u'`-coordinate of `ζ(x)`.
- *Corrected argument (66b3f0952f), checked.*
  - `µ{u'_1 != u_1} <= ε`, and `u'|W = u|W` off measure `|W|ε`, by invariance.
  - A cylinder approximation of `c_s` gives `µ{c_s(u') != c_s(u)} <= 2η + |W|ε`.
  - So the `τ^u`-defects of `f = y'` are `<= ε + η_s(ε)`, and `2ε + η_a(ε) + η_b(ε) >= 1 − √3/2` forces `ε >= c > 0`.
  - Items 3–7 use only a positive constant.
- *Item 7.* A group with supremum zero is not sofic, hence nonamenable. The three claims quantify over all finite bases,
  so each holds iff no group has supremum zero. With `generators-dense-iff-zero-rokhlin-entropy` item 2 (no
  infinite-entropy free actions at supremum 0), that is `every-group-has-positive-rokhlin-entropy-action`.

**`bernoulli-shifts-are-von-neumann-day`.**
- *Source.* `/scratch.global/sauer354/ex/ex-bernoulli-rokhlin-complete/1707.09573.txt`, lines 99–100: "Theorem 1.1. Let
  Γ be a countable non-amenable group and (K;κ) a nontrivial probability space. Then the Bernoulli shift Γ↷(K;κ)^Γ is
  von Neumann-Day." This matches the node.
- *Remarks.* The Lusin–Novikov remarks on measure preservation are correct.

## 9.3 Liftable actions

**`treeable-free-actions-lift-across-finite-normal-extensions`: PASS.**
- *Lemma 1 (2 ⇒ 1).* `w_1·(w_2·(y,n)) = (q_1q_2y, w_1w_2n(φ(q_1,q_2y)φ(q_2,y))^(−1))`.
- *Lemma 1 (1 ⇒ 2).* `φ'(w_1w_2,y) = φ'(w_1,q_2y)φ'(w_2,y)` and `φ'(n,y) = 1`.
- *Tree lifting.* Edge labels are antisymmetric, and path products are multiplicative because backtracks cancel.
  This is the classical cocycle-lifting on a treeing.

**`amenable-free-actions-weakly-equivalent-to-bernoulli`.** `bk1611.txt` line 501: "When the group Γ is amenable, there
is only one free weak equivalence class, i.e., all free actions are weakly equivalent to sΓ". This matches the node.

**`weakly-bernoulli-lift-iff-bernoulli-almost-lifts`: PASS.**
- *(i) ⇒ (ii).* The defect sets are unions of `A_t ∩ q_2^(−1)A_s` with `t_(q_1q_2) != s_(q_1)t_(q_2)`. Weak containment
  transfers `µ(q_2A_t ∩ A_s)` within `δ`, so the defect is `< k^2δ`.
- *(ii) ⇒ (i).*
  - The encoding `E_m` is equivariant.
  - The defect event is clopen, so `ν(D) = lim ν_m(D) = 0`, and `(q_2·x)(q_1)(1) = x(q_1)(q_2^(−1))`.
  - The limit is free, since it factors onto Bernoulli, and it is weakly contained in `B` through clopen partitions
    pulled back by `E_m`.

**`weakly-bernoulli-lifts-over-amenable-free-product-bases`: PASS.**
- *Amalgam.* `W ≅ W_1 *_N W_2`: `N` is normal in the amalgam with quotient `Q_1*Q_2`, and the map to `W` is injective
  on `N`.
- *Finite factors.* A transversal gives the exact lift `σ(q'q)σ(q)^(−1)`.
- *Gluing.* Reducing `q_1q_2` performs `k` cancellations and at most one merge. Each adjacent pair lies in `F_i` and
  fails on a translate of measure `< δ`, so the total is `< (k+1)δ <= ε`.
- *Instances.* The invisible central element dies in every finite quotient, so no virtual splitting exists.
  `Q_p*Z` contains `F_2` and maps onto `Z`, so it is nonamenable without (T).

## 9.4 Almost cocycles

**`weakly-bernoulli-liftable-action-makes-extension-sofic` (Theorem S): PASS.**
- *Presentation.* `Γ~ = <S ∪ A | A, [a,s], r = a_r>`: `A` injects, and `ker(G→Γ)` is its image.
- *Failure bound.* A relator's failure event is a union of atoms of the joined translates, so `<= |A|^(|S||F|)δ`.
- *Transfer.* At good vertices the block event has the Bernoulli law. Markov gives a labelling with
  `<= 3η|V||R| + o(|V|)` failing pairs.
- *Permutations.* `τ(s)` is a base permutation followed by a fibre translation.
- *Freeness.* It comes from the base where the image is nontrivial, and from van Kampen diagrams of `wa^(−1)` inside a
  fixed radius where it is trivial.

**`bernoulli-expansion-iff-ultrapower-cocycle-superrigidity`: PASS.**
- *(1) ⇒ (2).* Expansion gives exact `z_n`. Popa 0.1 (verbatim, part 3) gives `z_n = δf_n + χ_n`, and `Hom(Γ,A)` is
  finite, so `χ_n` is 𝒰-constant.
- *(2) ⇒ (1).* A sequence at distance `>= η` from `Z^1` gives an ultrapower cocycle, which (2) untwists, a contradiction.
  The rate is the supremum of distances at defect `<= ε`.

## 9.5 Hecke pairs, positive side

**`sofic-coset-actions-pass-to-marked-colimits`: PASS.**
- *Item 1.* `π_(kN)(x) = k^(−1)r_xHN` is well defined (`nHN = HN`) and injective by the choice of `N`, and (OA) is exact.
- *Item 3.* Finitely many kernel elements die at a stage, (LIFT) holds exactly, the chart map is injective via
  `p_n(H_n) <= H`, and stage covariance transports.
- *Item 5.* A section `s: G → G_(n_1)` exists because the finitely many relators die. `s(T) ⊆ H_(n_2)` after pushing,
  so `H = s^(−1)(H_(n_2))` is closed.
- *Items 6–7.* Only finitely many words are relevant. For `(N_k,M_k) → (N,M)` with `F/N_k` finite, finite presentation
  gives `N <= N_k` and `M <= M_k`.

**`sl2-laurent-f2-degree-one-amalgam-is-virtually-coxeter`: PASS.**
- *Reidemeister–Schreier.* `[a,x] = 1` indexes the conjugates by `g(3)`, and `(bcbf)^3` conjugated by `g` is
  `(c_(g(2))f_(g(3)))^3` over all ordered pairs `p != q`. So `W` is Coxeter with the stated `m`.
- *Tits representation.* It is integral (`2B ∈ {2, 0, −1, −2}`), and `φ_T` lies in the closed chamber. So
  `Stab(φ_T) = W_T` (Humphreys §5.13), and congruences mod `p` separate. Passing to `W ⋊ S_3` uses the
  `S_3`-invariant core.

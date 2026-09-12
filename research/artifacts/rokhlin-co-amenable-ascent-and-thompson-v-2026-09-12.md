# Rokhlin maximality ascends along co-amenable subgroups, and the Rokhlin entropy question for Thompson's V

Lane `rokhlin-entropy-v-l-times`, 2026-09-12. Handwritten proofs, no computation.

**Result.**
- **Theorem A:** maximal Rokhlin entropy of uniform Bernoulli shifts passes from an infinite co-amenable subgroup to the whole group. With the landed down-passing result, maximality is invariant along co-amenable inclusions.
- **Section 3:** wires the positive-entropy question for Thompson's V into Cairn.
- **Section 4:** audits which lower-bound mechanisms change when the Kazhdan host `U = L_(F_2)(1,2)^x` is replaced by V.

Nothing here proves positive Rokhlin entropy for any nonsofic group. `thompson-v-has-positive-rokhlin-entropy-action` stays open.

## 0. Imported statements

Section 5 quotes the sources.

- **(I1) Sub-additivity** (Seward, arXiv:1501.03367v4, Corollary 2.5). For an ergodic p.m.p. action on `Z`, an invariant sub-sigma-algebra `Σ` and the chain `F_1 = Σ`, `F_2 = B(Z)`, it gives `h^Rok(Z) <= h^Rok_(Z)(Σ) + h^Rok(Z | Σ)`.
  - The first term is the outer Rokhlin entropy of `Σ`. It is at most `H(α)` for every partition α with `Σ ⊆ σ-alg(α)`.
  - By definition, `h^Rok(Z | Σ) <= H(β | Σ)` for every countable partition β with `σ-alg(β) ∨ Σ = B(Z)`.
- **(I2) Weak containment** (Seward, arXiv:1602.06680v2, Theorem 1.2). Let `G ↷ (X, μ)` be free p.m.p., let `F` be a G-invariant sub-sigma-algebra, and let `G ↷ (Y, ν)` be weakly contained in all free p.m.p. actions of G. Then `h_G(X, μ | F) = h_G(X × Y, μ × ν | F ∨ B(Y))`.
- **(I3) Abért–Weiss** (arXiv:1103.1063v2, Theorem 1, quoted on main in `nontrivial-bernoulli-weak-equivalence-proof`). A free p.m.p. action of a countably infinite group weakly contains every Bernoulli action.

**Definitions.**
- **Relative Rokhlin entropy:** `h_G(X | F) = inf { H(α | F ∨ I_G) : σ-alg_G(α) ∨ F ∨ I_G = B(X) }`, where `I_G` is the invariant sigma-algebra. For ergodic actions `I_G` is trivial, and for trivial `F` this is `h^Rok_G(X)`.
- **Rokhlin-maximal at q:** `G` is Rokhlin-maximal at q when `h^Rok_G((A^k)^G, uniform) = k log q` for every `k >= 1`, where `|A| = q`. This is the definition of `bernoulli-rokhlin-maximality-passes-to-subgroups`.
- **Co-amenability (Følner form):** G acts on the right cosets `Ω = H\G` by `(Hg)s = Hgs`. For every finite `S ⊆ G` and `δ > 0` there is a finite nonempty `Ω' ⊆ Ω` with `|Ω's \ Ω'| <= δ|Ω'|` for all `s ∈ S`. Classically this is equivalent to a G-invariant mean on `G/H`; that equivalence is not used.

## 1. Theorem A

**Theorem A.** Let G be a countable group, let `H <= G` be an infinite subgroup that is co-amenable in the Følner sense, and let `q >= 2`. If H is Rokhlin-maximal at q, then so is G.

*Proof.* Replacing `A` by `A^k`, it suffices to show `h^Rok_G(A^G) >= log q`. The time-zero partition gives the reverse inequality.

Put `X = A^G` with uniform product measure and shift `(g.x)(h) = x(g^-1 h)`. Let `Q_g` be the partition of X according to `x(g)`, so `g.Q_1 = Q_g`. Let P be a countable partition with `H(P) < ∞` and `σ-alg_G(P) = B(X)`, and fix `ε > 0`.

**Step 1: a window.** As S runs through finite subsets of G, the sigma-algebras of `∨_(s ∈ S) sP` increase to `B(X)`. By martingale convergence there is a finite S with `H(Q_1 | ∨_(s ∈ S) sP) < ε`. By invariance,

    H(Q_g | ∨_(s ∈ S) gsP) < ε   for every g ∈ G.                          (1.1)

**Step 2: a Følner set of cosets.** Take a finite nonempty `Ω' ⊆ Ω` with `|Ω's \ Ω'| <= (ε/|S|)|Ω'|` for all `s ∈ S`. Put `Ω'' = {ω ∈ Ω' : ωs ∈ Ω' for all s ∈ S}`. Right multiplication by s is a bijection of Ω, so

    |Ω' \ Ω''| <= Σ_(s ∈ S) |Ω's \ Ω'| <= ε|Ω'|.                            (1.2)

Fix a representative `r(ω) ∈ G` with `ω = H r(ω)` for each `ω ∈ Ω`.

**Step 3: the H-system.** Restrict the action to H. For `Θ ⊆ Ω`, let `F_Θ` be the sigma-algebra of the coordinates in `∪_(ω ∈ Θ) ω ⊆ G`.
- The map `x -> (x(h r(ω)))_(h ∈ H, ω ∈ Θ)` identifies `(X, F_Θ)` with `(A^Θ)^H`.
- Since `(k.x)(h r(ω)) = x(k^-1 h r(ω))`, H acts on `F_Θ` as the uniform Bernoulli shift with base `A^Θ`.
- Coordinates on disjoint sets of cosets are independent, and the cosets partition G. So as H-systems `X = B × C`, with `B = F_(Ω'')` and `C = F_(Ω \ Ω'')`.

**Step 4: two partitions.**
- Put `P' = ∨_(ω ∈ Ω') r(ω)P`. Then `H(P') <= |Ω'| H(P)`. Let `Σ = σ-alg_H(P')`.
- Put `Q'' = ∨_(ω ∈ Ω'') Q_(r(ω))`. Since `k.Q_(r(ω)) = Q_(k r(ω))`, we have `σ-alg_H(Q'') = F_(Ω'')`.

Take `ω ∈ Ω''` and `s ∈ S`. Then `ωs ∈ Ω'`, and `r(ω)s` and `r(ωs)` lie in the same right coset, so `r(ω)s = k r(ωs)` for some `k ∈ H`. Hence `r(ω)sP = k.(r(ωs)P)`. The partition `r(ωs)P` is coarser than `P'`, so `r(ω)sP` is Σ-measurable. Conditioning on more lowers entropy, so (1.1) gives

    H(Q'' | Σ) <= Σ_(ω ∈ Ω'') H(Q_(r(ω)) | ∨_(s ∈ S) r(ω)sP) < |Ω''| ε.       (1.3)

**Step 5: an upper bound on a factor.** Let Z be the H-factor of X with sigma-algebra `F_(Ω'') ∨ Σ`. The restriction of a Bernoulli shift to the infinite subgroup H is mixing, so Z is ergodic.
- P' generates Σ under H, so the outer entropy of Σ is at most `H(P')`.
- Q'' is Z-measurable, and `σ-alg_H(Q'') ∨ Σ = B(Z)`.

So (I1) and (1.3) give

    h^Rok_H(Z) <= H(P') + H(Q'' | Σ) < |Ω'| H(P) + |Ω''| ε.                 (1.4)

**Step 6: a lower bound on the same factor.** Let β be a countable Z-measurable partition with `σ-alg_H(β) = B(Z)`. Then `σ-alg_H(β) ∨ C ⊇ F_(Ω'') ∨ F_(Ω \ Ω'') = B(X)`. The system X is ergodic, so `h_H(X | C) <= H(β | C) <= H(β)`. Taking the infimum over β,

    h_H(X | C) <= h^Rok_H(Z).                                                (1.5)

- **If `Ω'' = Ω`,** C is trivial and `h_H(X | C) = h^Rok_H(B)`.
- **Otherwise,** C is a Bernoulli action of H, so by (I3) it is weakly contained in every free p.m.p. action of H.
  - B is free: it is a nontrivial Bernoulli shift over an infinite group, and for `k ≠ 1` infinitely many disjoint coordinate pairs `{h, k^-1 h}` are independent.
  - (I2), with `X := B`, `F` trivial and `Y := C`, gives `h^Rok_H(B) = h_H(B | trivial) = h_H(B × C | C) = h_H(X | C)`.

H is Rokhlin-maximal at q, and `Ω''` is nonempty for `ε < 1`, so `h^Rok_H(B) = |Ω''| log q`.

**Step 7.** Combine (1.4), (1.5) and (1.2):

    |Ω''| log q < |Ω'| H(P) + |Ω''| ε,   so   H(P) > (1 - ε)(log q - ε).

As ε was arbitrary, `H(P) >= log q`. Partitions of infinite entropy do not affect the infimum, so `h^Rok_G(A^G) >= log q`. QED.

**Corollary B (invariance).** Let `H <= G` be infinite and co-amenable. Then H is Rokhlin-maximal at q if and only if G is. "Only if" is Theorem A. "If" is item 1 of `bernoulli-rokhlin-maximality-passes-to-subgroups`.

**Corollary C.** Suppose H is infinite, co-amenable in G, and Rokhlin-maximal at every `q >= 2`. Then G satisfies Gottschalk's surjunctivity conjecture and Kaplansky's direct finiteness conjecture.

*Proof.* Theorem A gives `h^Rok_G(k^G, u^G) = log k` for every k. Apply item 5 of `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`, which is Seward's Corollary 4.1. QED.

## 2. Remarks on Theorem A

1. **Finite index.** If `[G:H] < ∞`, take `Ω' = Ω`. Then `Ω'' = Ω` and C is trivial, so (I2) and (I3) are not needed. This recovers item 2 of `bernoulli-rokhlin-maximality-passes-to-subgroups` by a different argument.
2. **What each input pays for.**
   - Co-amenability pays for the windows. This is the ratio `|T'|/|T|` of Section 1.2 of `research/artifacts/rokhlin-lower-bounds-without-finite-models-2026-09-12.md`, now shown to be sufficient.
   - (I2) and (I3) remove the independent complement C. A generator of Z can use C only through relative entropy, and weak containment makes C invisible there.
3. **No new maximal group yet.** Every group currently known to be Rokhlin-maximal is sofic: every known lower bound runs through sofic entropy (Seward II, introduction, recorded on main). A co-amenable sofic subgroup already makes G sofic.
   - That is the theorem of Brude–Sasyk recorded in `research/artifacts/multi-mover-hnn-dossier-2026-08-15.md`, not re-read here. Remark 4 gives a direct proof.
   - So Theorem A yields a new maximal group only after some nonsofic group is proved maximal. It is a permanence statement for the maximal class that uses no finite models.
4. **Co-amenable induction of soficity.** Take a sofic approximation `σ_n : H -> Sym(d_n)` and Følner sets `Ω'` for a finite `W ⊆ G`.
   - **Construction.** Put `c(ω, g) = r(ω) g r(ωg)^-1 ∈ H`. Let `g` act on `Ω' × [d_n]` by `(ω, i) -> (ω g^-1, σ_n(c(ω g^-1, g)) i)` wherever `ω g^-1 ∈ Ω'`, and complete it to a bijection.
   - **Almost multiplicative.** By the cocycle identity `c(ω, gg') = c(ω, g) c(ωg, g')`, the defect is the boundary fraction plus the defects of `σ_n` on the finitely many values of c.
   - **Almost free.** For `g ≠ 1`, a fixed point needs `ωg = ω`, and then `c(ω, g) ≠ 1`.

   This is the standard argument; it is included only so that Remark 3 does not rest on an unread import.

## 3. Thompson's V: wiring

**V has the self-copy structure.** V acts on `C = {0,1}^N` by prefix replacement. For a word w, let `V_[w]` be the elements supported in the cylinder `[w]`. Conjugating by `x -> wx` identifies V with `V_[w]`. Hence:
- `V_[0]` and `V_[1]` commute and meet trivially, so `V × V <= V`;
- permuting the `2^n` cylinders of length n gives `Sym(2^n) <= V`.

The reviewed Remark 2.5 of `research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md` records the same.

**Consequences.**
- By Corollary A1 of `rokhlin-supremum-dichotomy-with-centralized-self-copies`, `h^Rok_sup(V)` is 0 or infinity.
- With `positive-rokhlin-entropy-action-gives-positive-supremum` and `infinite-rokhlin-supremum-forces-surjunctivity`, POS(V), INF(V) and RBS(V) are equivalent, and each makes V surjunctive and `K[V]` directly finite for every field K.
- That is the route `thompson-v-surjunctive-via-positive-rokhlin-entropy`.

**Descent from the Leavitt units.**
- POS(U) gives RBS(U) (`positive-rokhlin-entropy-makes-leavitt-units-surjunctive`), so U is Rokhlin-maximal at every q.
- `V <= U` by `leavitt-cylinder-swaps-generate-thompson-in-el`.
- Maximality passes to subgroups (`bernoulli-rokhlin-maximality-passes-to-subgroups`).
- So the Bernoulli 2-shift over V has Rokhlin entropy `log 2 > 0`. That is POS(V), and the route `thompson-v-positive-rokhlin-entropy-from-leavitt-units`.

**Counterexample direction.** A strict automaton over V makes V nonsurjunctive. Contrapositively, it forces `h^Rok_sup(V) = 0`. So `thompson-v-nonsurjunctive` refutes the positive-entropy claim for V.

## 4. Thompson's V: what changes relative to the Kazhdan host

This section is a mechanism analysis, not a theorem. The mechanism list is that of `research/artifacts/rokhlin-lower-bounds-without-finite-models-2026-09-12.md`, Section 4.

1. **Co-amenable induction.**
   - Over U, (T) and simplicity leave no proper co-amenable subgroup (`simple-kazhdan-groups-have-no-proper-co-amenable-subgroups`). V is a-T-menable, so that obstruction is absent, and Theorem A makes induction along co-amenable subgroups a genuine permanence theorem.
   - Two facts limit it for V. First, no point stabilizer of the Cantor action is co-amenable: `thompson-v-cantor-orbits-have-no-folner-sets` makes every orbital Schreier graph uniformly nonamenable. Second, a co-amenable subgroup of V known to be maximal would today be sofic and would make V sofic (Remark 3).
   - So along co-amenable subgroups, the V question reduces to `thompson-v-is-sofic`. Nothing Rokhlin-specific is gained until a nonsofic maximal group exists.
2. **Tree decompositions.** V acts properly on a CAT(0) cube complex (Farley; mentioned, not imported), so FW fails for V, unlike U. But the f-invariant needs the whole Cayley graph to be a tree. For groups with relations the Bethe functional is not an invariant (`window-entropy-deficits-are-not-isomorphism-invariant`).
3. **Treeings.** V contains `F_2 × F_2` (free subgroups of `V_[0]` and `V_[1]`), which is not treeable (Gaboriau, through `β_2^(2) = 1`; mentioned, not imported). So the Bernoulli orbit relation of V has no treeing either, for a different reason than over U.
4. **Koopman representation and weak containment.** These are blind in exactly the same way: the uniform Bernoulli shift over any countably infinite group has Koopman representation `λ^⊕N`, and all nontrivial Bernoulli shifts are weakly equivalent.
5. **Finitary witnesses.** V is simple. If V is not sofic, its sofic radical is V, and `sofic-radical-localizes-bernoulli-deficit-witnesses` gives no constraint, as over U.
6. **Groupoid counting.** The Cuntz groupoid underlying V has no Følner sequence (recorded under `thompson-v-is-sofic`, commit e03d940c3). So no groupoid-amenability count is available.

**Conclusion.** Every mechanism audited here either returns `thompson-v-is-sofic` or is blind to the base. The positive-entropy question for V is at least as hard as soficity of V along subgroup induction, and V lacks the (T) obstruction only for induction.

## 5. Sources, read 2026-09-12

The PDFs were extracted on MSI. `review-lit/entropy/1501.03367.txt` was already on MSI; arXiv:1602.06680v2 was fetched with curl and extracted with pdftotext. Spacing lost in extraction is restored.

**Seward, arXiv:1501.03367v4, Section 2.**
- "For a p.m.p. action G y (X,µ) and a G-invariant sub-σ-algebra F, we let I_G denote the σ-algebra of G-invariant sets and we define the relative Rokhlin entropy of G y (X,µ) relative to F, denoted h^Rok_G(X,µ|F), as inf{H(α|F∨I_G) : α is a countable Borel partition and σ-alg_G(α)∨F∨I_G = B(X)}."
- "For a p.m.p. ergodic action G y (X,µ), a collection C of Borel sets, and a G-invariant sub-σ-algebra F, we define the outer Rokhlin entropy as h^Rok_(G,µ)(C|F) = inf{H(α|F) : α is a countable Borel partition and C ⊆ σ-alg_G(α)∨F}."
- "Corollary 2.5. Let G y (X,µ) be a p.m.p. ergodic action, let C ⊆ B(X), let Σ be a G-invariant sub-σ-algebra, and let (F_n)_(n∈N) be an increasing sequence of G-invariant sub-σ-algebras with C ⊆ ∨_(n∈N) F_n ∨ Σ. Then (2.1) h^Rok_(G,µ)(C|Σ) ≤ h^Rok_(G,µ)(F_1|Σ) + Σ_(n≥2) h^Rok_(G,µ)(F_n|F_(n−1)∨Σ)."

(I1) is the case `C = B(Z)`, `Σ` trivial, `F_1 = Σ` (ours), `F_n = B(Z)` for `n >= 2`.

**Seward, arXiv:1602.06680v2, introduction.**
- "If F is a G-invariant sub-σ-algebra, then the Rokhlin entropy of G y (X,µ) relative to F, denoted h_G(X,µ|F), is inf{H(α|F∨I_G) : α countable partition and σ-alg_G(α)∨F∨I_G = B(X)}."
- "Theorem 1.2. Let G be a countably infinite group, let G y (X,µ) be a free p.m.p. action, and let F be a G-invariant sub-σ-algebra. If G y (Y,ν) is a p.m.p. action which is weakly contained in all free p.m.p. actions of G then h_G(X,µ|F) = h_G(X×Y,µ×ν|F∨B(Y))."

**Abért–Weiss, arXiv:1103.1063v2.** Re-read here from the PDF, fetched on MSI and extracted with ghostscript. It was earlier quoted from the HTML in `nontrivial-bernoulli-weak-equivalence-proof`.
- "Let κ be a probability space. The Bernoulli action κ^Γ is defined as the set of maps from Γ to κ, endowed with the product measure and the shift action by Γ."
- "Theorem 1 Let Γ be a countable infinite group and let f be a free p.m.p. action of Γ. Then f weakly contains every Bernoulli action of Γ. In particular, all free factors of i.i.d.-s of Γ are weakly equivalent."

Any probability space is allowed as base, so the infinite-product complement C of Step 6 is covered.

## 6. Cairn check

`cairn check --changed` on MSI, run on a `--shared` clone at tip be6bb740f with the 11 node files overlaid:
- **Exit code 4.** All five errors are in other lanes' files: `leavitt-ternary-frame-tree-uniformization-proof`, `locally-finite-hnn-regular-rank-model-proof`, `rgr-p-reduces-to-cyclic-twist-system`, `scalar-target-power-words-have-exact-roots` and `two-syllable-nonsingular-words-are-exactly-solvable`. No error or warning names a node of this lane.
- **`cairn why`.** The four new claims are ESTABLISHED through their routes. `thompson-v-has-positive-rokhlin-entropy-action`, `thompson-v-surjunctive`, `leavitt-unit-group-surjunctive`, `leavitt-unit-group-has-positive-rokhlin-entropy-action`, `every-group-has-positive-rokhlin-entropy-action`, `bernoulli-rokhlin-entropy-maximal-for-every-group` and `gottschalk-surjunctivity-conjecture` stay OPEN.

# EX review 2, dynamics: part 7. Tip recheck and the refill landings on these lanes' nodes

Lane `ex-verify2-dynamics`. Recheck tip `ee8d13842` (statuses), with nodes read at `01d580b3f`. The refill lanes are
ex2-sl3z-cocompact-weak-containment (69b86b04bf, a1cf1346e6), ex2-radu-superstrong-negative (4e2804d5e5, dc23e61b1d,
34b0ca8476), ex2-radu-chain-lamp-positive (018775687a), ex2-bernoulli-exactification (2cc01f001d, 0d15e308d3) and
ex2-rokhlin-almost-cocycle (f562ffc710). ex-verify-dynamics confirmed that it had covered none of items (1)–(5) of my
scope message.

## 7.1 Firing recheck at `ee8d13842`

**Method.** The same route fixpoint as the census. Graph-wide: 8,421 established, 1,558 open, 194 refuted.

**Still OPEN.**
- *Nonsofic actions:* `sl3z-on-cocompact-lattice-quotient-is-not-sofic`, `sl3z-admits-nonsofic-action`,
  `mixing-free-nonsofic-action-of-sofic-group`, `simple-group-lattice-admits-nonsofic-action`.
- *Radu's lattice:* `radu-bmw-lattice-sofic`, `radu-bmw-lattice-nonsofic`, `radu-nilpotent-by-arithmetic-quotients-are-sofic`,
  `radu-metabelian-quotient-is-sofic`, `radu-metabelian-quotient-is-not-sofic`, `radu-edge-coset-action-is-sofic`.
- *Bernoulli collapse:* `zero-rokhlin-supremum-forces-bernoulli-collapse`, `iid-generators-dense-at-zero-rokhlin-supremum`,
  `bernoulli-shifts-above-rokhlin-supremum-are-isomorphic`, `zero-supremum-bernoulli-automorphisms-dense-in-endomorphisms`,
  `zero-supremum-endomorphisms-have-approximate-right-inverses`.
- *Rokhlin entropy:* `every-group-has-positive-rokhlin-entropy-action`, `bernoulli-shift-entropy-classifies-for-every-group`,
  `rokhlin-maximality-ascends-finite-normal-extensions`, `rokhlin-maximality-ascends-amenable-normal-extensions`,
  `kun-thom-wreath-bernoulli-rokhlin-maximal`, `weakly-bernoulli-liftable-actions-force-virtual-splitting`.
- *HS stability:* `el-r-polynomial-vertex-not-flexibly-hs-stable`.

**New routes.** Two new routes lead into these targets, and both are unfired:
- `iid-density-from-collapse-and-endomorphism-density` needs `bernoulli-shifts-above-rokhlin-supremum-are-isomorphic`,
  which is open;
- `zero-supremum-collapse-via-approximate-right-inverses` needs `zero-supremum-endomorphisms-have-approximate-right-inverses`,
  which is open.

| new established claim | verdict |
|---|---|
| `sl3z-cocompact-not-factor-of-bernoulli-times-profinite` (+ `-proof`) | PASS. Credit note added (§7.2) |
| `popa-bernoulli-product-cocycles-come-from-cofactor` (+ `-citation`) | PASS, verbatim (math/0512646v8, p. 4, second sentence of Theorem 0.1) |
| `ioana-profinite-cocycle-superrigidity` (+ `-citation`) | PASS, verbatim (arXiv:0805.2998v1, `pdftotext` lines 57–63 for the Theorem A hypotheses, 111–115 for Theorem B) |
| `radu-delta-squared-orbit-is-signed-permutation-module` (+ `-proof`) | PASS |
| `radu-metabelian-quotient-embeds-in-edge-lamp-wreath` (+ `-proof`) | PASS |
| `radu-square-lamp-forces-reflections-in-finite-actions` (+ `-proof`) | PASS |
| `iid-density-iff-collapse-and-endomorphism-density` (+ `-proof`) | PASS |
| `bernoulli-isomorphism-from-approximate-right-inverses` (+ `-proof`) | PASS |
| `bernoulli-maximizes-extension-class-norm` (+ `-proof`) | PASS |
| `gohla-thom-lattices-no-weakly-bernoulli-liftable-action` (+ `-proof`) | PASS |
| `gohla-thom-class-norm-drops-under-weak-containment` (+ `-citation`) | PASS, verbatim (arXiv:2403.09582v2: Definition 2.2, Theorem 2.10, Lemma 2.13, Corollary 2.14, Lemma 2.15, Theorem 2.16, Theorem 3.4, Remark 3.14, Theorem 3.18) |

## 7.2 `sl3z-cocompact-not-factor-of-bernoulli-times-profinite`: PASS, with a credit note

**The proof, step by step.**
- *Coupling cocycle.* `c(γ, x) = g_(γx)^(−1)γg_x ∈ Λ`, and
  `c(γ_1γ_2, x) = g^(−1)_(γ_1γ_2x)γ_1g_(γ_2x)·g^(−1)_(γ_2x)γ_2g_x`.
- *Popa.* The second sentence of Theorem 0.1 untwists `w` onto `p`. `SL_3(Z)` has (T), and the diffuse Bernoulli
  action is s-malleable and mixing.
- *Ioana.* Theorem B gives `w''∘(id × r_n)`.
- *Holonomy.* At a point of `X_n`, `ρ(δ) = v''(δ, a)` is a homomorphism of `Γ_a`, by the cocycle identity at a fixed
  point.
- *Kill the holonomy.* Use BMS 16.2 (part 2, verbatim) together with almost-simplicity: `ker F` is `SL_3` or central,
  `e_12^N ∈ Γ'`, and `F(e_12^N)` would be a nontrivial unipotent element of `ι(Λ)`. This route avoids the `E_q` wording
  issue of Theorem E entirely.
- *Equivariant map into `G`.* On `Y_a`, `Ψ̃(δz) = g_(δΨ(z))c(δ,Ψ(z))φ(z) = δΨ̃(z)`.
- *Properness.* A `Γ_1`-invariant probability measure on `G` contradicts countable additivity over a Borel fundamental
  domain of the infinite discrete `Γ_1`.

**Calibration correction (a1cf1346e6).** The correction that this exclusion also covers the Hecke action, and so
separates nothing, is correct in substance. The Hecke action is weakly contained in finite actions, and the sketch
through Margulis superrigidity and Borel density is labelled as a sketch.

**Credit note (added forward).** Ioana, arXiv:0805.2998v1, §3, Remark (2) (`pdftotext` lines 821–829), already records
the product form. It takes `Γ ↷ X` profinite as in Theorem A and `ρ` the Bernoulli shift `[0,1]^Γ`: "let w : Γ × (X × Y)
→ Λ be a cocycle for the diagonal product action α × ρ ... Then there exist n such that w is cohomologous to a cocycle
w′ ... of the form w′ = w′′∘(id × s_n)", with Popa's Theorem 5.2 as input.
- So steps 2–3 of the route are Ioana's remark.
- The lane's content is steps 4–8: holonomy killed under (R) by BMS and almost-simplicity, then properness.

The node now says so.

## 7.3 Radu refills: PASS

- **`radu-delta-squared-orbit-is-signed-permutation-module`.**
  - *Pushing through the relators.* `aδ^2a = xzxz·aa = δ^2` (using `ax = xa`, `az = zb`, `bx = xb`, `bz = za`), and
    likewise for `b`. `cδ^2c = zxzx = δ^(−2)` (using `cx = zc`, `cz = xc`).
  - *The sign.* `ψ'` is a homomorphism, since every slab relator has an even number of letters in `{c, x, z}`.
  - *Independence.* The 4-cycles of the `{x,z}`-subgraph are edge-disjoint, hence independent in `Z_1(Y)`.
  - *Parity lemma.* `ĥδ^2ĥ^(−1) = δ^(−2)` in `G_2`, and `λ ∈ M` commutes with `δ^2 ∈ M`.
- **`radu-metabelian-quotient-embeds-in-edge-lamp-wreath`.**
  - *Host.* `Z_1(T_v) = 0` gives the cocycle, and its kernel is the kernel of Hurewicz. `e ↦ e − ē` is equivariant.
  - *Mark.* `ε` on `D_4` matches orientations: `ε = +1` on `1, xc, xz, zc` (forward edges) and `−1` on `x, xzc, z, c`
    (reversed). For example `x·e_0 = (xo → o)`, and `c·e_0 = (o → zo)`, the reverse of the last edge of the 4-cycle.
    So the signed sum is the image of the loop.
  - *Soficity.* GKP Theorem 3.6 is established through `gkp-theorem-3-6-citation`.
- **`radu-square-lamp-forces-reflections-in-finite-actions`.**
  - *The target.* Pushing forward along `gC_χ ↦ gK` is equivariant, and `N ⊆ K` normal acts trivially, so the target is
    a finite group.
  - *The count.* If `ε|_H = 1`, the image of `(xz)^4` is `2|H|Σ_(gH) ε(g)[gK]`, with distinct basis cosets and coefficients
    `±2, ±4, ±8, ±16`, all nonzero mod 32.
  - *The contradiction.* `(xz)^4` lies in the finite residual of `Γ_R`.
  - *Items 2–3.* They follow as written.
- **Status correction at 34b0ca8476** on `radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups`, item 3.
  - It says general amenable-by-sofic permanence is refuted by the Kun–Thom wreath product, and that the finite-kernel
    case stays open.
  - This refines part 3 §3.1, which recalled that status without re-reading it. The claim still asserts only the forward
    implication.

## 7.4 Bernoulli refills: PASS

- **`iid-density-iff-collapse-and-endomorphism-density`.**
  - *Dictionary.* The name map is an isometric bijection `Ind_λ(X) → Fac_G(X, X_λ)`.
  - *Topology.* `d` induces the intrinsic topology, through `μ(φ_n^(−1)A Δ φ^(−1)A) <= |W|·d` on cylinders and density of
    cylinders.
  - *Orbits.* Orbit closures of an isometric action form a symmetric, transitive relation.
  - *Equivalence.* (a) ⇔ (d) goes through the isometry `φ ↦ φ∘θ`.
  - *Item 5.* It applies item 3 of `iid-generators-not-dense-at-positive-rokhlin-supremum` with a two-point base of
    entropy `a < s`.
- **`bernoulli-isomorphism-from-approximate-right-inverses`.**
  - *Item 2.* ARI of `X_κ` plus `Fac(X_κ, X_λ) != ∅` gives approximate right inverses in `Fac(X_κ, X_λ)`, via `ψ = π'∘ζ`.
    Then `law(ψ(k), k)` is within `|W|ε` of `graph(φ)`, since `ψ(k) ~ λ^G`.
  - *`A` and `B` are `G_δ`.* Window events are clopen, and the martingale criterion applies.
  - *Density in `Y`.* `A ⊆ cl(B)` and `B ⊆ cl(A)`, so both are dense in `Y = cl(A) ∩ cl(B)`.
  - *Baire.* `Y` is compact and metrizable, so `A ∩ B != ∅`, which gives an isomorphism.
  - *Item 5.* `ν_ξ ∈ B ∖ cl(A)`, from the positive-supremum obstruction, contradicts `B ⊆ cl(A)`.
  - *Item 6.* Supremum zero forces `G` nonsofic, hence nonamenable. Bowen's Corollary 1.3 then gives factors both ways.
  - *Consequence.* This is a real reduction. At zero supremum, collapse follows from ARI for two finite bases of different
    entropy, one shift at a time. The consuming route stays unfired, because `zero-supremum-endomorphisms-have-approximate-right-inverses`
    is open.
- **`bernoulli-maximizes-extension-class-norm` and `gohla-thom-lattices-no-weakly-bernoulli-liftable-action`.**
  - *Lemma L.* `T_(g,a)T_(h,b)(z,t) = (ghz, t + a + b + β_h(hz) + β_g(ghz))`, and
    `β_h(hz) + β_g(w) = α_0(g,h) + β_(gh)(w)` at `w = ghz`. So `T` is a free action of `Γ~` with quotient `Z`.
  - *Lemma M.* This is the contractive half of GT Corollary 2.14.
  - *Theorem N(a).* Abért–Weiss.
  - *Theorem N(b), (⇐).* The ultrapower cochain `ζ` generates, together with `M(Bern)`, a separable invariant subalgebra.
    Mackey realization gives a free liftable `Y ≺ Bern`.
  - *Theorem G.* It chains `Bern ≺ Γ^ ≺` finite actions, the uniform cosystolic bound (GT 2.10, 2.15, 2.16) and Lemma L.
  - *Credit.* It correctly credits GT Remark 3.14 for the single quotient `{0,1}^(Γ~)/A`.

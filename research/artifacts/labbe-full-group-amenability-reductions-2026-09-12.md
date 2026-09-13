# Amenability of `[[Omega_U]]`: orbital recurrence, the polygon-exchange model, and walls

Lane `labbe-full-group-amenability`, 2026-09-12. This artifact backs the Attempts
entries of `labbe-shift-derived-full-group-is-amenable`. It does **not** decide
amenability. It proves four statements and pins the remaining crux.

## 0. Sources and provenance

These are arXiv e-print TeX sources, fetched with `curl` on MSI and then `msi get`, and read locally.
1503.04977 and 1903.06137 were fetched on 2026-09-12 at 21:08 CDT into
`/scratch.global/sauer354/labbe-amen/`. 1201.0257, 1305.2637 and 1602.04255 came from
`/scratch.global/sauer354/fpsz2/src/`. Line numbers refer to those files.

- **JMMdlS**, arXiv:1503.04977, `extAmen2.tex`.
  - l.112: `I` is the category of finite sets with injections. A functor `F: I -> Amen` is extended to all sets by direct limits, so every element of `F(X)` comes from `F(A)` for some finite `A ⊆ X`.
  - Corollary `prop:functor:amenable:intro` (l.135–139): if `G ↷ X` is extensively amenable, then a subgroup `H ≤ F(X) ⋊ G` is amenable as soon as `H ∩ ({1} × G)` is.
  - Lemma `lemma=JSbis` (l.262), (ii)⇒(i): extensive amenability can be checked on f.g. subgroups and single orbits.
  - Theorem `T: recurrent` (l.539), which is JNS Theorem 1.2: recurrent actions are extensively amenable.
  - Theorem `T:rank2full` (l.572–574): `IET(Λ)` is amenable if `rk Λ ≤ 2`.
  - Question `Q: polynomial` (l.219–222).
  - The remark after `prop:cantor` (l.724–726) cites Elek–Monod.
- **JNS**, arXiv:1305.2637, `amenable.tex`: Theorem `th:amenhomeo1` (l.104–117), with the finite-exceptional-set clause (2).
- **Elek–Monod**, arXiv:1201.0257, `syn_6.tex`.
  - Theorem `main` (l.47): there is a free minimal Cantor `Z^2`-action whose topological full group contains a non-abelian free group.
  - Comment 3 (l.60): the example is a minimal subshift.
- **ChJN**, arXiv:1602.04255: the Penrose group `P` (l.90 ff., section at l.297). Its amenability is open, per the existing node text.
- **Labbé**, arXiv:1903.06137, `common-content.tex`.
  - l.523–527: `T = R^2/Z^2`, `R_U^n(x) = x + φ^{-2} n` with `φ = (1+√5)/2`.
  - Theorem `thm:OmegaU-partition` (l.539–559):
    - (i) `X_{P_U,R_U} = Ω_U`, which is minimal and aperiodic;
    - (iii) `(T, Z^2, R_U)` is the maximal equicontinuous factor;
    - (iv) the fibre cardinalities are `{1, 2, 8}`.
  - l.1215–1277 define `Δ_{P,R}`, the generic coding `SR`, the directional codings `SR^v` and the direction set `Θ^P`.
  - Lemma `lem:closure-of-tilings` (l.1286–1291): `closure SR(T \ Δ) = X_{P,R}`.
  - Proposition `prop:factor-map` (l.1427–1446): `f: X_{P,R} -> T` is a factor map, `f ∘ σ^k = R^k ∘ f`, and `f` is one-to-one on `f^{-1}(T \ Δ)`.
  - l.2552: `P_U` gives a symbolic representation.
  - l.2568–2580:
    - `Θ^{P_U} = R·{(1,0), (0,1), (1,-1), (1,-φ)}`;
    - fibres of size 8 occur exactly over the `R_U`-orbit of `0`;
    - every other point of `Δ` has a fibre of size 2.

## 1. Orbital recurrence is automatic, and not enough

**Proposition 1 (orbital recurrence).**
- **Setup.** Let `Z^2` act freely on a set `X`. Let `W` be the group of bijections `g` of `X` for which there is a finite `F_g ⊂ Z^2` with `g(x) ∈ F_g · x` for all `x`. For a Cantor system, `[[Z^2 ↷ X]] ≤ W`, because the continuous cocycle `n_g: X -> Z^2` has finite range.
- **Claim.** For every f.g. `G ≤ W`, every `x ∈ X` and every symmetric, finitely supported probability measure `μ` on `G`, the `μ`-random walk on `Gx` is recurrent.
- **Consequence.** `W ↷ X` and all its restrictions are extensively amenable.

*Proof.*
1. **Transport to `Z^2`.** Let `S = supp μ` and `C = max{‖n‖_∞ : n ∈ F_s, s ∈ S}`. Freeness gives an injection `ι: Gx -> Z^2` with `y = ι(y)·x`, and `‖ι(sy) - ι(y)‖_∞ ≤ C` for all `s ∈ S`.
2. **Network.** The `μ`-walk is the reversible chain with conductances `c(y,z) = Σ_{s ∈ S, sy = z} μ(s)`. These are symmetric because `μ` is symmetric (`sy = z` iff `s^{-1}z = y`), and each vertex has total conductance 1.
3. **Comparison.** Transported by `ι`, this network has conductance at most 1 on pairs at `ℓ^∞`-distance at most `C`, and 0 elsewhere. Loops do not affect recurrence. So it is obtained from the network `Z^2_C` (vertex set `Z^2`, conductance 1 between points at `ℓ^∞`-distance in `[1, C]`) by lowering conductances and deleting vertices. By Rayleigh monotonicity it suffices that `Z^2_C` is recurrent.
4. **Nash-Williams.** Let `Π_k` be the set of edges `{p,q}` with `‖p‖_∞ < kC ≤ ‖q‖_∞`.
   - Since `‖q‖_∞ - ‖p‖_∞ ≤ C`, no edge lies in two different `Π_k`.
   - Each `Π_k` separates `0` from infinity.
   - `|Π_k| ≤ #{p : (k-1)C ≤ ‖p‖_∞ < kC} · (2C+1)^2 ≤ 8kC^2 (2C+1)^2`.
   - Hence `Σ_k |Π_k|^{-1} = ∞`, and `Z^2_C` is recurrent.
5. **Conclusion.** Recurrent actions are extensively amenable (`T: recurrent`). `lemma=JSbis` (ii)⇒(i) passes from f.g. subgroups and single orbits to `W ↷ X`. ∎

**Corollary 2 (the reduction).**
- **Setup.** Let `G ≤ W` be as above, and let `F: I -> Amen` be a functor.
- **Claim.** Suppose some `c: G -> F(X)` satisfies `c_{gh} = c_g · (g · c_h)` and has amenable kernel `{g : c_g = 1}`. Then `G` is amenable.

*Proof.* The map `g ↦ (c_g, g)` is an injective homomorphism `G -> F(X) ⋊ G`, since `(c_g, g)(c_h, h) = (c_g · g·c_h, gh) = (c_{gh}, gh)`. Its image meets `{1} × G` in the image of `ker c`. Apply `prop:functor:amenable:intro` together with Proposition 1. ∎

**Remark 3 (orbital recurrence alone decides nothing).**
- Elek–Monod Theorem `main` gives a free minimal Cantor `Z^2`-subshift whose full group contains `F_2`.
- By Proposition 1, that full group acts extensively amenably on every orbit.
- So recurrence, even together with freeness, minimality and the subshift property, does not imply amenability of `[[X]]`.
- For `Ω_U` the entire difficulty is the cocycle of Corollary 2. Recurrence comes for free and carries no information about `Ω_U` specifically.

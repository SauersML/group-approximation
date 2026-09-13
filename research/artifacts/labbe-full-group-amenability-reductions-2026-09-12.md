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

## 2. The polygon-exchange model and its walls

**Notation.**
- `T`, `R = R_U`, `P = P_U = {P_a}` and `Δ = Δ_{P,R}` are as in Labbé. The atoms of a topological partition are disjoint open sets whose closures cover `T` (l.1037).
- For `w ∈ Ω_U`, `D_n(w) = ∩_{‖k‖ ≤ n} R^{-k}(P_{w_k})` (l.1060). `f(w)` is the unique point of `∩_n closure D_n(w)`. This is `prop:factor-map`, which applies by l.2552 and Theorem (i).
- For `g ∈ [[Ω_U]]` write `g(w) = σ^{n_g(w)} w` with `n_g: Ω_U -> Z^2` continuous. Aperiodicity makes `n_g` unique, and uniqueness gives `n_{gh}(w) = n_g(hw) + n_h(w)`.

**Proposition 4 (polygon-exchange model).** For `x ∈ T \ Δ` put `ĝ(x) = x + φ^{-2} n_g(f^{-1}(x))`.
- (a) `ĝ` is a bijection of `T \ Δ`, and `g ↦ ĝ` is an injective homomorphism `[[Ω_U]] -> Sym(T \ Δ)`.
- (b) There is a finite `B_g ⊂ Z^2` with the following properties.
  - For each `a ∈ A^{B_g}` the map `ĝ` translates `Q_a \ Δ` by a vector in `φ^{-2} Z^2`, where `Q_a = ∩_{m ∈ B_g} (P_{a_m} - φ^{-2} m)` is an open polygon.
  - The sets `Q_a \ Δ` partition `T \ Δ`.
  - All boundaries lie in the finite union of segments `∪_{m ∈ B_g} (∂P - φ^{-2} m)`, with directions in `Θ^{P_U}`.

*Proof.*
1. **Fibres and invariance.** `f` is onto and one-to-one on `f^{-1}(T \ Δ)`, so each `x ∈ T \ Δ` has exactly one preimage. `Δ` is `R`-invariant and `f(gw) = R^{n_g(w)} f(w)`. So `g` preserves `f^{-1}(T \ Δ)`, and there `ĝ = f ∘ g ∘ f^{-1}`. Hence `ĝ` is a bijection and `(gh)^ = ĝ ĥ`.
2. **Injectivity.**
   - If `ĝ = id`, then `φ^{-2} n_g(w) ∈ Z^2`, so `n_g(w) = 0` for all `w ∈ f^{-1}(T \ Δ)`.
   - That set is nonempty, since `T \ Δ` is dense (l.1228) and `f` is onto. It is also `σ`-invariant.
   - Its closure is therefore a nonempty closed invariant set, which is all of `Ω_U` by minimality.
   - By continuity `n_g ≡ 0`, so `g = id`.
3. **(b), the window.** `n_g` is continuous with values in `Z^2`, so by compactness it depends only on `w|B_g` for some finite `B_g`.
4. **(b), the coding.** Let `x = f(w) ∈ T \ Δ`. Then `R^k x ∈ closure P_{w_k}` for every `k`, and `R^k x ∉ ∂P`. So `R^k x ∈ P_{w_k}`, and `w_k` is the unique atom containing `R^k x`. Thus `w|B_g = a` iff `x ∈ Q_a`, and on `Q_a \ Δ` the map `ĝ` translates by `φ^{-2} n_g(a)`. ∎

So `[[Ω_U]]` is a group of polygon exchanges of `T`, defined on the invariant dense set `T \ Δ`. The translations lie in `φ^{-2} Z^2 mod Z^2`, which is free abelian of rank 2, and the cuts have four directions. `D([[Ω_U]])` is amenable iff this group is, because `[[Ω_U]]/D` is abelian.

**Proposition 5 (walls on orbits).**
- **Setup.** Fix `x ∈ T` and identify its orbit with `Z^2` via `n ↦ R^n x`. This is free because `φ^{-2} ∉ Q`. Let `L ⊂ T` be a segment with direction `d ∈ Θ^{P_U}`.
- **Claim.** `N(L) = {n : R^n x ∈ L}` is contained in:
  - a line `{n_2 = c}` if `d = (1,0)`;
  - a line `{n_1 = c}` if `d = (0,1)`;
  - a line `{n_1 + n_2 = c}` if `d = (1,-1)`;
  - a strip `{n : n_2 - φ^{-1} n_1 ∈ J}` if `d = (1,-φ)`, where `J` is a translate of the parameter interval of `L`.
- **Consequences.**
  - **Two lifts disagree only along walls.** Generic orbits carry no walls. On a singular orbit, `x ∈ Δ`, let `w ≠ w'` in `f^{-1}(x)`. Then `{n : n_g(σ^n w) ≠ n_g(σ^n w')}` is contained in `N(L)` for the finitely many segments `L` of `∪_{m ∈ B_g} (∂P - φ^{-2} m)`.
    - Reason: if `R^n x` avoids those segments, then `R^{n+m} x ∉ ∂P` for all `m ∈ B_g`. The argument of Proposition 4(b) then gives `(σ^n w)|B_g = (σ^n w')|B_g`.
  - This is the comparison `τ_g` of JMMdlS used between the two lifts. Its support is contained in finitely many lines and strips, not in a finite set.
  - The vertices of the polygons `Q_a` form a finite subset of `T`, so they meet each orbit in finitely many points.
  - By l.2568–2580, all 8-point fibres of `f` lie over the single orbit `R^{Z^2}(0)`.

*Proof.*
1. **`d = (1,0)`.** `R^n x ∈ L` forces `x_2 + φ^{-2} n_2 ≡ c (mod 1)` for the height `c` of `L`. Two values `n_2 ≠ n_2'` would give `φ^{-2}(n_2 - n_2') ∈ Z`, which is impossible.
2. **`d = (0,1)` and `d = (1,-1)`.** The same argument works, using the functionals `y_1` and `y_1 + y_2`.
3. **`d = (1,-φ)`, the equation.** Lift `L` to `{(a,b) + t(1,-φ) : t ∈ I}` and put `u = x - (a,b)`. Then `R^n x ∈ L` iff there are `m ∈ Z^2` and `t ∈ I` with `u_1 + φ^{-2} n_1 - m_1 = t` and `u_2 + φ^{-2} n_2 - m_2 = -φt`.
4. **Eliminating `t`.** This gives `φu_1 + u_2 + φ^{-1} n_1 + φ^{-2} n_2 = φ m_1 + m_2`. Since `φ^{-1} = φ - 1` and `φ^{-2} = 2 - φ`, we have `φ^{-1} n_1 + φ^{-2} n_2 = φ(n_1 - n_2) + (2n_2 - n_1) ∈ Z[φ]`.
5. **Solving for `m`.** A solution needs `φu_1 + u_2 = φa_0 + b_0 ∈ Z[φ]`. Then, as `1` and `φ` are independent over `Q`, `m_1 = a_0 + n_1 - n_2`.
6. **The strip.** So `t = (u_1 - a_0) + n_2 - φ^{-1} n_1`, using `φ^{-2} - 1 = -φ^{-1}`. The condition `t ∈ I` is the strip condition. ∎

**Lemma 6 (factor embedding).**
- **Setup.** Let `π: X -> Y` be a factor map of free Cantor `Z^2`-systems.
- **Claim.** `h ↦ h̃`, with `h̃(x) = n_h(πx) · x`, is an injective homomorphism `[[Y]] -> [[X]]`.

*Proof.*
1. `h̃` is continuous, and `π ∘ h̃ = h ∘ π`.
2. So `h̃ k̃ (x) = (n_h(k πx) + n_k(πx)) · x = n_{hk}(πx) · x`. With `k = h^{-1}` this shows that `h̃` is a homeomorphism.
3. If `h̃ = id`, freeness of `X` gives `n_h ∘ π = 0`. Since `π` is onto, `n_h = 0`. ∎

Consequently a non-abelian free subgroup of `[[Y]]`, for any free Cantor factor `Y` of `Ω_U`, would make `[[Ω_U]]` non-amenable. No such factor is known. Any factor of `Ω_U` has zero entropy and inherits a toral equicontinuous factor. The Elek–Monod system was not compared with it.

## 3. What stays open, and why the known proofs stop

- **JMMdlS `T:rank2full`.** For an IET, `τ_g = g̃ g^{-1}` is a finitely supported permutation, because discontinuities meet each orbit in finitely many points.
  - For `ĝ`, the analogue changes along the walls of Proposition 5, which are 1-dimensional on each orbit.
  - Every `F(X)` has finite supports (l.112), so the natural germ-difference cocycle is not a cocycle into any `F: I -> Amen`.
  - Corollary 2 needs a different cocycle, and none is known.
- **JNS `th:amenhomeo1`.** Clause (2) asks for an `H` with amenable `[[H]]` that agrees with each generator off finitely many points.
  - Relative to translations, the exceptional set is the wall set, which is infinite.
  - Taking `H = Z^2` makes clause (1) the question itself.
- **Free subgroups.** Not ruled out.
  - The Elek–Monod mechanism needs every reduced word to be realized as a self-avoiding path in a proper edge-colouring.
  - Whether patterns of `Ω_U` (polygonal cells of the `Q_a`) realize this was not analysed.
- **Nearest open analogues.**
  - The Penrose group (ChJN), whose amenability is open;
  - JMMdlS `Q: polynomial`, which is also open.

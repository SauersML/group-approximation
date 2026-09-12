# The Z^2 SFT case: minimal aperiodic Wang shifts escape every recorded obstruction

Lane `fp-simple-amenable-z2-sft`, 2026-09-12.
- **Root:** `fp-infinite-simple-amenable-group` (OPEN).
- **Predecessor:** `research/artifacts/fp-simple-amenable-full-groups-2026-09-12.md`, case (S1).
- **Nodes landed with this artifact:**
  - `sfts-without-finite-orbits-are-not-residually-finite-actions` (proved here);
  - `minimal-aperiodic-wang-shift-exists` (citation);
  - `minimal-z2-subshift-derived-full-groups-are-fg-simple` (citation);
  - `labbe-shift-derived-full-group-escapes-known-obstructions` (proved here);
  - `labbe-shift-derived-full-group-is-amenable` (OPEN);
  - `labbe-shift-derived-full-group-is-finitely-presented` (OPEN);
  - route `fp-simple-amenable-via-labbe-shift-full-group` into the root.

**Outcome.** Nothing settles the root.
- Minimal aperiodic `Z^2` SFTs exist (Labbé).
- The derived subgroups of their topological full groups are finitely generated infinite simple groups.
- All three obstructions recorded on main fail for them. That is proved below, not assumed.
- So the concrete candidate `D([[Omega_U]])` stays live, with amenability and finite presentation both open.
- The suggested mechanism ("finite presentation forces periodic points") cannot work as it stands. The mechanism reads only finite orbits of an SFT neighbourhood, and here the SFT neighbourhood can be the shift itself, which has none.

## 1. Sources read (arXiv TeX sources on MSI, `/scratch.global/sauer354/fpsz2/src/`)

- **Labbé, arXiv:1802.03265** (`article1.tex`), "A self-similar aperiodic set of 19 Wang tiles".
  - Definitions, lines 225–240: `Omega_T` is the set of valid Wang tilings `Z^2 -> T` (contiguous edges share colours). A nonempty Wang shift is *aperiodic* if none of its tilings has a nontrivial period.
  - Theorem 1 (line 296): "The Wang shift `Omega_U` is self-similar, aperiodic and minimal." The abstract says `Omega_U` is "a minimal subshift of `U^{Z^2}`".
  - A Wang shift is a nearest-neighbour SFT, so `Omega_U` is a minimal SFT on which `Z^2` acts freely.
- **Chornyi–Juschenko–Nekrashevych, arXiv:1602.04255** (`IET_copy.tex`).
  - Theorem `main` (lines 81–84): "Consider a minimal faithful action of `Z^d` on a Cantor set conjugate to the action on a closed `Z^d`-invariant subset of `A^{Z^d}` for some finite alphabet `A`. Then the commutator subgroup of the topological full group `[[Z^d]]` is finitely generated."
  - Line 207: "It is known, see [matui1], that the derived subgroup of `[[Z^d]]` is simple and is contained in every non-trivial normal subgroup of `[[Z^d]]`."
  - Line 209: the order-3 elements cycling three disjoint clopen sets generate `[[Z^d]]'`.
  - Line 88: the rank-2 IET groups shown amenable by Juschenko–Matte Bon–Monod–de la Salle "can be realized as topological full groups of minimal action of `Z^2`". So some minimal `Z^2` systems do have amenable full groups.
  - Line 95, for the Penrose tiling group `P`: "It is an open question to decide if the group `P` is amenable."
- **Nekrashevych, arXiv:1511.08241** (`fullgr.tex`).
  - Line 118: "Let `G` be a minimal groupoid of germs. Then `A(G)` is simple, and is contained in every non-trivial normal subgroup of the topological full group of `G`."
  - Line 124: "If `G` is expansive and has infinite orbits, then `A(G)` is finitely generated."
  - Line 113 cites ChJN. ChJN line 86 says `A(G)` and the derived subgroup coincide for actions of abelian groups.
- **Elek–Monod, arXiv:1201.0257** (`syn_6.tex`).
  - Theorem 1.1 (line 48): "There exists a free minimal Cantor `Z^2`-action whose topological full group contains a non-abelian free group."
  - The example (lines 66–97) is a minimal subsystem of proper edge-colourings by six letters. Its free product of three involutions (translate across the edge carrying the letter) acts faithfully.
  - Remark 1 (line 54) gives free minimal `Z^2`-actions with locally virtually abelian full groups (products of odometers).
- **Xin Ma, arXiv:2209.00580** (`main.tex`, read in `/scratch.global/sauer354/fpsa/src/`).
  - Definition `defn: residually finite action` (line 1191, after Kerr–Nowak): for every finite `F ⊆ G` and `epsilon > 0` there is a finite `E ⊆ X` with a `G`-action `beta` such that `E` is `epsilon`-dense and `d(alpha(s) z, beta(s) z) < epsilon` for all `z` in `E` and `s` in `F`.
  - Theorem C (line 405): minimal topologically free residually finite actions on the Cantor set have LEF full groups.
- **Juschenko–Nekrashevych–de la Salle, arXiv:1305.2637** (`amenable.tex`), Theorem `th:amenhomeo1` (lines 104–117). If `[[H]]` is amenable, every `g` in `G` coincides locally with `H` off a finite set, all orbital Schreier graphs of `G` are recurrent, and germ groups are amenable, then `[[G]]` is amenable.

## 2. Theorem A: SFTs without finite orbits carry no residually finite action

**Theorem A.**
- **Setting.** Let `Lambda` be a finitely generated group, `A` a finite alphabet, and `Y ⊆ A^Lambda` a subshift of finite type with no finite `Lambda`-orbit. Let `X ⊆ Y` be a nonempty closed invariant set.
- **Conclusion 1.** The action `Lambda ~ X` is not residually finite in the sense of Kerr–Nowak (Ma's Definition).
- **Conclusion 2.** `X` has no periodic approximations (PA) in the sense of `periodic-approximable-subshifts-host-no-fp-simple-group`.

*Proof.*
1. **Conventions.** `(lambda . x)(mu) = x(mu lambda)`. `Y` is cut out by allowed patterns on a finite shape `K` containing `e`.
   - Every compatible metric `d` has some `epsilon_0 > 0` such that `d(x, x') < epsilon_0` implies `x(e) = x'(e)`. Indeed, the sets `{x : x(e) = a}` form a finite clopen partition of a compact space, so they have a positive Lebesgue number.
2. **An exact finite model.** Suppose the action is residually finite. Take `F = K` and `epsilon = epsilon_0`. This gives a finite `E ⊆ X` with a genuine action `beta` of `Lambda` on `E` and `d(s . z, beta(s) z) < epsilon_0` for `z` in `E` and `s` in `K`. Fix `z_0` in `E`.
3. **The periodic configuration.** Define `y(lambda) = (beta(lambda) z_0)(e)`.
   - For `s` in `K`, apply step 2 to `z = beta(lambda) z_0`. This gives `y(s lambda) = (beta(s) beta(lambda) z_0)(e) = (s . beta(lambda) z_0)(e) = (beta(lambda) z_0)(s)`.
   - So the `K`-pattern of `y` at `lambda` equals the `K`-pattern at `e` of the point `beta(lambda) z_0` of `X ⊆ Y`. It is therefore allowed, and `y ∈ Y`.
4. **Finite orbit.** `L = Stab_beta(z_0)` has finite index, because `E` is finite.
   - For `l` in `L`: `y(lambda l) = (beta(lambda) beta(l) z_0)(e) = y(lambda)`.
   - Hence `y` is invariant under `L` acting through `x -> x(. l)`, and its `Lambda`-orbit is finite. This contradicts the hypothesis on `Y`.
5. **(PA).** (PA) asks, for `K` as above, for a finite-orbit `y` whose `K`-patterns all occur in `X`. Such a `y` lies in `Y`, which has no finite orbit. So (PA) fails. ∎

**Remarks.**
- Density of `E` was never used, so the conclusion is stronger than stated.
- For `Lambda = Z^2`, a nonempty SFT with no doubly periodic point has no nontrivial stabilizer at all. A singly periodic point makes the set of `v`-periodic points a nonempty SFT over `Z^2/<v>`. That set has a periodic point, giving a doubly periodic point.
- So for `Z^2`, "no finite orbit" is the same as the whole action being free.

**Corollary A.1.**
- For every nonempty closed invariant subset of an aperiodic `Z^2` SFT, the hypotheses of Ma's Theorem C fail.
- So do the hypotheses of `periodic-approximable-subshifts-host-no-fp-simple-group`, item 1.
- Neither result can decide full groups there.

## 3. Theorem B: `D([[Omega_U]])` escapes every recorded obstruction

Let `X = Omega_U` be Labbé's Wang shift and `Gamma = D([[Z^2 ~ X]])`.

**Theorem B.**
1. `Gamma` is finitely generated, infinite and simple.
2. `X` carries an invariant probability measure of full support. So no nonempty clopen set contains two disjoint clopen copies of itself through compact open bisections, and the compressibility obstruction (`amenable-full-group-forces-invariant-measure`, Corollary 1.2) does not apply.
3. The extension theorem `fp-subshift-full-group-subgroups-extend-to-sft` is satisfied with `Y = X`. Its finite-orbit clause is vacuous.
4. `X` fails (PA), and `Z^2 ~ X` is not residually finite, so neither `periodic-approximable-subshifts-host-no-fp-simple-group` nor Ma's Theorem C applies.

*Proof.*
1. **Item 1.** `X` is a minimal subshift with a free action. So the action is faithful, minimal and conjugate to a subshift.
   - ChJN Theorem `main` gives finite generation.
   - Simplicity follows from Matui as quoted by ChJN (line 207), and from Nekrashevych's Theorem (line 118) together with ChJN line 86.
   - `X` is an infinite Cantor set: aperiodic implies infinite, and minimal and infinite implies perfect. So there are infinitely many order-3 elements cycling disjoint clopen sets, and they lie in `Gamma` (ChJN line 209). Hence `Gamma` is infinite.
2. **Item 2.** `Z^2` is amenable, so there is an invariant Borel probability `mu`. Its support is closed, invariant and nonempty, so by minimality it is `X`. If a clopen `A` contained disjoint clopen `B` and `C` with bisections `A -> B` and `A -> C`, then `mu(A) >= 2 mu(A)`, so `mu(A) = 0`, which contradicts full support.
3. **Item 3.** `X` is an SFT containing `X`, invariant under `Gamma`, with no finite orbit.
4. **Item 4.** This is Theorem A with `Y = X`. ∎

**What this does not say.**
- It does not say `Gamma` is amenable, nor that it is finitely presented.
- It does not rule out `Gamma` being LEF by some other argument.
- No source read here addresses `Omega_U`'s full group.

## 4. The two open questions, and why the available tools stop

**(Q1) Amenability of `D([[Omega_U]])`.**
- **JNdlS/JMMdlS.** Theorem `th:amenhomeo1` needs every element to agree locally with an amenable `[[H]]` off a finite set. The rank-2 IET realizations of ChJN line 88 meet this, because discontinuities of an IET are finitely many points.
  - For `Omega_U` I found no candidate `H`. The natural sets where an element of `[[Omega_U]]` changes its translation vector are unions of cylinder boundaries, and on each orbit `Z^2` these look like 1-dimensional walls, not finite sets.
  - This is a heuristic reason the theorem does not apply. It is not a proof that `Gamma` is non-amenable.
- **Elek–Monod mechanism.** Their free product acts faithfully because a homogeneous minimal proper edge-colouring realizes every reduced word as a path.
  - Wang colourings are not proper, so the involutions are not defined as they stand.
  - Whether `[[Omega_U]]` contains a faithful `Z/2 * Z/2 * Z/2`, or any `F_2`, was not checked.
- **Analogue.** The Penrose tiling group has the same profile: aperiodic, of finite type through matching rules, and minimal. Its amenability is recorded as open by ChJN (line 95).

**(Q2) Finite presentation of `D([[Omega_U]])`.**
- **Extension theorem.** `fp-subshift-full-group-subgroups-extend-to-sft` produces an SFT neighbourhood, and `X` is already one. So finite presentation imposes no periodic-point condition through this theorem.
  - More precisely, any argument that reads only finite orbits of SFT neighbourhoods is blind here, by Theorem A.
- **Known theorems stop.** Matui's finite presentation theorem (arXiv:1210.5800) covers one-sided irreducible SFT groupoids, which are compressible and hence non-amenable. Nekrashevych's finite presentation results (arXiv:1312.5654, lines 50–90) concern expanding maps and hyperbolic groupoids. Neither covers a two-dimensional zero-entropy-type SFT groupoid, and I found no finite presentation criterion for `Z^2`-SFT groupoids in the sources read.
- **Soficity.** `Gamma` is sofic: Elek–Monod line 128 notes that full groups of minimal subshifts of amenable groups are sofic (Elek–Szabó). A finitely presented infinite simple group is isolated in the space of marked groups, but soficity gives no contradiction with that.

## 5. Not verified

- **Primary sources behind the quotations.** Matui's simplicity theorem (ChJN's [matui1]) was used only as quoted by ChJN, and not from the primary paper.
- **Kerr–Nowak.** The primary paper was not read. The definition used is Ma's restatement of it.
- **Labbé.** His later papers connecting `Omega_U` to toral `Z^2`-rotations and to Jeandel–Rao were not read.
- **Literature search.** The arXiv API was rate-limited ("Rate exceeded", then HTTP 503). No search for existing work on full groups of minimal aperiodic SFTs was completed, so novelty of Theorem A and Theorem B is not claimed. Theorem A is an elementary pseudo-orbit argument and is very likely known.

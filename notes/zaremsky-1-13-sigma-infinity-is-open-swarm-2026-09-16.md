# Zaremsky 1.13 (is Σ^∞ open?): swarm lane, 2026-09-16

Target: `zaremsky-1-13-sigma-infinity-is-open`.
Hole worked: `every-f-infinity-group-has-open-sigma-infinity`, locked for this lane.

New nodes:
- `bounded-displacement-mapping-torus-sigma-infinity-open` (claim);
- `bounded-displacement-mapping-torus-sigma-infinity-open-proof` (route, `requires: []`);
- artifact `research/artifacts/zp-sigma-infinity-mapping-torus-displacement-2026-09-16.md`.

## 1. Status gate (checked 2026-09-16)

- Zaremsky, *Some open problems*, https://zaremsky.github.io/open_problems.pdf.
  - Downloaded 2026-09-16. The PDF text was extracted with a zlib/TJ script,
    since no pdftotext was available.
  - The file carries the date July 12, 2026. Problem 1.13 is still listed, with
    no note that it was solved.
- arXiv API sweep, 2026-09-16: queries `abs:BNSR`, `ti:"Sigma invariants"`,
  "Novikov homology", "BNSR automorphism", "semidirect/extension Sigma".
  - Recent hits read at abstract level:
    - 2606.02978 (BNSR of link groups, 2026-06);
    - 2605.28595 (twisted jump loci bound Σ, 2026-05);
    - 2606.26033 (strong fundamental domain ⇒ homological Σ empty or dense, 2026-06);
    - 2512.16039 (fixed subgroups of automorphisms, 2025-12);
    - 2505.18826 (McCool groups, 2025-05);
    - 2502.16026 (tropical integral jump loci, 2025-02);
    - 2404.12334, 2403.04941, 2401.05545 (2024).
  - None states non-openness of `Σ^∞`, a group of type `F_∞` with infinitely
    many distinct `Σ^m`, or a bounded-displacement or uniform-certificate
    criterion for openness.
  - The novelty check is at abstract level only. The criterion is elementary,
    so it may exist informally in the literature. Treat it as a reusable
    lemma, not as a claim of priority.

## 2. Setup and a homological reformulation

- **Setup.** `Σ^m(G)` is open for every `m`, and `Σ^∞ = ∩_m Σ^m`. The
  established depth lemma says non-openness at `χ` needs finite-depth characters
  accumulating at `χ` with depth `→ ∞`.
- **Reformulation.** For `m ≥ 2`, `Σ^m(G) = Σ^2(G) ∩ Σ^m(G;Z)`
  (arXiv:2309.12213, eq. (2.1)), and `Σ^2(G)` is open. So for
  `[χ] ∈ Σ^∞(G)`, `Σ^∞(G)` is a neighbourhood of `[χ]` iff `Σ^∞(G;Z)` is.
  Problem 1.13 is therefore purely homological at the points of `Σ^∞(G)`:
  can Novikov homology `Tor_*^{ZG}(Nov_ξ, Z)` vanish in all degrees at `ξ = χ`,
  while nearby characters have Novikov homology that is nonzero only in
  degrees tending to infinity?

## 3. What was proven (full proofs in the artifact)

- **Sign check (artifact §2).** In the Novikov–Sikorav criterion, the
  completion that works is the one allowing infinite sums towards `+∞` of `ξ`.
  - Test group: `BS(1,2)` with `χ(t) = 1`, `t a t^{-1} = a^2`.
  - `[χ] ∉ Σ^1`, and `H_1` over that completion is nonzero: map to
    `Z((s))`, where `t − a − 1 ↦ s − 2` is not a unit.
  - `[−χ] ∈ Σ^1`, and all homology over its completion vanishes.
  - The repo's notation `\widehat{ZG}_{-χ}` is ambiguous without this check.
- **Theorem A (mapping tori).** Setting: `G = N ⋊_φ Z`, `N` of type `F_∞`,
  `χ` the fibre character, `V = Hom(N,R)^φ`.
  - Take a lift `f'` of `φ^{-1}` on a finite-type free resolution of `N`, with
    displacement `Δ(f') < ∞`. This means the supports of all matrix entries,
    in all degrees, have `V`-norm bounded uniformly. Then
    `Tor_*(Nov_{aχ+ψ}(G), Z) = 0` for `a > ‖ψ‖Δ(f')`.
  - Proof sketch: the resolution is `Cone(1 − τ)`, `τ(g ⊗ x) = g t ⊗ f'(x)`.
    Over the Novikov ring, `τ` has valuation `≥ a − ‖ψ‖Δ > 0` in every degree,
    so `1 − τ` is invertible by a geometric series and the cone is contractible.
  - Symmetrically, lifts of `φ` handle `−[χ]`.
  - With lifts of both `φ^{±1}`, the conclusion does not depend on the sign
    convention. Then `Σ^∞(G)` contains open neighbourhoods of `±[χ]`.
- **Corollary C (artifact §4).** A power `φ^{±k}` with bounded-displacement
  lifts suffices. The proof uses Shapiro's lemma for Novikov modules over the
  index-`k` subgroup. This covers `φ` of finite order in `Out(N)`.
  - The hypothesis depends only on the outer class.
  - It is automatic for `N` of type F.
- **Proposition B (artifact §5).** For any `Γ` of type `F_∞` and any `ξ`, a
  *uniform certificate* gives openness of `Σ^∞(Γ;Z)` at `ξ`. A uniform
  certificate is a chain endomorphism `φ` lifting `id_Z` with
  `inf_i v_ξ(φ_i) > 0` and uniformly bounded support norms.
  - Proof: `1 − φ` is null-homotopic and invertible over the Novikov ring, so
    the tensored resolution is contractible.
  - This makes precise the "no uniform bound" failure mode in the Attempts of
    `every-f-infinity-group-has-open-sigma-infinity`.

## 4. Approaches tried and where each dies

1. **General openness at discrete fibre characters.** The aim was to prove
   bounded-displacement lifts always exist.
   - Where it dies: no construction. A cellular realisation `f` of `φ` on a
     finite-type `K(N,1)` gives displacement per degree, controlled by how the
     `ψ`-height changes under `f` on `i`-cells. Nothing bounds this uniformly
     in `i`.
   - The Stein–Farley complexes of Thompson-type groups do have bounded height
     oscillation on cells, but they are not of finite type modulo the group.
   - Open.
2. **Extension lemma along `Σ^∞(N)` directions.**
   - The Novikov module `Nov_{aχ+ψ}(G)`, restricted to `N`, is a space of
     growth-conditioned sequences over `Nov_ψ(N)`.
   - If `Nov_ψ(N) ⊗ P_*` is contractible, each contraction has finite
     valuation shift in each degree. So the sequence complex is acyclic in every
     degree, and by the Wang sequence `aχ + ψ ∈ Σ^∞(G;Z)` for all `a`.
     Only the vanishing direction of the Wang sequence is needed.
   - Where it dies: this only helps for `ψ ∈ Σ^∞(N;Z)`. For openness it
     presupposes the openness problem for `N` over the invariant sphere
     `S(V)`. The bad directions `S(V) ∖ Σ^∞(N;Z)` are not known to be closed.
     Not written up as a node.
3. **Reformulating non-openness as unbounded "valuation growth" of `f_*` on
   Novikov homology.**
   - Idea: compare `H_i(N; Nov_ψ(N))` for invariant `ψ ∉ Σ^∞(N)` against the
     Wang map `1 − t f_*`.
   - Where it dies: the quotient valuations on these homology modules are not
     norms, and I could not state a clean equivalence. Notes only.
4. **Stein-type slope groups as a no-witness (M3 variant).**
   - Setting: `N_0` = PL homeomorphisms of `R_{>0}` with slopes in `⟨2,3⟩` and
     breakpoints in `Z[1/6]`, and `G = N_0 ⋊ Z^2` by the two scalings.
   - Where it dies: the kernels of rational directions `(p,q)` are
     `N_0 ⋊_{2^q 3^{-p}} Z`. `Z[1/6]/(2^q − 3^p)` is finite, so no arithmetic
     obstruction to finite generation appears. I found no depth mechanism
     along rational directions.
   - Caveat: the `F_∞`-ness of these kernels was not verified, so this is
     heuristic only.
   - By Theorem A, any witness of this shape at a discrete character must
     defeat bounded displacement.
5. **Inner or finite-order monodromy; products; finite-cd fibres.** These give
   no witness:
   - inner or finite-order monodromy: Corollary C;
   - products: depth is additive (earlier artifact, M1);
   - fibres of finite cd: `bnsr-invariants-stabilize-at-cohomological-dimension`.
6. **Brin's `Aut(F)` periodic germs (a lead from the 1.18 lane).**
   - Here `V = Hom(F,R)`, both endpoint slope characters.
   - A test case for Theorem A: compute a lift of the monodromy on the
     Brown–Geoghegan resolution (two cells per positive dimension) and check
     whether the endpoint-slope displacement is bounded.
   - Not done. This is the recommended next computation.

## 5. Recommended next steps

- **Brin's `Aut(F)`.** Compute the displacement of `h ∈ Aut(F)` with periodic
  germs on the Brown–Geoghegan complex. Bounded displacement gives openness of
  `Σ^∞(F ⋊_h Z)` at the fibre characters. Unbounded displacement for all
  choices would be the first mapping-torus candidate for a negative answer at a
  discrete point.
- **Converses.**
  - Does openness at `±[χ]` force a bounded-displacement lift?
  - Does openness force a uniform certificate?
  - A converse would turn Theorem A into an exact reformulation of Problem 1.13
    at discrete fibre characters.
- **Other characters.** Irrational characters, and characters with
  `−[ξ] ∉ Σ^∞`, are untouched by Theorem A. Proposition B is the only tool
  there.

## 6. Imports and their trust status

- **Used as standard, with the same trust surface as existing
  `requires: []` routes:**
  - Novikov–Sikorav criterion (Suciu arXiv:2010.07499, abstract; the sign is
    checked in artifact §2);
  - comparison `Σ^m = Σ^2 ∩ Σ^m(·;Z)` (arXiv:2309.12213, eq. (2.1));
  - openness of `Σ^2` (arXiv:2505.18826, §2.1);
  - the BGK kernel criterion (arXiv:1502.02620, Citation 1.2).
- **Not re-verified here, and not used in any node proof:** the Bieri–Renz
  valuation criterion, and the claim that it gives degreewise certificates.
  These are mentioned only in artifact §5 remarks.

## Referee (2026-09-16)

**What was checked.**

- *Status gate.* Re-downloaded https://zaremsky.github.io/open_problems.pdf on
  2026-09-16 and extracted its text: the file is dated July 12, 2026 and
  Problem 1.13 ("Every Σ^n(G) is an open subset of the character sphere Σ(G),
  but what about Σ^∞(G)? Must that be open?") is still listed with no
  resolution note. The referee's web-search budget was exhausted, so the
  novelty audit rests on the solver's abstract-level arXiv sweep; the notes
  already disclaim priority, and the claim is labelled as a criterion, not as a
  resolution of 1.13.
- *Citations.* Fetched the arXiv abstract pages of 2010.07499 (Suciu,
  *Sigma-invariants and tropical varieties*; the quoted Novikov–Sikorav
  sentence is in the abstract), 2309.12213 (Molyneux–Nucinkis–Santos Rego,
  golden-mean Thompson group), 2505.18826 (Ershov–Zaremsky, McCool groups) and
  1502.02620 (Zaremsky, Σ-invariants of `F_{n,∞}` and Houghton groups). All
  exist and match the repo's earlier use. Equation (2.1), §2.1 and Citation
  1.2 were not re-read in the PDFs; the imports (I1)–(I4) are the same trust
  surface as the landed `bnsr-invariants-stabilize-at-cohomological-dimension-proof`.
- *Theorem A, line by line.* Well-definedness of `τ(g ⊗ x) = g t ⊗ f'(x)`
  (`n t = t φ^{-1}(n)`), `ZG`-linearity, the cone being a finite-type free
  resolution of `Z` (long exact sequence with `1 − ρ` injective, cokernel `Z`),
  the identification `M ⊗ τ` = right multiplication by `T_i = (t c^{(i)}_{jk})`
  on row vectors, the estimate `χ'(t g) = a + ψ(g) ≥ a − ‖ψ‖Δ`, convergence of
  `Σ T^n` in the Novikov ring, and the symmetric `t^{-1}` version. All correct.
- *Corollary A1 / both completions.* For `[ξ]` in the double cone both `ξ` and
  `−ξ` satisfy the vanishing hypothesis, so the conclusion does not depend on
  the sign in (I1). Correct.
- *Corollary C (powers).* `Nov_ξ(G) ≅ ⊕_i Nov_{ξ|H}(H) g_i = Nov_{ξ|H}(H) ⊗_{ZH} ZG`
  as right `ZG`-modules (finite index is used, so the sum is finite), plus
  Shapiro. Correct. Lifts `x ↦ n_0^{±1} x` of `c_{n_0^{±1}}` check out.
- *Sanity tests.* `F_2 × Z` viewed as `F_2 ⋊_{c_x} Z`: the region
  `|a| > ‖ψ‖` from Theorem A is contained in the true region `a ≠ ψ(x)` and is
  sharp at `‖ψ‖ = |ψ(x)|`. `F_2 ⋊ Z` with the generator swap (Δ = 0) and
  `Z^3` also agree with known invariants.
- *Artifact §2 (sign).* Recomputed the Fox derivatives of `t a t^{-1} a^{-2}`,
  checked `d∘d = 0` using `ta = a^2 t`, the Cayley-graph connectivity
  (component of `1` at level 0 is `Z`, so `[χ] ∉ Σ^1`, `[−χ] ∈ Σ^1`), the unit
  computations over `Nov_{−χ}`, and the obstruction `t − a − 1 ↦ s − 2` in
  `Z((s))`. Correct under the stated conventions (right module tensored with the
  left cellular chain complex; `Γ_χ = {χ ≥ 0}` with edges `g — gs`).
- *Proposition B.* Null-homotopy of `1 − φ`, invertibility over the perturbed
  Novikov ring, and `1 = d(uh) + (uh)d`. Correct.
- Duplicates: `bin/cairn search --similar` shows only the open 1.13 answer
  claims and unrelated nodes; `distinct_from` entries are adequate.

**What was changed.**

- The claim's "Consequence for Problem 1.13" said that failure of openness
  forces *every lift of every power* of the monodromy to have unbounded
  displacement. The sign-free route only proves that for each `k` the lifts of
  `φ^k` and `φ^{-k}` are not both bounded; the one-sided sharpening (artifact
  §3, §6) needs the sign pinned in artifact §2 and gives "every `φ^{-k}`" at
  `[χ]` and "every `φ^k`" at `[−χ]`, never all powers at once. Reworded the
  claim accordingly and added a pointer to
  `finite-outer-order-mapping-torus-is-virtually-product`.
- Artifact §5 (Proposition B): the "same holds for `−ξ`" sentence now names
  the second certificate's constants and the radius `min(c/R, c'/R')`.

**Caveats kept in notes only.** §4.2 above (extension lemma along
`Σ^∞(N)` directions) and §4.4 (Stein-type slope groups) are sketches that were
not refereed as proofs; they are not used by any node.

**Verdict.** Theorem A, Corollaries A1 and C and Proposition B are sound, with
the standard imports (I1)–(I4). The claim is an honest criterion for openness
at fibre characters of mapping tori; Problem 1.13 remains open. Landed with the
wording fix above.

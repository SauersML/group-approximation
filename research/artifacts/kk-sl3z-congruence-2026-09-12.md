# Kadison–Kaplansky on torsion-free subgroups of SL_3(Z): literature status, a fence, and the congruence-trace dead end

Lane `kk-torsion-free-congruence`, 2026-09-12. Hosts: torsion-free finite-index
subgroups `Γ` of `SL_3(Z)`, e.g. the principal congruence subgroup `Γ(3)` and the
level-3 elementary subgroup `E_3(3)`. Root: `kadison-kaplansky-torsion-free`.

All quotations below come from arXiv PDFs downloaded and extracted with
`pdftotext -layout` on MSI (`/scratch.global/sauer354/kkcong`). The line numbers
refer to those text files.

## 1. Status: open

No source says Kadison–Kaplansky is known for these groups. Four independent sources
(2007–2019) say the mechanism that would give it, Baum–Connes surjectivity, is open for
`SL_3(Z)`. One of them says outright that Kadison–Kaplansky is open for its principal
congruence subgroups.

- **M. Fuchs, arXiv:math/0612023v2 (2007), p. 4 (lines 449–453).** "The theorem is weaker
  than the analogous statement for the C*-algebraic completion C*_r Γ where it is known
  under the name Kadison-Kaplansky conjecture and still unsolved for the class groups
  considered in this paper. The Kadison-Kaplansky conjecture is an easy corollary of the
  Baum-Connes-conjecture calculating K_0(C*_r Γ). However, the latter is unproved even for
  SL(3, Z) or its principal congruence subgroups, which are torsion-free."
  The same page (lines 442–445) says the *algebraic* idempotent theorem for `CΓ` "has been
  proved by Lafforgue ([36]), using Banach KK-theory, and by Puschnigg ([42])".
- **Gomez Aparicio–Julg–Valette, arXiv:1905.10081 (2019).**
  - p. 6–7 (lines 276–278): "the conjecture without coefficients is true for all cocompact
    lattices in SL3 (R) but it is still open for SL3 (Z)".
  - p. 57 (lines 2874–2877): "nothing is known about the Baum-Connes conjecture for general
    discrete subgroups of G. In particular it is not known whether SL3 (Z) satisfies
    Conjecture 4".
- **Kammeyer–Lück–Rüping, arXiv:1401.0876v2 (2015), Introduction.** "the Baum-Connes
  conjecture ... is still open for many lattices in virtually connected Lie groups, for
  instance for SL(n, Z) for n ≥ 3."
- **Bartels–Lück–Reich–Rüping, arXiv:1204.2418v2 (2013), Introduction.** "It is a long
  standing question whether the Baum-Connes Conjecture holds for GLn (Z)."

**Recency.** arXiv API searches on 2026-09-12 found no paper after 2018 claiming
Baum–Connes or Kadison–Kaplansky for `SL_3(Z)` or its subgroups. The queries were
`abs:Kadison AND abs:Kaplansky`, `abs:"SL(3,Z)" AND abs:Baum`, and
`abs:"Baum-Connes" AND abs:"higher rank"`. The newest hit on `SL_3(Z)` was
Sánchez-García's Bredon homology computation (math/0601587), which is the left-hand side
only. `lit-scout-2-findings-2026-09-12` found no 2025–26 Baum–Connes or
Kadison–Kaplansky result for Kazhdan groups. A plain title listing, done after this
file's first landing, is recorded in Section 5.

**Why every known method stops at `SL_3(Z)`.**
- **Higson–Kasparov:** needs the Haagerup property, which property (T) excludes.
- **Hyperbolic methods (Mineyev–Yu, Lafforgue, Puschnigg):** `SL_3(Z)` contains `Z^2`, so
  it is not hyperbolic.
- **Rapid decay (Lafforgue, Corollary 1.6.3 of the ICM address; AJV Theorem 6.15):** it
  fails for `SL_3(Z)`, see `sl3z-has-no-spectral-unconditional-completion`.
- **Strong property (T):** it holds for `SL_3(Z)` (de la Salle, quoted in AJV p. 109,
  lines 5616–5617). So Lafforgue's Banach-representation homotopies cannot deform the
  `γ`-element to `1` in any category that descends to `C*_r`.

## 2. What does hold on these hosts

1. **Unconditional assembly.** By `lafforgue-unconditional-assembly-for-reductive-lie-subgroups`,
   every closed subgroup of a reductive Lie group has
   `μ_A : K_*^G(\underline{E}G) → K_*(A(G))` an isomorphism for every unconditional
   completion `A(G)`. Sources: Lafforgue, ICM 2002 (arXiv:math/0304342), Theorem 1.6.2
   (lines 444–451), and the remark before Theorem 1.5.3 (lines 332–336): classes a′), c′)
   "respectively contain all closed subgroups of reductive Lie groups, and all hyperbolic
   groups". AJV §6.1.2 (lines 2665–2674) records the same thing.
2. **Algebraic idempotents are trivial.**
   - Lafforgue's route (Fuchs, above) works through `ℓ¹(Γ)`: item 2 of
     `unconditional-spectra-of-kk-witnesses-cross-the-gap`.
   - Independently, the Farrell–Jones route gives every field of characteristic zero:
     Bartels–Lück–Reich, arXiv:math/0703548, Theorem 0.12(ii) and the sentence after it
     (lines 338–356), together with Kammeyer–Lück–Rüping Theorem 1 (lattices in virtually
     connected Lie groups lie in FJ).
   - With `small-capacity-kk-witnesses-are-algebraic-idempotents`, every Kadison–Kaplansky
     witness `a ∈ Z[i][Γ]` has spectral capacity at least 1.
3. **The fence (new packaging, no novelty claimed).**
   `unconditional-spectra-of-kk-witnesses-cross-the-gap`. If a reduced spectral projection
   of `a ∈ M_n(Z[i][Γ])` has non-integral trace, then for every unconditional completion
   `A(Γ) ⊆ C*_r(Γ)`, the spectrum of `a` in `M_n(A)` meets the vertical line through the
   gap. In particular the `ℓ¹(Γ)`-spectrum does. Proof on the route node.
4. **Where the fence stops.** By AJV Remark 6.18 (lines 2883–2905, credited to Lafforgue
   [Laf10]), `SL_3(Z)` has no unconditional completion that is dense in `C*_r` and closed
   under holomorphic calculus.
   - The obstruction sits on the amenable subgroup `H = Z^2 ⋊_A Z`, `A = [[3,1],[2,1]]`,
     through Jenkins's non-symmetric `ℓ¹(H)`.
   - Kadison–Kaplansky holds on `H` itself (amenable, so Haagerup).
   - So the spectral excess that a witness must exploit already appears on subgroups where
     no witness can live.

## 3. Trace limits along congruence towers (directive item (a)): a dead end

**Lemma (any residually finite group; elementary).** Let `Γ_N ⊲ Γ` have finite index, and
suppose every finite subset of `Γ \ {1}` misses `Γ_N` for large `N`. Let
`a = a* ∈ M_n(C[Γ])`, `c ∉ spec_r(a)`, and `π_N` the regular representation of `Γ/Γ_N`.
Then

```text
tau( chi_(-inf,c)(lambda(a)) ) = lim_N  #{eigenvalues of pi_N(a) below c} / (n [Γ:Γ_N]).
```

*Proof.*
1. `Tr π_N(a^m) / (n[Γ:Γ_N]) = τ(a^m)` once `Γ_N` avoids the support of `a^m`.
2. All the normalized eigenvalue measures `μ_N` live in `[-||a||_1, ||a||_1]`. Moment
   convergence therefore gives `μ_N → μ_a` weakly.
3. `μ_a({c}) = 0`, since `c ∉ supp μ_a = spec_r(a)` (`reduced-projection-iff-gapped-spectral-measure`).
   Portmanteau finishes. QED

This is the formula of `bc-kun-thom-trace-test-2026-09-12` §4, for any residually finite
group. Every projection of `M_n(C*_r Γ)` has this form up to unitary equivalence:
approximate it within `1/4` by a self-adjoint element of `M_n(Q(i)[Γ])` and take the
spectral projection above `1/2`.

**Why no integrality comes out of it.**
- **No use of torsion-freeness.** The formula holds verbatim for groups with torsion. Over
  `Z × Z/2` the torsion projection `(1+g)/2` has counts exactly `1/2` in every quotient. The
  quotients `Γ/Γ_N` all have torsion.
- **The congruence completion adds nothing.** Let `C*_Λ(Γ)` be the completion of `C[Γ]` in
  `⊕_N π_N`; it weakly contains `λ`. For a free ultrafilter `ω`, the ultralimit
  `τ_ω = lim_ω τ_N` is a continuous trace on `C*_Λ` that agrees with `τ∘λ` on `C[Γ]`, hence
  everywhere. So the tower sees exactly the reduced trace and no extra K-theoretic
  information.
- **Uniform gaps fail for Kazhdan towers.** `ℓ²(Γ/Γ_N)` contains non-tempered constituents:
  the trivial representation, and permutation representations of `SL_3(Z/N)` on projective
  spaces. Their eigenvalues may lie inside a reduced gap. They carry vanishing proportion
  but need not vanish. A uniform gap would put `χ(a)` in `C*_Λ`, but by the previous item
  that still gives only rational approximants of `τ(χ)`.
- **Pro-3 tower (item (b)).** `Γ(3)/Γ(3^k)` is a 3-group, so denominators are powers of 3.
  That constrains algebraic idempotents only, which Section 2 already makes trivial. A
  gapped non-algebraic projection has capacity at least 1, and its trace is a real limit
  that no denominator condition controls.
- **Spectral gaps from (T) (item (c)).** A Kazhdan gap bounds `Δ` on `ℓ²_0(Γ/Γ_N)` away from
  `0`. It isolates only the trivial representation, whose spectral projection has
  `τ_ω = lim 1/[Γ:Γ_N] = 0`.

**Verdict.** Congruence towers compute the trace of a candidate projection. They cannot
certify integrality or its failure: any real number is a limit of the rational counts they
produce. A proof needs index theory beyond the unconditional completions (Section 2.4). A
refutation needs a projection whose `K_0`-class avoids the image of every
`K_0(A(Γ)) → K_0(C*_r Γ)`, with `A` unconditional.

## 4. Remaining sub-targets (not opened as graph nodes)

- **Trace limits of explicit elements.** Compute `lim #{eig < c}/|F_N|` for concrete
  `a ∈ Z[Γ(3)]` with a numerically visible reduced gap. Warning: reduced spectra are not
  computable from finite quotients, because of the non-tempered contamination above. Only
  guidance.
- **ℓ¹ versus reduced spectra of self-adjoint elements of `Z[Γ(3)]`.** By the fence, a
  witness is an element whose reduced gap is closed by non-symmetric spectrum in every
  unconditional completion. Whether the excess spectrum of natural elements (sums of
  generators of `E_3(3)`) comes only from amenable subgroups of exponential growth, as in
  Remark 6.18, is the concrete question a counterexample search would start from.

## 5. Recency listing

arXiv API title listings were run on MSI on 2026-09-12, newest first, for 2020–2026.

- **`ti:Baum AND ti:Connes`: 32 hits.** None of the titles names `SL_n(Z)`, a higher-rank
  lattice or property (T). They cover:
  - coarse and groupoid versions;
  - extensions (arXiv:2508.05726, 2601.09615);
  - Dehn fillings (arXiv:2509.15070);
  - relatively hyperbolic groups (arXiv:2512.21169);
  - semigroup crossed products;
  - `D_∞`;
  - higher Kazhdan projections (arXiv:2006.09317).
- **`ti:Kadison`: 18 hits.** All are about Kadison–Singer, Kadison–Schwarz, Kadison's
  orthonormal-basis problem, or Fuglede–Kadison determinants. None is about the
  idempotent conjecture.

Only titles were screened. The abstracts of these hits were not read. The earlier abstract
searches (Section 1) found nothing newer either. So the "open" status stands, subject to
that limit.

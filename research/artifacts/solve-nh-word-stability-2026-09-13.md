# Where published HS-stability mechanisms stop on hyperbolic Kazhdan groups

Lane `solve-nh-word-stability`, 2026-09-13.

**Target.** `non-hyperlinear-group`, through `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity`.
Its open premise, `kazhdan-hyperbolic-b2-group-flexibly-hs-stable`, asks for one word-hyperbolic
Kazhdan group `Γ` with `b_2 ≥ 1` that is flexibly HS-stable.

**Directive.** Find a non-cohomological, word-specific stability mechanism, or show exactly where
every known mechanism fails.

**Verdict.** No mechanism was found. One reduction theorem landed:
`kazhdan-hs-instability-lives-on-properly-nonamenable-limits`. Every mechanism below stops at an
identified step. The premise stays OPEN.

## 1. Sources fetched on MSI (`~/nhws/<arXiv id>/`)

- 2506.20843 (Dogon--Vigdorovich), `Sigma_submission.tex`
- 2211.10492 (Dogon), `main.tex`
- 1809.00632 (Becker--Lubotzky), `main.tex`
- 1901.07182 (Lazarovich--Levit--Minsky), `stability_submission.tex`
- 2310.17474 and 2311.06706 (Chapman--Lubotzky I and II), `Part1.tex` and `Part_2.tex`
- 1909.08507 (Dinur--Meshulam), `covers_arxiv1.tex`

Line numbers below refer to those files.

## 2. Mechanism map

**M1. Amenable-trace uniqueness.** Hadwin--Shulman, generalized as DV `thm:HS_for_non_amenable_grps`,
l.1557–1562: "Γ is hyperfinitely Hilbert--Schmidt stable" iff "every von Neumann amenable character
of Γ is a limit of finite dimensional traces."
- *What it does.* It corrects asymptotic representations whose limit algebra is amenable, through
  uniqueness of embeddings of that algebra.
- *Where it stops.* For every Kazhdan group this face is automatically stable: (A1)–(A2) of the new
  claim. Mixed limits reduce to their properly non-amenable part: (A3).
- *So:* it certifies nothing beyond (T). A witness to instability of a candidate is properly
  non-amenable. For separating approximations the limit algebra is `L(Γ)`, a non-amenable II₁ factor
  (non-elementary hyperbolic groups without finite normal subgroups are ICC).

**M2. Character rigidity.** DV Theorem 1.6, imported on main as
`character-rigidity-equals-hyperfinite-hs-stability`, together with the fp-simple dictionary
`character-rigid-fp-simple-groups-stability-dictionary`.
- *Where it stops.* It needs a higher-rank lattice (charmenability) or a simple group. `Γ` is neither.
- `Γ` is also not character rigid: `ah-groups-fail-regular-fd-character-rigidity` pulls back the
  regular character of an infinite ICC Dehn-filling quotient.

**M3. Products.** DV `prop:hyp_stab_prod`, l.1583–1593: F₂×F₂ "is hyperfinitely Hilbert--Schmidt
stable, while it is not Hilbert--Schmidt stable, as shown by Ioana."
- *Where it stops.* A non-elementary hyperbolic group is not virtually a product of two infinite groups.
- *Why* (standard, not re-read): torsion subgroups of hyperbolic groups are finite. So two commuting
  infinite factors would contain commuting infinite-order elements generating `Z²`, which hyperbolic
  groups do not contain.

**M4. Geometry of surfaces.** Lazarovich--Levit--Minsky, l.164–166: "Let $S$ be a closed orientable
surface of genus $g \ge 2$. Then the fundamental group $\pi_1(S)$ is flexibly stable in permutations."
By l.101–103 this is "the first non-trivial example of a non-amenable flexibly stable group"; the
method is branched covers of hyperbolic surfaces.
- *Where it stops.* The coefficients are permutations. The argument uses the 2-manifold structure,
  and a Kazhdan group is not virtually a surface group (surface groups surject onto `Z`).
- l.227 adds: "there exist small cancellation hyperbolic groups that are not even flexibly stable"
  (permutations).

**M5. Becker--Lubotzky.**
- l.185–188: infinite hyperlinear Kazhdan groups are not strictly HS-stable.
- §5, l.989–1000: the Rips construction gives hyperbolic groups that are not flexibly P-stable,
  through quotients with finitely generated kernel.
- *Why the Rips step does not transfer to HS.* In permutations, the fixed set of a finitely
  generated normal kernel is invariant and almost full. In the normalized HS metric, almost-trivial
  action of the kernel's generators forces almost-invariant vectors, not a nearly full fixed
  subspace, unless the kernel has (T). That is the hypothesis of
  `flexible-hs-stability-passes-to-kazhdan-kernel-quotients`. So neither direction transfers.

**M6. Coverings and cocycles.**
- *Chapman--Lubotzky II.*
  - l.289: complete complexes and spherical buildings are coboundary expanders; both are simply connected.
  - l.804: for a complex whose fundamental group has (τ), "finite coverings … have a uniform lower
    bound on their cosystoles." That is rigidity (distance between cocycles), not a Cheeger constant.
  - l.1122: "We do suspect that a random object should not be stable in the mid-range."
- *Dinur--Meshulam,* l.107–108: cover-stable iff cosystolic expander "with respect to non abelian
  coefficients"; the example is the spherical building $A_3(\mathbb{F}_q)$.
- *Where it stops.*
  - The coefficients are `Sym(n)` or discrete groups, and unitary HS coefficients are not treated.
  - The positive examples have trivial `π_1`.
  - For `π_1 = Γ` the relevant quantity is the cocycle Cheeger constant, which is the open Chapman--Peled
    hypothesis on main (`random-complex-cocycle-cheeger-beats-triangle-count`).

**M7. Cohomological existence.** De Chiffre--Glebsky--Lubotzky--Thom Newton steps and bounded
degree-two primitives.
- *Where it stops.* `H²(Γ; C) ≠ 0` sits on the trivial summand of every adjoint module (`b_2 ≥ 1`).
- Relator adjunctions only enlarge it (`relator-adjunctions-grow-degree-two-cohomology`, e1cce5941).
- For the GHB(7) kernel, `ghb7-kernel-blocks-degree-two-newton-stability` records the same failure.

**M8. Robust spectral gap.** DV `cor:eq defs of robust`, l.1779–1786:
"(T) ⟹ (T;W*)_rob ⟺ (T;W*) ⟹ (T;CE) ⟺ (T;FD)_rob ⟹ (T;FD) ⟹ (τ)".
- *What it gives.* Uniform spectral gap for almost representations. That is rigidity: nearby genuine
  representations are nearly conjugate, and amenable limits are atomic (A1).
- *Where it stops.* It does not produce a genuine representation near an asymptotic one.

**M9. Weak ucp-stability** (Dogon, 2211.10492).
- *Where it stops.* It is a consumer, not a producer. For hyperlinear Kazhdan groups it equals flexible
  stability (`kazhdan-weak-ucp-stability-is-flexible-stability`).

## 3. What a proof has to do

By M1 and (A3), a proof must correct properly non-amenable asymptotic representations: separating
approximations with limit `L(Γ)`, and the twisted sectors of the Dogon--Vigdorovich corner theorem.
It must also meet the recorded constraints:
- it must use a property of the candidate that Belegradek--Osin covers lack
  (`classwide-hyperbolic-kazhdan-hs-stability-covers-fp-kazhdan`);
- for a hyperlinear candidate, it must produce a persistent prime degree-two class
  (`hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class`).

No source read here corrects asymptotic representations on a non-amenable limit for any infinite
Kazhdan group.

**Natural combinatorial form, not attempted.** A lower bound on the unitary (normalized-HS) cocycle
Cheeger constant of the candidate's 2-complex. It would be the unitary analogue of Chapman--Lubotzky I,
which no source treats.

## 4. Not done

- Jung's theorem (non-uniqueness of embeddings of non-amenable algebras into `R^ω`) was not pinned.
- Ioana's F₂×F₂ result is quoted only as DV state it.
- The standard hyperbolic-group facts in M1 (ICC) and M3 were not re-read.
- No numerics.

# Random hyperbolic Kazhdan groups as non-hyperlinear candidates (lane solve-nh-random-t, 2026-09-13)

Target: hyperlinearity or soficity of random hyperbolic groups with property
(T), as a source of a non-hyperlinear group.

**Verdict:** partial.
- **Landed:** one elementary theorem, a dimension collapse for almost-representations of random presentations (`density-random-groups-no-small-nondegenerate-almost-reps`). It is ESTABLISHED in the graph but has not been independently reviewed.
- **Not decided:** the hyperlinearity of random groups at densities in [1/6, 1/2).

## 1. Literature, from source text (TeX on MSI, `/scratch.global/sauer354/random-t`)

**Ashcroft, arXiv:2202.12318**, *Property (T) in random quotients of hyperbolic groups at densities above 1/3*.
- TeX l.128–129, Theorem A: "Let G=⟨S | T⟩ be a non-elementary hyperbolic group with growth rate 𝔥. Let ω(l) ≤ log log l be any slow-growing function. Let d>1/3 and for each l≥1 uniformly randomly select a set R_l ⊆ Ann_{l,ω}(G) of size exp{𝔥ld}. The group G/⟨⟨R_l⟩⟩ has Property (T) with probability tending to 1 as l tends to infinity."
- TeX l.155, quoted literally: "Groups in the density model are virtually special for d<1/6 \cite{Ollivier-Wise, Agol13} and contain a free codimension-1 subgroup for d<3/14 \cite{montee2021random} ... a random group in the density model has Property (T) at d>1/3 \cite{Zuk,kotowski,ashcroft2021property}".
- TeX l.150 and l.152: for groups with harmful torsion and 1/3<d<1/2 it is asked whether the quotients are almost surely infinite and hyperbolic.

**Kotowski–Kotowski, arXiv:1106.2242.**
- TeX l.98: "for d < 1/5 random groups in the density model do not have property (T)" (citing Ollivier–Wise).
- The same line: "It is an open problem to decide if the density 1/3 for the Gromov model can be improved or if it is critical for having property (T)".

**Survey arXiv:1702.01942** (*Random presentations and random subgroups*). I grepped its TeX for "residually finite", "sofic", "hyperlinear" and "virtually special". The only residual-finiteness statement found is l.463, "an A-generated 1-relator group is generically residually finite", about one-relator groups. The survey states nothing on residual finiteness, soficity or hyperlinearity of density-model groups at d ≥ 1/6.

**Status.** None of the sources read say anything about residual finiteness, soficity or hyperlinearity at densities in [1/6, 1/2). Below 1/6: virtually special, hence linear and hyperlinear (Ashcroft l.155 citing Ollivier–Wise and Agol; the primary sources were not re-read). I did one web search; it found nothing more. This isn't an exhaustive search.

**Repo context.**
- Already imported: `gromov-density-random-groups-kazhdan-above-third`, `gromov-density-random-groups-hyperbolic-aspherical` and `density-random-group-hyperbolic-kazhdan-with-positive-b2`.
- The stability route: `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` (ESTABLISHED) needs the open `kazhdan-hyperbolic-b2-group-flexibly-hs-stable`.
- The Chapman–Peled random-complex route has hypothesis `random-complex-cocycle-cheeger-beats-triangle-count`, refuted by `random-complex-cheeger-capped-by-triangle-count`.

## 2. The first-moment test (directive step 3)

Model: `N = ⌈(2n−1)^{dℓ}⌉` independent uniform reduced relators of length ℓ.

**Per-relator bound** (letter swap). If two letters of a tuple V differ by more than 2ε′ in normalized Hilbert–Schmidt norm, a random relator is ε′-satisfied with probability at most 1 − κ_n, where κ_n = (n−1)/(2n(2n−1)²). Swapping the first letter of the relator by an independent admissible letter keeps it uniform, and changes r(V) by exactly ||x(V) − x′(V)||₂.

**Union bound.** An operator-norm δ-net of U(D) has at most (1+2/δ)^{2D²} points. The Lipschitz constant of a word of length ℓ is ℓ. So the expected number of nondegenerate almost-solutions is at most

```text
exp( 2nD² log(1 + 8ℓ/ε) − κ_n N ).
```

**Theorem (landed).** With high probability, every ε/2-almost representation of dimension D ≤ D_ℓ ≍ (2n−1)^{dℓ/2}/√(log ℓ) has all letters within 2ε of each other. That means it collapses to the length-parity map.

**What it shows.**
- Approximations need dimension at least about |R|^{1/2}.
- A random group has no nondegenerate finite quotient of order ≤ D_ℓ.
- This holds at every density, including d < 1/6, where the groups are hyperlinear. So it is only a bounded-dimension collapse.

## 3. Attempts

**(a) Proving random (T) groups are hyperlinear.** Unclear, no mechanism.
- Residual finiteness is the only generic tool, and it is known only through cubulation for d < 1/6. (T) excludes cubulation, since cubulated Kazhdan groups are finite (Niblo–Reeves; not re-read).
- Random permutation representations: by the landed theorem, any nondegenerate exact permutation model has degree > D_ℓ. The first moment for maps F_n → S_m allows surviving homomorphisms only once m ≳ N / log m. It says nothing about whether they exist.
- No strong-convergence or local-approximation argument for density-model groups was found.

**(b) Forcing non-hyperlinearity in all dimensions by counting.** Killed as a method.
- **Why it fails.** The union bound pays exp(C n D² log ℓ) for the net, and the per-relator bound is only a constant. That constant can't be improved uniformly over nondegenerate tuples. Take V = J^{⊕(1−t)D} ⊕ W^{⊕tD} with J an involution and t ≍ ε′². It is 2ε′-nondegenerate, yet a random relator is ε′-satisfied whenever r(W) is within about ε′/√t = O(1) of I, which has probability bounded below.
- **So what's out of reach:** dimensions with D² log ℓ ≫ N are beyond any first-moment argument with an R-independent per-relator bound.
- **What would be needed:** a structural, R-dependent argument, for example one where property (T) of Γ_R forces almost-invariant vectors of the Kazhdan projection to carry a dimension-independent defect. That is the open flexible-stability content of `kazhdan-hyperbolic-b2-group-flexibly-hs-stable`.

**(c) Cyclically reduced model.** The landed theorem uses independent reduced words. For Gromov's cyclically reduced words, the letter swap should move to a middle position, where the cyclic condition is untouched. The admissible-pair probability then needs a lower bound on adjacent-letter marginals of uniform cyclically reduced words. I didn't prove it, so nothing is claimed for that model.

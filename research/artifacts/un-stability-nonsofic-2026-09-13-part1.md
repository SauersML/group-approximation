# UN lane un-stability-nonsofic, part 1: stability of simple Kazhdan groups is nonsoficity

Lane `un-stability-nonsofic`, 2026-09-13. The directive asked for a stability route to nonsofic groups through the
dichotomy's simple Kazhdan groups `S = EL_N(A_k(𝒢))/Z`. This part records the sharp answer for simple groups and
the firewalls around the route.

## 1. The answer for simple groups

`infinite-simple-group-permutation-stable-iff-nonsofic` (proof in its `-proof` route):
- for an infinite simple group, strict and flexible permutation stability are each equivalent to nonsoficity;
- the correcting homomorphisms are always trivial.

The mechanism fits in one line. The limit kernel of an almost action is a normal subgroup, so simplicity makes it
`1` or `S`. `S` means the almost action is asymptotically trivial; `1` becomes a sofic approximation after
coordinatewise amplification.

**Consequence for the directive.** The planned implication "`S` permutation stable ⇒ `S` nonsofic", via
`sofic-stable-implies-residually-finite` and "infinite simple ⇒ not RF", is correct but empty: it is literally an
equivalence. Stability of `S` cannot be proved by any method that does not already prove nonsoficity of `S`.

## 2. Calibration on the two calibrating groups

| group | soficity | permutation stability |
|---|---|---|
| Pestov 9.1 `S = EL_3(LC(X,F_2)⋊Z)/Z` | LEF, hence sofic (Lean + Comparator) | unstable in every sense: its LEF models are far from the trivial action, the only genuine one |
| `H = L_(F_2)(1,2)^x = EL_2(L_(F_2)(1,2))` | nonsofic (`openai-leavitt-unit-nonsofic`) | stable in every sense; this recovers `binary-leavitt-unit-group-is-permutation-stable` without the character simplex |

The calibration matches the directive's expectation that stability fails on the measure side. It fails for exactly
the reason soficity holds.

## 3. Where a stability input can still matter (firewalls)

**F1. A simple group carries no stability information beyond soficity.** This is §1. Any stability-based
nonsoficity argument must place stability on a NON-simple input. Examples are a Kazhdan subgroup `L` with a
compressor `u`, or a lattice as in Bowen–Burton.

**F2. Hilbert–Schmidt transport needs operator-norm control.**
- The non-MF tex, footnote at l.204 and the paragraph at l.1844–1853, says the one-sided Kazhdan transport
  (Thm l.478) uses operator-norm control of conjugation maps. There the corona is stably finite, so `U*PU ≤ P`
  forces `U*PU = P`.
- In the sofic setting the tex's group `W = Cl(X) ⋊ V` is sofic, and `ε ∈ 𝔇_W(Γ)` moves almost every point. So the
  collapse of Cor l.571 fails there.
- A stability hypothesis on `L` does not repair it. Genuine finite actions `ρ` of `L` give exact inclusions of
  invariant-vector projections `P_L ≤ P_(uLu^-1)` and nearly equal normalized traces. That is small-RANK control,
  and a specific vector such as `σ(c)` can concentrate in a small-rank difference.
- So "flexible P-stability of `L` + compressor ⇒ `𝔇_G(L)` acts trivially in sofic approximations" does not follow
  from the tex's argument. It stays an open route with this recorded gap.

**F3. Literature recalled, not imported.**
- The PDFs are downloaded to `scratchpad/un/lanes/un-stability-nonsofic/lit/` but not quoted, so nothing below is
  load-bearing in an established node.
- Becker–Lubotzky, arXiv:1809.00632: (T) obstructs permutation stability for infinite residually finite groups, and
  they introduce flexible stability.
- Bowen–Burton, arXiv:1906.02172: flexible stability of `PSL_d(Z)`, `d >= 5`, would yield a nonsofic group.
- Arzhantseva–Păunescu, arXiv:1502.00805: presentation-based stability for finitely presented groups.

**F4. What is already on main, so this lane does not repeat it.**
- `halvable-corner-makes-elementary-groups-nonsofic`: one halvable idempotent in some `M_d(R)` over a finite field
  makes `EL_(nd)(R)` nonsofic.
- `purely-infinite-simple-algebras-have-nonsofic-el-groups`: every countable purely infinite simple algebra over a
  finite field has nonsofic `EL_n`, `n >= 2`.
- So the paradox side of the dichotomy is already NONSOFIC at the level of `EL_n`, not just "no MF quotient", for
  purely infinite simple algebras.

## 4. Part 2 plan

- **Lemma:** a proper halvable idempotent `s_0 t_0 < e` meets the central scalars trivially, so every quotient of
  `EL_(nd)(R)` by central scalars, and in particular the simple quotient `S`, is nonsofic.
- **Corollary (the stability face of the dichotomy).** For finitely generated purely infinite simple Steinberg
  algebras over finite fields, `S_N = EL_N/Z` (`N >= 3`) is an infinite finitely generated simple Kazhdan group that
  is nonsofic and permutation stable in every sense. Matricial algebras, Pestov's included, give sofic simple Kazhdan
  groups that are unstable.

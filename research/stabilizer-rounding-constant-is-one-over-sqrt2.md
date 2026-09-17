---
rg: 2
id: stabilizer-rounding-constant-is-one-over-sqrt2
kind: claim
title: The optimal constant in stabilizer rounding of Pauli sums is 1/sqrt2
artifacts:
  - research/artifacts/pauli-frustration-stabilizer-rounding-2026-09-12.md
  - research/artifacts/pauli-stabilizer-rounding-model-test-2026-09-12.md
  - experiments/stabilizer-rounding-constant-2026-09-17/README.md
distinct_from:
  pauli-sums-near-their-one-norm-round-to-stabilizer-states: that proves rounding with constant 1+sqrt2; this proves the sharp constant 1/sqrt2, which that claim's one-qubit example shows cannot be lowered.
---

**ESTABLISHED (ordinary proof, unreviewed; route `stabilizer-rounding-constant-is-one-over-sqrt2-proof`).** For every explicit Pauli decomposition `H = sum_P beta_P P` with weight
`W = sum|beta_P|`,

```text
max_(phi stabilizer) <phi|H|phi>  >=  lambda_max(H) - (1/sqrt2)(W - lambda_max(H)).
```

The constant cannot be smaller: `(X+Z)/2` has ratio exactly `1/sqrt2`.

**Why it matters.** It would lower the NP threshold for frustration ratios from
`2+sqrt2` to `1+1/sqrt2`. That is exactly where stabilizer witnesses stop working,
by the same example. It would narrow the open window for open problem 1 of
Natarajan--Nirkhe (see `pauli-norm-games-qpcp-needs-imperfect-completeness`) to
`1 < p/q <= 1+1/sqrt2`. The multiplicative factor for Pauli-projector Hamiltonians
in `pauli-projector-hamiltonians-are-stabilizer-approximable` would become
`1+1/sqrt2`.

## Attempts

- **The averaging proof of the `1+sqrt2` bound.** It keeps signed Paulis with
  expectation above `1/sqrt2` and averages every term outside their group to zero.
  A term with expectation `e` in `(0,1/sqrt2]` then loses all of `e` while
  contributing only `1-e` to the frustration. The ratio `e/(1-e)` peaks at `1+sqrt2`.
  Reaching `1/sqrt2` needs a rounding that keeps part of those terms, for example
  by extending the commuting set greedily with sign choices. The loss analysis for
  such extensions is not done.
- **Anticommutation geometry.** Expectations of pairwise anticommuting signed
  Paulis satisfy `sum e_P^2 <= 1` (Clifford algebra), which is stronger than the
  pair bound `e_P + e_Q <= sqrt2` used in the proof. A proof might round against
  this body; no argument is written.
- **Numerical evidence.** On 7500 random instances with `n<=3` and exhaustive
  stabilizer enumeration, the largest ratio observed is `0.707107`
  (`research/artifacts/pauli-stabilizer-rounding-model-test-2026-09-12.md`). This is
  evidence, not proof; small `n` and random sampling may miss worse instances.
- **Proved (sw-078, 2026-09-17): post-selection induction.** Route
  `stabilizer-rounding-constant-is-one-over-sqrt2-proof`. Take a top eigenvector
  `psi` and the term `R` whose signed expectation `M` is largest. Post-selecting
  `psi` on `A_R = +1` gives energy exactly `lambda - a/(1+M)`, where `a` is the
  anticommuting part's energy. The code space is an `(n-1)`-qubit instance of weight
  at most `W - w_R - W_A`, so induction on `n` closes once `a <= (sqrt2-1)(1+M)W_A`.
  That holds termwise: an anticommuting partner has expectation at most
  `min{M, sqrt(1-M^2)}`, which is `<= (sqrt2-1)(1+M)`, with equality only at
  `M = 1/sqrt2`. This is the greedy sign-choice extension proposed above, analysed
  through the post-selection identity instead of averaging. Cross-checks: the rounding
  on 3000 random instances with `n<=4` gave no violation; primal and dual-LP searches
  at `n<=3` peak at `0.7071068` (`experiments/stabilizer-rounding-constant-2026-09-17/`).
  Consequences: factor `1+1/sqrt2` for Pauli-projector and code-space Hamiltonians,
  NP at `b > (1+1/sqrt2)a`, and the Natarajan--Nirkhe window becomes
  `1 < p/q <= 1+1/sqrt2`.

**Referee check (2026-09-17, ref-04).** SOUND; no error found, no status change.
Re-derived every step of `stabilizer-rounding-constant-is-one-over-sqrt2-proof`:
(R1) `+wI` shifts both sides by `w`, and `-wI` shifts the right side by
`-w-w/sqrt2`, against `-w` on the left, so it only
weakens the claim; (R2) merging uses that the right side decreases in `W`; (F1) from
`(aA+bB)^2=(a^2+b^2)I`, which also bounds negative `x_Q`; (F2) both branches, using
`(1-t)/sqrt2=t` and `(1-t^2)/(1+t^2)=cos(pi/4)`. In Step 2, `(I+A_R)K(I+A_R)=2(I+A_R)K_c`
checks termwise, `A_R K_A` is anti-Hermitian, and `<psi|A_R K|psi>=lambda M`, so (2)
holds. In Step 3, `U A_Q U^*` for `Q` in `C` is `+-B_Q tensor I` or `+-B_Q tensor Z`,
with `B_Q=I` excluded (it would give `A_Q=+-I` or `A_Q=+-A_R`; the proof names only the
second, and (R1) excludes the first); `K'` has weight at most `sum_C w_Q`, and
`U^*(phi' tensor |0>)` is a stabilizer state. The Step 4 algebra expands to
`(1+c)lambda-cW+[cW_A-(1+c)a/(1+M)]`, and `(1+c)t=c`. `n=0` and `K'=0` are covered. The
sharpness example `(X+Z)/2` gives `stab=1/2=(1+c)lambda-cW`. Consequences: Pauli
projectors and code projectors have weight one (identity term included), so the factor
`1+1/sqrt2` follows. The NP verifiers need only a rational threshold strictly between
the two sides. For games inputs with `W<=1`, monotonicity in `W` gives `p>(1+1/sqrt2)q`.
The root bound `a>=(2-sqrt2)(b-V)` and relative gap `<=sqrt2-1` are correct arithmetic.
"Fail at or below" for witnesses is shown by one instance and its averaged copies; it
is not a hardness claim, as the node says. Independent computations
(`experiments/stabilizer-rounding-constant-2026-09-17/referee_ref04_*`, no shared code):
exact stabilizer enumeration by Clifford-gate closure (6, 60, 1080, 36720 states), and a
search over random dense, sparse and `+-1` sums, magic-state Pauli-vector families and
Nelder--Mead restarts at `n=1..4` (3000/3000/3000/900 random, 200/200/300/60 restarts).
The maximum ratio is `0.7071067812` at every `n`, with no violation, and is attained by
several non-trivial supports. A step checker on 4000 random instances (`n<=4`) confirms
(F1), (1), (2), (3), `lambda' >= lambda-a/(1+M)-w_R`, and that each compressed commuting
term is a signed non-identity Pauli, to `1e-14`. Literature (bounded web search): product-state
results (Bravyi--Gosset--König--Temme, JMP 60 (2019) 032203; Lieb's `lambda_max/9`;
Gharibian--Parekh) are multiplicative bounds for traceless local Hamiltonians. Recent
stabilizer-ground-state papers (arXiv:2403.08441, arXiv:2603.06286) and quantum norm
designs (arXiv:2509.11979) state no additive 1-norm frustration bound. No prior
statement of (SR*) or its constant was found; no priority claim. Remaining caveats: this
is an ordinary proof with one referee and no Lean check, and the rounding is
existential (it uses a top eigenvector), so no efficient algorithm is claimed.

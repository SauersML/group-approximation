# EX review 2, dynamics: part 2. ex-sl3z-cocompact-quotient

Lane `ex-verify2-dynamics`, tip `6dd68ce8d`. Commits under review: 5dea6f786f, a5893bd6f5, 4301977864,
e48aab9bfa, 324b0eede3 and 9544c83e55. None of these claims had a first-wave review. The artifacts are
`sl3z-cocompact-quotient-microstates-2026-09-13.md` and `sl3z-cocompact-quotient-holonomy-drift-2026-09-13.md`
(with its `-part2`).

| claim | verdict |
|---|---|
| `benoist-quint-zariski-dense-invariant-measures-are-haar` (+ `-citation`) | PASS, verbatim against the preprint (p. 2) |
| `sl3z-cocompact-quotient-uniquely-ergodic-minimal` (+ `-proof`) | PASS |
| `uniquely-ergodic-action-sofic-iff-topological-microstates` (+ `-proof`; artifact §3) | PASS |
| `sl3-norm-drift-excludes-finite-almost-invariant-configs` (+ `-proof`) | PASS |
| `sl3z-cocompact-microstates-carry-flat-lambda-labels` (+ `-proof`) | PASS |
| `bms-sln-z-representations-agree-with-algebraic-ones` (+ `-citation`) | PASS, verbatim against the Numdam scan (pp. 60, 95, 134, 135) |
| `sl3z-cocompact-quotient-uniformly-far-from-finite-actions` (+ `-proof`) | PASS after a GAP (wording) in step 2, now corrected in the route and in part 2 of the artifact |
| `hecke-orbits-make-lattice-quotient-actions-sofic` (+ `-proof`) | PASS |
| routes `sl3z-cocompact-quotient-nonsofic-from-no-microstates` and `sl3z-cocompact-nonsofic-from-stability-and-no-finite-approx` | PASS as implications. Their premises are open, so neither route fires |
| `sl3z-on-cocompact-lattice-quotient-is-not-sofic` and the other open nodes | OPEN at `6dd68ce8d`, and labelled OPEN. No false establishment |

## 2.1 Benoist–Quint import: PASS

The preprint was read from Benoist's homepage (`09stationnaire.pdf`, the copy on MSI in lane
`ex-sl3z-cocompact-quotient`).
- *Page 2.* Corollaire 1.2 (a), (b) and (c) match the route verbatim.
- *Zariski-density convention.* "lorsque G n'est pas linéaire : cela signifie que l'image Ad(Γ) est Zariski
  dense dans le groupe adjoint Ad(G)". This matches.
- *Point (c).* It is weak convergence of `ν_n = (1/#X_n) Σ δ_x` to Haar measure on `X`.
- *Not re-read.* The definition of "quasi-simple" on p. 1 (simple Lie algebra). The journal version was not
  compared.

## 2.2 Minimality and unique ergodicity: PASS

- *Zariski density.* A polynomial vanishing on `u_ij(Z)` vanishes on `u_ij(R)`, and these subgroups generate `SL_3(R)`.
- *No finite orbit.* `u_12(n)` in the finite-index stabilizer gives `w = g^(−1)u_12(n)g ∈ Λ ∖ {1}`. With
  `a_t = diag(e^(−t), e^t, 1)`, `a_t u_12(n) a_t^(−1) = u_12(ne^(−2t)) → 1`. Writing `a_tg = f_tλ_t` with `f_t`
  in a compact set gives `λ_twλ_t^(−1) → 1` in the discrete `Λ ∖ {1}`, which is impossible.
- *Atoms.* The atoms of maximal mass form a finite invariant set. So an invariant measure is atom-free, and
  Corollaire 1.2(a) applies.
- *Minimality.* Orbit closures are infinite, closed and invariant, so Corollaire 1.2(b) applies.

## 2.3 The microstate criterion: PASS

- **(i).** `(M1)` comes from the trace of `u_su_tu_(st)^*`.
- **(M2).**
  - If `d(sx_p, x_q) >= ε`, then `sp ∩ q = ∅`, because `diam(sp) <= ω_s(2/m)` and `diam q <= 2/m`.
  - So these pairs have `μ(q ∩ sp) = 0`, and each has model fraction `< ε'`.
  - There are at most `|P_m|^2` pairs, which gives `(M2)`.
  - Every atom of a partition is nonempty, so `x_p` exists. The artifact's "empty atom" clause is vacuous.
- **(ii), Step A.** Bijectivity of `σ_k(s)` and `(M2)` give `|∫f∘s dν_k − ∫f dν_k| <= ω_f(ε_k) + 2||f||ε_k`.
  Limit points are invariant, so `ν_k → μ` by uniqueness.
- **(ii), Steps B–C.**
  - *Factorization.* The trace factorizes over `V_k × W_k`.
  - *Nontrivial group part.* The sofic approximation `τ_k` kills the group factor.
  - *Trivial group part.* Iterated `(M1)` and `(M2)` put the marks within `η_k` of the translates. The error is
    at most `2mε_k + ν_k(N_(η_k))`.
  - *Continuity sets.* By Portmanteau for closed sets, `limsup ν_k(N_η) <= μ(N_η) → μ(∂) = 0`. The translated
    atoms are continuity sets because the `s` are measure-preserving homeomorphisms.
  - Lemma LC (PASS in dynamics part 1, §2.2) concludes.
- **Dependencies.** Both requirements are established: `paunescu-sofic-action-class-permanence` (Definition 1.4;
  part 3 here, verbatim) and `sofic-action-with-sofic-ergodic-components-is-sofic`.

## 2.4 Norm drift: PASS

- *Reduction.* `u = xw/||x||` gives `||sx|| >= ||x||·||su||`.
- *Pairs.* `||u ± u_je_i||^2 = 1 ± 2u_iu_j + a`, so the product is `(1+a)^2 − 4ab`. Using `b <= 1 − a`, this is
  at least `1 − 2a + 5a^2`, whose discriminant is negative.
- *Concavity.* On `b_1 + b_2 = 1 − a` the minimum is at an endpoint. That gives
  `f(a) = log((1 − 2a + 5a^2)(1+a)^2) = log(1 + 2a^2 + 8a^3 + 5a^4)`, which is increasing and `>= 0`.
- *The constant.* `Σ_s log||su|| = (1/2)Σ_j (pair sums) >= (1/2)f(max_j a_j) >= (1/2)f(1/3)`, and
  `f(1/3) = log((81 + 18 + 24 + 5)/81) = log(128/81)`.
- *Summation.* `Σ_ωΣ_s[N(τ_sω) − N(ω)] = 0`, and the split gives `κ <= 12(η + θB)`.
- *Metric form.* `e = Φ(τ_sω)(sΦ(ω))^(−1)` and `||sΦ|| <= ||e^(−1)||·||e sΦ||`.

## 2.5 Flat labels: PASS

Artifact part 1, §§1–2.
- *Existence.* `d̄(xΛ, yΛ) = min_λ d(x, yλ)` is attained, since `Λ` is discrete.
- *Uniqueness.* `d(xλ, xλ') = d(xμx^(−1), 1)` with `μ = λλ'^(−1)`, and conjugation by `K` distorts by at most
  `C_1`. So `d(μ,1) <= 2C_1ε < r_Λ`.
- *Flatness.* `g_(v_m) = E·(s_m···s_1)·g_(v_0)·λ_1···λ_m`, with `E = Π p_ie_ip_i^(−1)` and
  `d(E,1) <= mC_1ε` by right-invariance. So `λ_1···λ_m = g^(−1)E^(−1)g` lies within `LC_1^2ε < r_Λ` of `1`.
  The Lipschitz range is respected because `ε_0 <= 1` and `LC_1ε <= r_Λ/(2C_1)`.
- *Definition 1.3(3).* On an honest action with every pair good, the labelled maps satisfy the relators, and the
  holonomy is a homomorphism.
- *Corollary 2.3.* Norm drift applies with `B(D_X)`, since `d(Φ(σ̃_sω), sΦ(ω)) = d̄(...) <= D_X` for a minimizing
  label, and with `η(ε)` on good pairs.

## 2.6 Bass–Milnor–Serre import: PASS

Read from the Numdam scan (`bms.pdf` on MSI; PDF page = journal page − 58).
- *p. 60, (i).* "Every subgroup of finite index contains some E_q (q ≠ 0), and E_q itself has finite index in Γ".
  Here `E_q` is "a normal subgroup E_q ⊂ Γ_q, generated by certain 'elementary' unipotent matrices".
- *p. 95, Corollary 4.3(b).* "If A is not totally imaginary then C_q = {1} for all q". This matches.
- *p. 134, (16.1).* a) `π(Γ̂)` is open in `G_(A^f)`. b) `ker(π)` is finite. The text adds: "these conditions depend
  only on G over Q, and not on the choice of Γ".
- *p. 135, Theorem 16.2.* Verbatim as quoted.
- *Unipotents.* The conclusion that `f` sends unipotents to unipotents follows because algebraic homomorphisms
  preserve Jordan decompositions.

## 2.7 Uniform exclusion (Theorem E): PASS after a corrected wording GAP

**The argument.**
- Holonomy gives `ρ_v : Γ_v → Λ`.
- BMS 16.2 applies to `ι∘ρ_v` and gives algebraic `F = ι∘ρ_v` on a finite-index `Γ'`.
- Unipotents of `Γ'` map to unipotent elements of `ι(Λ)`, hence to `1`.

**GAP (wording).** The route and the artifact said that the `e_ij^N` in `Γ'` "generate `E_3(Z,N)`, which has finite
index". The subgroup they generate need not be normal, so it is not BMS's `E_q`. The conclusion survives with a
one-line repair.
- By BMS (i), `Γ'` contains some `E_q`.
- `E_q` is generated by `SL_3(Z)`-conjugates of elementary matrices congruent to `1` mod `q`, all unipotent and all
  in `Γ'`.
- So `ρ_v(E_q) = 1`, and `ker ρ_v` has finite index.

Corrected forward in `sl3z-cocompact-quotient-uniformly-far-from-finite-actions-proof`, step 2, and in part 2 of the
artifact, §3.

**Also clarified in the route.** "Their union `O` is finite" now reads "the union of the orbits through `V × {1}`",
as in the artifact.
- Each orbit is finite, since stabilizers have finite index.
- `O` is invariant and has no bad pairs.
- Corollary 2.3 gives the contradiction.

**Hypothesis (R).** It is model-tested.
- *`SL_3(Z)` fails it.* It contains unipotents.
- *`SL_1(O_D)` satisfies it.* Left multiplication by `x` is unipotent only if `(x − 1)^9 = 0` in the division
  algebra, which forces `x = 1`.

## 2.8 Hecke orbits: PASS

- *Hypotheses.* Corollaire 1.2(c) applies to every Zariski-dense subgroup: a subgroup is a sub-semigroup, and
  Zariski density is taken through `Ad` for non-linear `G`.
- *Criterion.* `finite-equidistributed-orbits-give-sofic-action` (PASS in dynamics part 3, §8b) needs exactly
  weak convergence of the normalized counting measures on finite invariant sets.
- *Instance 1, infinitely many orbits.*
  - `chΓ_2 = c'hΓ_2` iff `c^(−1)c' ∈ Δ = hΓ_2h^(−1)`, so `|P| = [C : C ∩ Δ]`.
  - If `P` were finite, then `Γ_1 ∩ Δ <= C ∩ Δ <= Δ` with `[Δ : Γ_1 ∩ Δ] < ∞` would force `[C : Γ_1] < ∞`.
- *"Where it stops".* Pairs from different commensurability classes have no finite orbits at all. This agrees with
  §2.2.
- *Scope nits.* These need no fix.
  - Instance 3 should use the identity component `SO_0(n,1)`.
  - Commensurator density and Margulis' criterion are recalled there, not imported.

## 2.9 Firing check

- **At `6dd68ce8d`, OPEN:** `sl3z-on-cocompact-lattice-quotient-is-not-sofic`,
  `sl3z-cocompact-quotient-admits-no-topological-microstates`,
  `sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions`, `sl3z-is-stable-in-finite-actions`,
  `mixing-free-nonsofic-action-of-sofic-group` and `simple-group-lattice-admits-nonsofic-action`.
- **`...-nonsofic-from-no-microstates`.** A valid implication by part (i) of the criterion.
- **`...-nonsofic-from-stability-and-no-finite-approx`.** A valid implication.
  - Diagonal amplification by finite quotients `q_k`, injective on `F_k`, gives a sofic approximation.
  - The Loeb factor map pushes to Haar measure by Step A.
  - Weak containment in finite actions passes to factors.
- **What the lane proves.** Theorem E excludes honest finite models with no defects. Nonsoficity needs the
  defect-tolerant version, and the nodes say so.

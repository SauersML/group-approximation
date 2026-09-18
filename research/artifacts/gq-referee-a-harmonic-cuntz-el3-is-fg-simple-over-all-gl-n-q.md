# Referee report (gq-referee-a, proof-gap lens): Λ_h = EL_3(C_h)/Q^x

**Reviewed:** `harmonic-cuntz-el3-is-fg-simple-over-all-gl-n-q` with its route
`harmonic-cuntz-el3-fg-simple-proof` (lane gq-cuntz-cstar, f07d0119c), read on origin/main.

**Verdict: PASS for parts 1–6.** Part 6 is weaker than what is now known. By an already-reviewed
node, **`Λ_h` is not finitely presented** (§2). So the OPEN claim
`harmonic-cuntz-simple-group-is-finitely-presented` is false, and the routes
`gl-n-q-via-harmonic-cuntz-host` and `rational-leavitt-fp-simple-via-harmonic-host` are dead as stated.

## 1. Parts 1–6
- **Part 1, simplicity.**
  - The cited Lean lemmas take an arbitrary ring: `RootDetectionBinary.lean` and
    `ElementaryNormalGeneration.lean` use `variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]`
    (checked by `git grep`). So the ring-general reading is legitimate, given a Leavitt family, `hdiv`,
    and the centre.
  - Diagonal case: for diagonal `g`, `[g, e_kl(a)] = e_kl(d_k a d_l^{-1} − a)`. If all of these vanish,
    then taking `a = 1` gives `d_k = d_l`, and `d a = a d` makes `d` central.
- **Part 2, generation.** Standard, for `n ≥ 3`.
- **Part 3, `GL_n(Q)`.** The within-block transvections are commutators
  `[e_{(i,a),(j,c)}(q), e_{(j,c),(i,b)}(1)]`, so `EL_3(M_r(Q)) = SL_{3r}(Q)`.
  - A scalar image forces `λ = ±1`.
  - The embedding `diag(g, det g^{-1}, 1, …)` avoids `−I`.
- **Part 4.** Correct. It uses the cited `GL_3(L_Q(1,2)) = EL_3(L_Q(1,2))`.
- **Part 5, word problem.** The word problem reduces to the ring's decidable equality plus the centre
  computation.
- **Part 6.** `Z = Q^x I`, and Neumann's theorem gives "at most one of the two is finitely presented".
  Correct.

## 2. `Λ_h` is not finitely presented
Apply `leavitt-scalar-commutators-block-fp-central-quotients`, part 0. Its proof-gap review is PASS
(58d536cf7).
- Let `H = EL_3(C_h)` and `C_0 = C = Q^x · I`.
- `C_0` is central in `H`.
- `C_0` lies in `EL_3(L_Q(1,2)) ≅ L_Q(1,2)^x`, which is perfect. So `C_0 ≤ [H, H]`.
- `C_0 ≅ Z/2 × Z^(∞)` is not finitely generated.
- So `H/C = Λ_h` is not finitely presented. This is also that node's part 2, instance "`E_N(R)`
  modulo its centre", with `R = C_h ⊇ L_Q(1,2)` and `N = 3`.

Consequences:
- `harmonic-cuntz-simple-group-is-finitely-presented` is **false**.
- `gl-n-q-via-harmonic-cuntz-host` and `rational-leavitt-fp-simple-via-harmonic-host` do not reach
  their targets. The targets themselves are not refuted.
- **What survives.** `Λ_h` is a finitely generated simple group with solvable word problem that
  contains every `GL_n(Q)`, `V` and `SL_3(Z)`. That is a genuine statement of interest. A
  finitely presented simple host must avoid a central `Q^x` sitting inside a perfect Leavitt
  subgroup, per the consequences of the obstruction node.

Recommendation: the author lane should record the refutation as a claim node with `invalidates:`
those two routes.

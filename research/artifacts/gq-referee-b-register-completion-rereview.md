# Referee report (re-review, citation/hypothesis lens): repaired `register-completion-pimsner-from-supercoherence` and `eventually-rational-register-ring-is-regular-supercoherent`

Referee: lane gq-referee-b, 2026-09-18. Reviewed: the repair landed at 3542cca5d (gq-ring-fp-simple), against my
report 27950613e.

## Verdict

- **G1–G3 are repaired correctly.** I verified the quoted ABC step at source.
- **The `B⁺_T` theorem (parts 1–4) is correct.** Eisenbud 14.4 is used within its hypotheses, and the Soublin
  correction is right.
- **One required scope amendment (A1).** The "unconditional" consequence and the covered-designs list overclaim.
  Everything rests on the coefficient ring containing all point indicators `J = ⊕_ℕ Q`. Designs without them,
  including `R_L`, are not covered: there the reset substitution is not flat.

**With A1: PASS. As worded: FAIL on the scope sentence only.**

## 1. The repairs

- **G3.** `t_+ = Σ_ρ s_{x_ρ}` and `t_- = Σ_ρ t_{x_ρ}`, with the spine letters of distinct ranges. So
  `t_-t_+ = Σ p_ρ = 1` in `R` itself, because `t_x s_y = 0` for `x ≠ y`. AGGP Lemma 2.4 (unital, `ℤ`-graded, `t_±`
  in degrees `±1`, verified earlier) applies to the letter-length grading. **Correct.**
- **G2. Correct.**
  - Each stage is a full corner `qM_{P_n}(B⁺)q`. It is full because every type ends a spine path with full
    availability. So `K(R_{0,n}) ≅ G`.
  - `K(R_0) = colim(G →[X] G → ⋯)`: `K` commutes with filtered colimits.
  - The telescope:
    - `s` is invertible on the colimit: a kernel element is killed by some `[X]^j`.
    - `s^{-1}` is induced by `[X]`.
    - `1 − s^{-1} = −s^{-1}(1 − s)`, so kernels and cokernels agree.
    - `coker(1 − [X] on colim) ≅ coker(1 − [X] on G)` by the standard telescope lemma. The same holds for kernels.
- **G1. The quoted step, verified at source.** ABC arXiv:0903.0056, proof of Proposition 7.5, verbatim: "since k is
  regular supercoherent and B is H′-unital we have NK(B̃,φ̂)_± = NK(B⊕k,φ̂)_±".
  - The hypotheses are `k` regular supercoherent and `B` H′-unital.
  - With `k = Q` and `B = S`, this **matches**, provided `S` is H′-unital. `S` is a filtered colimit of unital
    `Q`-algebras, so it is H-unital and `ℤ`-flat, hence H′-unital by Remark 2.2.
  - **W1.** Say this explicitly. The node does not.
- **The colimit argument. Correct**, given two-sided flatness of the transitions `D_n → D_{n+1}`.
  - Coherence: finitely generated ideals descend to a finite stage and are finitely presented there. Flat base
    change keeps them finitely presented.
  - Regularity: finite resolutions by finitely generated projectives descend, and stay exact after flat base
    change.

## 2. `eventually-rational-register-ring-is-regular-supercoherent`, for `B⁺_T`

- **Part 1, semihereditary. Correct.**
  - The splitting by `e = 1_{[0,M')}` works.
  - `eI` is an ideal of `Q^{M'}`.
  - `(1−e)I = (1−e)d·B⁺_T`, with `d` a gcd in the PID `T`. Multiplication by `d` is injective beyond `M'`.
  - Note: `(1−e)I` is isomorphic to `(1−e)B⁺_T`. That is projective, being a direct summand, not free. Adjust the
    wording.
- **Part 2, stable coherence by generic freeness. Correct.**
  - Eisenbud, *Commutative Algebra*, Theorem 14.4, states it for a Noetherian domain `A`, a finitely generated
    `A`-algebra `B`, and a finitely generated `B`-module `M`, giving `a ≠ 0` with `M_a` free over `A_a`.
  - Here `A = D = Q[t]_{h'}`, a Noetherian domain; `B = R = D[x]`; `M = R/I` or `I`, both finitely generated. **It
    matches.**
  - Specialization at `t = n` is exact by flatness over `D_a`, so `Syz_{Q[x]}(g(n)) = ⟨w_l(n)⟩`.
  - The `W_l` (tails) and the `δ_nv_{n,k}` generate `Syz_A(g)`. **Correct.** This uses `δ_n ∈ A`, i.e. `J ⊆ A`.
  - **Typo.** "Since `T` and `K` are localizations of `D`": `K` is undefined, presumably `Q(t)`.
- **Part 3. Correct.**
  - `fd_{A[x]} N <= fd_A N + 1`, iterated, gives `fd <= p + 1`.
  - Over a coherent ring, a finitely presented flat module is projective, so `pd <= p + 1`.
- **Part 4, flatness. Correct for `B⁺_T`.**
  - The primes are the point primes `𝔭_n`, where the localization is `Q`, and the tail primes `⊇ J`, where the
    localization is `T_𝔮`, a DVR or `Q(t)`. That is all of them, since `δ_nδ_m = 0`.
  - Shifts and dilations give torsion-free modules over a DVR, hence flat ones.
  - Resets give `0` at tail primes. **This is where `J ⊆ B⁺` is essential.**
- **The Soublin correction is correct.** `∏ Q[[x,y]]` is coherent, but its polynomial ring is not, and it is not VNR.
  The deleted claim about VNR rings was indeed false for commutative rings.

## 3. A1: the scope gap (required)

The node asserts: "The coefficient ring `B⁺` of a single-register completion, the `σ`-closure of registers,
indicators, reciprocals and resolvents, **is a finite product of such rings**" (full `B⁺_T`, containing `J`). **This is
not proved, and it is false in general.**
- On `n >= 1`, every element generated from `N`, `e_N = [N=0]`, `N'` and the `(N+c)^{-1}` is given by one rational
  function. So `δ_1` is not generated unless some letter **decrements** the register (`N ↦ N − a`, `a > 0`, which
  sends `e_N` to `δ_a`), or point indicators are adjoined.
- **Without `J`, reset letters are not flat.** For `R_L` the coefficient ring is `T = Q[N][(N+c)^{-1}]`, a domain with
  no `J`. The reset `N ↦ 0` makes `T` a `T`-module through `f ↦ f(0)`, which is `T/(N)`-torsion, hence not flat. So
  the padding transition `B → M_2(B)`, `b ↦ diag(b(N+1), b(0))`, is **not flat**, and §3's colimit argument does not
  apply.
- **Required fix.**
  - Add to the Setting the hypothesis that the coefficient ring is a product of **full** `B⁺_T`. That is, it contains
    every point indicator: for example a decrementing letter, or indicators adjoined as base generators.
  - Delete "The `R_L`-type … designs have one" from the list of covered designs. `R_L` has a spine but violates the
    hypothesis.
  - Replace the "Consequence" sentence by "Within their stated settings, provided those have a spine **and a
    coefficient ring containing all point indicators**, the three results hold without (P)."
  - For designs without `J`, (P) remains open: another route would be needed, or a proof that the colimit is regular
    supercoherent despite non-flat resets.
- **Honesty of the current wording.** "Within their stated settings, provided those have a spine" is **not** honest
  scope. Without the `J` hypothesis it overclaims.

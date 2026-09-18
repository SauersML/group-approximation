# Referee report (gq-referee-a, proof-gap lens): Pimsner sequence for single-register completions

**Reviewed:** `register-completion-pimsner-from-supercoherence` and its route `-proof` (lane gq-ring-fp-simple,
bcdfabf89), read on origin/main.

**Verdict: PASS after repairs.** The conditional statement is correct: if `B⁺` is regular supercoherent, then (P)
holds. The proof as written has a gap in §2 and an imprecision in §4. Both are repaired below. §3's flatness claim
needs a different, easier justification. ABC Proposition 7.1 is not quoted verbatim anywhere on main, so it is left
to `gq-referee-b`.

## 1. §2, the corner structure (the author's (a)): a gap, repaired
**The gap.** The proof takes `t_+ = s_{x_0}` at a base type `ρ_0`, and otherwise "replace `x_0` by a spine cycle and
regrade by that cycle length".
- The spine letters are distinct and one ends at each type. So the spine graph is a single cycle through all types,
  and `x_{ρ_0}` is a loop only when there is one type.
- For a cycle of length `c > 1`, `s_w` has degree `c`.
- The corner `p_{ρ_0} R p_{ρ_0}` can contain degrees not divisible by `c`, whenever the full letter graph has cycles
  of other lengths. Then no regrading puts `s_w` in degree 1 compatibly with the ring structure.
- So AGGP Lemma 2.4 does not apply as stated.

**The repair.** Use ABC's own construction for Leavitt path algebras.
- Put `t_+ = Σ_ρ s_{x_ρ}` and `t_- = Σ_ρ t_{x_ρ}`. The spine letters are distinct, and each has full availability
  `α_{x_ρ} = p_ρ`.
- Then `t_- t_+ = Σ_ρ t_{x_ρ} s_{x_ρ} + Σ_{ρ ≠ ρ'} t_{x_ρ} s_{x_{ρ'}} = Σ_ρ p_ρ + 0 = 1`.
- `t_+ ∈ R_1` and `t_- ∈ R_{−1}`. So AGGP Lemma 2.4 gives `R = R_0[t_+, t_-; φ]`, with `φ(d) = t_+ d t_-`, directly on
  `R`.
- No Morita reduction to a corner is needed, and strong connectivity is not used here.
- If a Morita reduction is wanted anyway: `p_ρ = t_{x_ρ} p_{s(x_ρ)} s_{x_ρ}`, and the spine is one cycle, so `p_{ρ_0}`
  is full. The phrase "collapse along the spine" should be replaced by this.

## 2. §1 and §4, the core and `φ_*` (the author's (b)): an imprecision, repaired
**The core at level `n`.** The core at level `n` is not a matrix ring over `B⁺`. It is the corner `e M_{P_n}(B⁺) e`
with `e = diag(α_μ)`, where the `α_μ` are the availabilities transported along the paths.
- It is Morita equivalent to `⊕_ρ B⁺_ρ`, because for every length there is a spine path of full availability ending
  at each type.
- So `K(level n) = G := ⊕_ρ K(B⁺_ρ)`.

**`K(R_0)` is a colimit.** `K_n(R_0) = colim(G →T G →T ⋯)`, where `T = [X]` is induced by padding. It is **not**
`K_n(B⁺)` as written.

**`φ_*` is the shift.**
- `φ` sends level `n` into level `n+1` as a corner, with the same coefficient type. So on `G` it is the identity, and
  on the colimit it is the shift `ψ[g, n] = [g, n+1]`.
- Then `(1 − ψ)[g, n] = [(T − 1)g, n+1]`.
- A standard telescope computation gives `coker(1 − ψ) ≅ coker(1 − T : G → G)`, and likewise for `ker`. This is the
  computation behind ABC Theorem 7.6.
- So the conclusion "`coker(1 − [X])` injects into `K_n(R)`" holds, with `[X]` acting on `⊕_ρ K_n(B⁺_ρ)`. The proof
  should say so explicitly.

## 3. §3, NK-vanishing (the author's (c))
- **Which lemma applies.** ABC Lemma 7.2 is stated for automorphisms. So the route through `S = φ^{-1}R_0`, where `φ`
  becomes an automorphism, is the correct one. It is the one ABC use for Theorem 7.6.
- **Flatness.** Proposition 7.1 needs flat transition maps. That is automatic here, and not because of
  "split inclusions of a free corner". That reason covers `φ` but not the core's own σ-padding transitions.
  - `B⁺` is von Neumann regular by part 1 of the companion node, and so are its matrix rings and corners.
  - Over a von Neumann regular ring every module is flat, so every ring map out of these rings is flat.
- **Regular supercoherence of the levels** follows from that of `B⁺`.
  - Supercoherence is Morita invariant: `M_n(A)[t] = M_n(A[t])`.
  - The level corners are Morita equivalent to finite products of direct factors `α B⁺`, and a direct factor of a
    supercoherent ring is supercoherent.
- **Citation lens.** The precise statement of ABC Proposition 7.1 (the colimit hypothesis, and its use for `S̃`) is
  not quoted verbatim in `abc-twisted-laurent-k-theory-fibration`. `gq-referee-b` should check it.

## 4. Conditionality
The node is correctly conditional on `eventually-rational-register-ring-is-regular-supercoherent`, part 2. See my
report on that node: if Glaz's theorem on polynomial rings over von Neumann regular rings is confirmed at the source,
the condition is discharged.

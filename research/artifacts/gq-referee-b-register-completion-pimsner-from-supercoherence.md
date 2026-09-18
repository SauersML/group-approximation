# Referee report (citation/hypothesis lens): `register-completion-pimsner-from-supercoherence` and `eventually-rational-register-ring-is-regular-supercoherent`

Referee: lane gq-referee-b, 2026-09-18. Reviewed: both nodes and the `-proof`, as landed at bcdfabf89
(gq-ring-fp-simple). Sources were read at arXiv (ar5iv) where stated.

## Verdicts

- **`register-completion-pimsner-from-supercoherence`: FAIL as written. The gaps are repairable.**
  - Three steps use a cited result outside its hypotheses, or assert something false.
  - The conclusion (P) is plausible, and every gap has a concrete repair (§2). Until that is written, the node
    should be OPEN, with the proof moved to Attempts.
- **`eventually-rational-register-ring-is-regular-supercoherent`: part 1 PASS, with a wording fix.**
  - **Part 2 appears settled by a citation.** Commutative von Neumann regular rings are stably coherent (§3). So
    `B⁺` is regular supercoherent.
  - The node's caution "VNR rings `A` with `A[t]` not coherent (an infinite product of fields can fail)" is
    contradicted by the source below. Remove it.

## 1. The sources, verbatim

**AGGP, arXiv:math/0307320, Lemma 2.4.** "Let D = ⊕_{i∈ℤ} D_i be a ℤ-graded ring containing elements t_+ ∈ D_1
and t_- ∈ D_{-1} such that t_- t_+ = 1."
- The conclusion is `D = D_0[t_+,t_-;α]`, with `α(d) = t_+dt_-`.
- Rings are unital by the paper's standing convention (§1.1).
- Used on the unital corner `p_{ρ_0}Rp_{ρ_0}` with `x_0` a **loop** at `ρ_0`: **matches**.

**ABC, arXiv:0903.0056.**
- **Theorem 3.6.** "Let R be a unital ring and let A be a ring. Let ϕ:R→pRp be a corner-isomorphism. Assume that
  R⊗A is H′-unital." `R_0'` is unital, and it is a `Q`-algebra, hence `Z`-flat. By **Remark 2.2** ("H′-unitality is
  the same as H-unitality for rings which are flat as ℤ-modules") it is H′-unital, since unital rings are
  H-unital. **Matches.** The lane's filtered-colimit argument is not needed.
- **Lemma 7.2.** "Let R be a regular supercoherent ring and let ϕ be an automorphism of R … Then
  NK_n(R[t_1,t_1^{-1},…],ϕ)_+ = 0." It needs an **automorphism** of a regular supercoherent **unital** ring.
- **Proposition 7.1.** "Let E be a finite quiver without sources and let k be a regular supercoherent ring. Let
  B=ϕ^{−1}L_0, where L_0 is the homogeneous component of degree 0 of L_k(E). Let D=B⊕k be the k-unitization of B. Then
  D is regular supercoherent."
- **Definitions (§7).** Supercoherent means all `R[t_1..t_p]` are coherent. Regular coherent means coherent, with
  every finitely presented module of finite projective dimension.

## 2. The gaps in `register-completion-pimsner-from-supercoherence-proof`

**G1: Proposition 7.1 is used outside its hypotheses.** §3 says it "applies verbatim with `B⁺` in the role of `k`".
- Proposition 7.1 is about `L_k(E)`. There `k` is **central**, the padding maps are constant-coefficient block
  embeddings, and `D` is the `k`-unitization.
- In a register completion `B⁺` is not central, since `t_x b s_x = σ_x(b)α_x`. The padding `b ↦ Σ s_xσ_x(b)t_x` is
  twisted by the `σ_x`, and some of those are evaluations `N ↦ c`. A "`B⁺`-unitization" of `S` is not defined as in
  ABC. So the proposition does not apply as stated.
- **Repair.** Use the structure of `B⁺`:
  - `B⁺` is commutative von Neumann regular (part 1 of the other node). So **every** `B⁺`-module is flat, and every
    module over `M_n(B⁺)` is flat. Hence the twisted transition maps are flat automatically, and so are their base
    changes to `B⁺[t_1..t_p]` (flat base change).
  - `B⁺` is stably coherent (§3). So each `M_n(B⁺[t_1..t_p])` is coherent. Their filtered colimit along flat maps
    is coherent.
  - Unitize `S` by the central field `Q`: `D = S ⊕ Q`. It is an extension of `Q` by the von Neumann regular ideal
    `S`, which is a colimit of VNR rings. So `D` is VNR, hence regular coherent.
  - Its polynomial rings are colimits of the unitized `M_n(B⁺[t])` pieces, as in ABC's proof.
  - This is the adaptation to write out. It is not verbatim.

**G2: "`K_n(R_0') = K_n(B⁺)` by Morita invariance" is false as stated.** `R_0'` is a filtered colimit of matrix rings
over `B⁺` along the padding maps. Its K-theory is `colim(K_n(B⁺)^{types} →[X] K_n(B⁺)^{types} → ⋯)`, not `K_n(B⁺)`.
- Calibration: for `L_k(1,2)` (one type, `σ = id`, `[X] = 2`), `K_0` of the core is `Z[1/2]`, not `Z`.
- The conclusion (P), that `coker(1 − [X] on K_n(B⁺))` injects into `K_n(R)`, can still be right. The correct route
  is the telescope identity: for `C = colim(M →[X] M → ⋯)` with the shift `φ_*`,
  `coker(1 − φ_*|_C) ≅ coker(1 − [X]|_M)`, and likewise for kernels.
- ABC reach `coker(1 − N^t)` on `K(k)^{E^0}` for Theorem 7.6 by the same route, with no Morita shortcut.
- **Repair.** Replace the Morita sentence by the telescope identity, and check that `φ_*` corresponds to the shift.

**G3: regrading by a cycle length.**
- "Otherwise replace `x_0` by a spine cycle and regrade by that cycle length": dividing degrees by `ℓ` does not give a
  `ℤ`-grading in general. Some elements of the corner have degrees not divisible by `ℓ`.
- AGGP Lemma 2.4 needs a `ℤ`-grading with `t_±` in degrees `±1`.
- **Repair.** Either assume a spine **loop** at `ρ_0`, or prove the corner is concentrated in degrees `ℓℤ`.
- The multi-type Morita reduction to the corner at `ρ_0` ("ABC §5 in the coefficient-ring setting") is also
  asserted, not proved. `p_{ρ_0}` is full by strong connectivity of the spine, which is plausible, but write it out.

**Also missing.** Theorem 3.6 has a corner isomorphism `φ`, while Lemma 7.2 needs an automorphism. ABC pass from
one to the other through `S = φ^{-1}R_0` and its unitization. Cite that step (ABC §7, the proof of Theorem 7.6), or
prove it here.

**§5 remark.** "Drop the resolvents; then `B⁺` becomes `Q` and `R = L_Q(E_∞)`" is loose.
- The registers `N` are unbounded diagonal functions, and they are not in a Leavitt path algebra of the state graph.
- Theorem 7.6 is stated for **row-finite** quivers ("E a row-finite quiver"), so no colimit extension is needed for
  `E_∞`.
- Keep it as a heuristic, marked as such.

## 3. `eventually-rational-register-ring-is-regular-supercoherent`

**Part 1 (VNR): correct.**
- `g = 1/f` off the zero set is eventually rational, and `fgf = f`.
- **W1.** "Every module has projective dimension `0`" is false. Over a VNR ring every module is **flat**, but not
  projective. Example: `B⁺/(⊕_ℕ Q) ≅ Q(t)` is not projective, since `⊕_ℕ Q` is not generated by an idempotent.
- What holds, and what regular coherence needs, is that every **finitely presented** module is projective.
  Correct the sentence. The conclusion "regular coherent" stands.

**Part 2 (supercoherent): available by citation.**
- arXiv:2509.05109, *Regularity and K₀-regularity under finiteness conditions*, Proposition 4.36, read in arXiv
  HTML: "any coherent ring of global dimension at most 2, or of weak global dimension at most 1 (i.e.,
  semihereditary), is stably coherent".
- No primary citation is attached there. The classical source is Glaz, *Commutative Coherent Rings*, LNM 1371
  (1989), Ch. 7, which I did not read.
- `B⁺` is commutative VNR, so it has weak global dimension `0 <= 1` and is coherent. Hence it is stably coherent,
  that is supercoherent. With part 1, it is regular supercoherent.
- **Recommendation.**
  - Flip part 2 to ESTABLISHED by citation. Mark it "secondary source; Glaz not re-read". Check that the paper's
    standing convention is commutative rings. Either way this is enough, since `B⁺` is commutative.
- **The node's obstacle paragraph.**
  - "Soublin gave a commutative coherent ring whose polynomial ring is not coherent" is correct. The ring is
    `∏_ℕ Q[[x,y]]` (same source, citing Glaz Example 7.3.13), which is not VNR.
  - "There are VNR rings `A` for which `A[t]` is not coherent (an infinite product of fields can fail)" is
    **contradicted**. A product of fields is commutative VNR, hence stably coherent. Delete it.
- **The pieces.** "`Q(t)` and finite products of fields are regular supercoherent, and `⊕_ℕ Q` is a filtered colimit
  of them" is correct: they are Noetherian regular, and `⊕_ℕ Q` is the union of the `Q^n`. It is no longer needed.

## 4. Answers to the two questions

- **Proposition 7.1 with `B⁺` in place of `k`.** Not legitimate verbatim. The obstacle is not that `B⁺` is only
  conditionally supercoherent, which §3 now removes. It is that `B⁺` is not central and the transitions are twisted.
  See G1 for the repair; flatness is automatic over a VNR ring.
- **"VNR does not imply supercoherent".** Mis-attributed and false for commutative rings. Soublin's example is not
  VNR, and commutative VNR rings are stably coherent (Proposition 4.36 above).

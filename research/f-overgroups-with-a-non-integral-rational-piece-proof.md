---
rg: 2
id: f-overgroups-with-a-non-integral-rational-piece-proof
kind: route
title: A congruence-subgroup drag moves every irrational into the interior piece, the commensurator identity turns the piece into a global Moebius map on the relation, and Smith normal form plus the end-germ density argument finish
target: f-overgroups-with-a-non-integral-rational-piece-are-nonamenable
requires:
  - thompson-f-co-amenable-hosts-have-integral-end-germs
  - co-amenable-subgroups-transfer-hyperfinite-orbit-relations
  - thompson-f-interval-orbit-relation-is-hyperfinite
  - lodha-moore-breakpoint-orbit-is-hereditarily-amenable-not-ea
---

**Imports.** Everything is imported from `thompson-f-co-amenable-hosts-have-integral-end-germs-proof`
(ESTABLISHED), cited by step name:
- *Step 0 there.* For `x ∉ Q` and `γ ∈ PSL_2(Z)` there is `f ∈ F` with `f = γ` near `x`. Hence
  `Fx = PSL_2(Z)x` for `x ∈ R \ Q`.
- *Lemma D there.* A piecewise-`PSL_2(Z)` homeomorphism with rational breakpoints is `C^1`.
- *Lemma C there.* Countable reduction of co-amenability.
- *Step 3 there, the density half.* It uses only a translation `τ_h(t) = t + h` with `0 < h < 1`
  together with `PSL_2(Z)`: the Shimizu iteration starts at `ξ_0 = [[0,−1],[1,0]]`, and the Lie algebra
  step uses `U = τ_1` and `[[1,0],[1,1]]`. So it proves that `⟨PSL_2(Z), τ_h⟩` is dense in `PSL_2(R)`
  for every such `h`.
- *Step A there.* `R_L` is `λ`-hyperfinite for every `L ≤ F`.
- *Step 4 there.* A transfer argument through
  `co-amenable-subgroups-transfer-hyperfinite-orbit-relations`.

Two verbatim Lodha–Moore lines (arXiv:1308.4250, `vN_fp.tex`), quoted in that route:
- l.304–306, Carrière–Ghys: "If $\Gamma$ is a countable dense subgroup of $\PSL_2(\Rbb)$, then the
  action of $\Gamma$ on the real projective line induces an orbit equivalence relation which is not
  amenable with respect to Lebesgue measure."
- l.271–272: "the elements of $F$ correspond exactly to those homeomorphisms $f$ of $\Rbb$ which are
  piecewise $\PSL_2(\Zbb)$ and which have continuous derivatives."

**Notation.**
- `ℓ ∈ PGL_2^+(Q) \ PSL_2(Z)` is represented by a primitive integer matrix `L`, meaning its entries
  have gcd 1, with `D = det L`. `D ≥ 2`: if `D = 1` then `L ∈ SL_2(Z)`, which is excluded.
- In `PSL_2(R)`, `ℓ` is `L/√D`.
- `Γ(D) = {δ ∈ SL_2(Z) : δ ≡ I mod D}` is the principal congruence subgroup. It is normal in
  `SL_2(Z)`, because it is the kernel of reduction mod `D`.

**Lemma K (commensurator identity).** If `δ ∈ Γ(D)`, then `L δ L^{−1} ∈ SL_2(Z)`.

*Proof.* Write `δ = I + DM` with `M ∈ M_2(Z)`. Since `L^{−1} = adj(L)/D`,
`L δ L^{−1} = I + D·L M L^{−1} = I + L M adj(L)`. This is an integer matrix, and its determinant is
`det δ = 1`. ∎ (Checked exactly in `commensurator_drag.py`, check 1.)

**Lemma S (a short translation).** `⟨PSL_2(Z), ℓ⟩` contains `τ_{1/D}`.

*Proof.*
- Smith normal form over `Z` gives `U_0 L V_0 = diag(d_1, d_2)` with `U_0, V_0 ∈ GL_2(Z)` and
  `d_1 | d_2`. Here `d_1` is the gcd of the entries, so `d_1 = 1`, and `d_2 = D`.
- If `det U_0 = −1`, replace `U_0` by `diag(1,−1)U_0`, and treat `V_0` the same way. The results
  `U, V ∈ SL_2(Z)` give `U L V = diag(ε_1, ε_2 D)` with `ε_i = ±1`.
- Its determinant is `D > 0`, so `ε_1 = ε_2`. Projectively, `μ = U ℓ V` is `t ↦ t/D`, and it lies in
  `⟨PSL_2(Z), ℓ⟩`.
- Then `μ τ_1 μ^{−1}(t) = μ(Dt + 1) = t + 1/D`. ∎ (Check 2.)

**Step 1 (the congruence drag).** Let `G ⊇ F` and `g ∈ G` with `g = ℓ` on a nonempty open interval
`J`. Then `ℓy ∈ Gy` and `ℓ^{−1}y ∈ Gy` for every `y ∈ R \ Q`.

*Proof.*
- `g` is real-valued on `J`, so the pole of `ℓ` is not in `J`. Pick a rational `r = u/v ∈ J` in lowest
  terms. Bezout gives `γ ∈ SL_2(Z)` with first column `(u, v)`, so `γ(∞) = r`.
- Put `δ_n = γ τ_{Dn} γ^{−1}`. Since `τ_D ∈ Γ(D)` and `Γ(D)` is normal, `δ_n ∈ Γ(D)`.
- For irrational `y`, the point `x = γ^{−1}y` is a finite irrational. Then `δ_n y = γ(x + Dn) → γ(∞) = r`
  as `n → ∞`, by continuity of `γ` on `P^1`. Fix `n` with `δ := δ_n` satisfying `δy ∈ J`. (Check 3.)
- *Chain.*
  - `δy ∈ Fy`, by Step 0, since `y ∉ Q`.
  - `g(δy) = ℓδy`, since `δy ∈ J`.
  - `ℓδy = (ℓδℓ^{−1})(ℓy)` with `ℓδℓ^{−1} ∈ PSL_2(Z)` by Lemma K. Also `ℓy ∉ Q`, since
    `ℓ ∈ PGL_2(Q)`. So `ℓδy ∈ F(ℓy)` by Step 0.
  - Hence `ℓy ∈ Gy`.
- For the inverse, apply this to `z = ℓ^{−1}y`, which is irrational: `ℓz = y ∈ Gz`, so `ℓ^{−1}y ∈ Gy`. ∎

*This is where the end-germ route stalled.* That route's closing paragraph says that for an interior
piece the pseudogroup yields only `λγ` with `γx ∈ I`, and "not `λ` itself". Lemma K supplies the
missing step: choosing `γ = δ` in the congruence subgroup lets `ℓ` pass through `δ` at the cost of the
integral element `ℓδℓ^{−1}`, which `F` absorbs.

**Step 2 (the relation of `Γ = ⟨PSL_2(Z), ℓ⟩` sits inside that of `G`).**
- `Γ ≤ PGL_2(Q)` preserves `Q ∪ {∞}`, so `Y = R \ Q` is `Γ`-invariant and conull.
- For `y ∈ Y` and a word `μ_1 ⋯ μ_n` with each `μ_i ∈ PSL_2(Z) ∪ {ℓ^{±1}}`, every intermediate point lies
  in `Y`. Each letter moves it within its `G`-orbit: by Step 0 for `PSL_2(Z)`, and by Step 1 for `ℓ^{±1}`.
- By induction, `Γy ⊆ Gy` for all `y ∈ Y`. This is the same induction as Step 2 of the end-germ route.

**Step 3 (`Γ` is dense; its relation is not amenable).**
- By Lemma S, `Γ ⊇ Γ_h := ⟨PSL_2(Z), τ_h⟩` with `h = 1/D ∈ (0, 1)`.
- By the density half of Step 3 of the end-germ route, `Γ_h` is dense in `PSL_2(R)`. Hence so is `Γ`.
- `Γ` is countable. By Carrière–Ghys, `R_Γ` on `P^1` is not `λ`-amenable, and so it is not
  `λ`-hyperfinite (Connes–Feldman–Weiss, used exactly as in the end-germ route's trust surface).

**Step 4 (part 1).** Let `G` be as in part 1, and suppose a countable `L_0 ≤ G` with `λ`-hyperfinite
`R_{L_0}` is co-amenable in `G`.
- Lemma C with `C = F ∪ {g}` gives a countable `G'` with `L_0 ∪ F ∪ {g} ⊆ G' ≤ G`, in which `L_0` is
  co-amenable.
- `G'` acts on `R` by homeomorphisms that preserve `λ`-null sets. By the transfer lemma,
  `R_{G'}|_A` is hyperfinite for some Borel `A` with null complement.
- Steps 1–2 apply to `G'`, since they use only `a`, `b` (through `F`) and `g`. So
  `R_Γ|_{A∩Y} ⊆ R_{G'}|_A` is a Borel subrelation, and hence hyperfinite. This uses the subrelation
  remark after Step A of the end-germ route.
- `A ∩ Y` is conull. So `R_Γ` would be `λ`-hyperfinite, contradicting Step 3. ∎

The two named consequences:
- `L_0 = 1` is co-amenable exactly when `G` is amenable.
- Every `L_0 ≤ F` is countable, with `λ`-hyperfinite relation by Step A.

**Part 2.**
- *`G_0`.* `c = 2t/(1+t)` on `[0,1]` has primitive matrix `(2 0; 1 1)` with `D = 2` (check 4).
  `G_0 = ⟨a,b,c⟩` has finitely many Möbius pieces per element, so it preserves null sets.
- *`G_{1/2}`.* `t + 1/2` has primitive matrix `(2 1; 0 2)` with `D = 4`, and it is a global Möbius map.
  `F ≤ G_{1/2}`, because `a = (t + 1/2)^2`.
- *`⟨F, g⟩`.* The hypothesis concerns `g` only on `J`.

**Part 3.** Let `F < G ≤ PP_Q`. Suppose every piece of every element of `G` lies in `PSL_2(Z)`.
- The breakpoints are rational, and pieces in `PSL_2(Z)` map rationals to rationals. By Lemma D each
  element is `C^1`.
- It is piecewise `PSL_2(Z)`. It is increasing, since pieces in `PGL_2^+` are increasing off their
  poles.
- By l.271–272 it lies in `F`, so `G ≤ F`, a contradiction.

Hence some element has a piece `ℓ ∉ PSL_2(Z)` on an open interval, and part 1 applies: elements of
`PP_Q` have finitely many Möbius pieces, so they preserve null sets. Maximality: an amenable `G` with
`F ≤ G ≤ PP_Q` must equal `F`. ∎

**Part 4.** Let `G` be as in part 4, amenable or with some `L_0 ≤ F` co-amenable.
- *Pieces.* If some piece were outside `PSL_2(Z)`, part 1 would contradict the hypothesis. So all
  pieces lie in `PSL_2(Z)`.
- *Breakpoints.* At a breakpoint `x`, the adjacent pieces `γ_1 ≠ γ_2` agree, so `γ_1^{−1}γ_2 ≠ 1`
  fixes `x ∈ R`. A nontrivial element of `PSL_2(Z)` with a real fixed point is parabolic, with a
  rational fixed point, or hyperbolic, with real quadratic fixed points. Elliptic elements have no
  real fixed point.
- *Rational-breakpoint elements.* These lie in `F`, as in part 3.
- *Orbit relation.* Pieces in `PGL_2(Q)` preserve `Q`, and at a breakpoint the value is given by
  either adjacent piece. So `R \ Q` is invariant. For `x ∈ R \ Q`, `gx = γx` for a piece `γ` of `g` at
  `x`, so `Gx ⊆ PSL_2(Z)x = Fx ⊆ Gx` by Step 0.
- Hence `R_G = R_F` on `R \ Q`, and this relation is `λ`-hyperfinite by Step A.
- Without assuming `F ≤ G`, the same piece argument gives `Gx ⊆ Fx`, so `R_G ⊆ R_F` on `R \ Q`. This
  is a Borel subrelation, hence hyperfinite. ∎

The *blindness* statement is this equality. Every certificate built from the measured relation `R_G`
sees `R_F`, which is hyperfinite. Such certificates include:
- a non-amenable subrelation, as in Monod, Carrière–Ghys and Steps 1–3;
- a failure of the transfer lemma.
So none of them can distinguish an integral `G` from `F`.

**Consequence for `lodha-moore-breakpoint-orbit-is-hereditarily-amenable-not-ea`.** That node's item 4
states: "If so, `G_{1/2} ↷ Q` is a second calibrator of the same kind". Its premise, that `G_{1/2}` is
nonamenable, is part 2 here. It is also part 2 of the end-germ node. So `G_{1/2} ↷ Q` is a `C^1`
calibrator.

**Trust surface.**
- *Imported nodes.* Everything is inherited from the end-germ route: Step 0, Lemmas C and D, Step 3's
  density argument, Step A, and the transfer lemma together with its Zimmer and
  Connes–Feldman–Weiss imports.
- *New arguments.*
  - Lemma K, an integer identity.
  - Lemma S, Smith normal form over a PID, a textbook fact.
  - Step 1, continuity of Möbius maps on `P^1`.
  - The fixed-point classification of `PSL_2(Z)` elements via the trace, a textbook fact.
- *Checked exactly* in `experiments/thompson-f-overgroups-2026-09-17/commensurator_drag.py`: Lemma K,
  Lemma S, the drag of Step 1, and the matrices of part 2.
- *Not reviewed* by a second agent.

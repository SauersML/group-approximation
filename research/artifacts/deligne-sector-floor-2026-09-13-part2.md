# Exponents between Frobenius and normalized HS for the Deligne sector, part 2 (lane ex2-nh-deligne-sector-floor, 2026-09-13)

Continues `research/artifacts/deligne-sector-floor-2026-09-13.md`, with the same notation. Status: commentary,
unreviewed, except where a node is named.

## 4. The operator-norm side

**The conditional theorem.** `deligne-sp2g-covers-not-mf-from-operator-hs-stability` proves: if
`Gamma~_g` (`g >= 3`) is operator-HS-stable, then `Rad_MF(Gamma_n) = <z^2>` for every `n >= 3`.
- **Why the detour through the cover.** The covers `Gamma_n` fail `[T_2]`, since `H^2(Gamma_n; R) =
  H^2(Gamma; R) != 0`. BDL's remark after Conjecture 1.8 concerns l-adic Deligne extensions, which have
  `[T_2]` themselves; it does not reach the real covers.
- **The route.** Round `phi(z^2)` to exact order `m`, cut out a nontrivial eigenprojection (asymptotically
  central because `z^2` is central and the spectrum is separated), compress (BDL Proposition 2.4,
  re-derived), compose with `Gamma~ -> Gamma_n`, round once, and apply Malcev.
- **Scope.** It works for any order `m`, and for any central extension whose top group is
  operator-HS-stable and whose finite residual contains `z^2`.

**Kazhdan splitting of an operator-norm model of `Gamma~`.**
- **The finite-dimensional part rounds.** Property (T) makes every finite-dimensional irreducible `sigma`
  isolated, so there is a minimal central projection `p_sigma in C^*(Gamma~)` with
  `p_sigma C^*(Gamma~) = M_(dim sigma)`. A model gives a `*`-homomorphism into the norm corona. The image of
  `p_sigma` lifts to asymptotically central projections, and `M_n` is semiprojective. So on finitely many
  isotypic pieces the model is operator-close to genuine representations.
- **The remainder is diffuse.** Its limit trace vanishes on every `p_sigma`. This is not a contradiction:
  genuine representations of unbounded dimension also have diffuse limits.
- **A necessary condition.** Every operator-norm model trace of `Gamma~` satisfies `tau(z^2) = 1`. So the
  operator twist parameters of `Sp_(2g)(Z)` all lie in `(1/2)Z/Z`.

**An attempted converse, and where it dies.** One might hope that Conjecture 1.8 for `Gamma~` follows from
two inputs:
- operator sector emptiness for all `theta` outside `(1/2)Z`, and
- operator-HS-stability of the residually finite metaplectic quotient `Gamma~/<z^2>`.

Given a model `phi` of `Gamma~`, the first input puts `phi(z^2)` HS-close to `I`, but not operator-close.
- **Square-root correction fails.** Replacing `phi(z)` by `phi(z) c(phi(z^2))`, with `c` a continuous
  square-root inverse, needs a branch cut at `-1`. The correction multiplies each relator `r~ = z^(k_r)` by
  the central unitary `c(.)^(k_r)`, which is HS-small but operator-large. So the result is no longer an
  operator-norm model.
- **Spectral projections fail.** Cutting out the eigenvalues near `-1` needs a spectral gap. In the corona,
  `phi(z^2)` may have connected spectrum with negligible trace mass away from `1`.

So the converse needs genuinely new rounding, not bookkeeping.

**Traces do not decide rounding.** Two operator-norm models with the same limit trace need not be HS-close
when the group von Neumann algebra is non-amenable. This is recalled from Jung's characterization of
amenability by conjugacy of embeddings into `R^omega`; the exact statement was not re-checked. The diffuse
part therefore needs the model, not only its character, even though character rigidity fixes the
character.

**DGLT in operator norm.**
- With operator defect `tau`, `Ad phi` is an operator-almost representation on `(M_d, HS)`. `[T_2]` gives a
  correction with `||b||_HS <= K tau`, and nothing more. After one step the operator defect is
  uncontrolled.
- **Speculative.** A Schatten-coefficient vanishing theorem with constants polynomial in `p`, used at
  `p = log d`, would give only a polylogarithmic operator floor `tau >~ 1/poly(log d)`.

## 5. Next targets and staffing

1. **Rung I1 via rank-stability (cleanest general target).** Principle to test: *a tuple for `Gamma_n` whose
   relator defects have rank at most `k` is within rank `C(k)` of a genuine representation of the same
   dimension, generator by generator.*
   - **It gives I1 at once.** A genuine `pi` has `pi(z^2) = I`, so `zeta I - pi(z)` is invertible when
     `zeta^2 != 1`. Hence `d <= C(k)`.
   - **Consistency test, trivial sector.** A finite quotient minus a point for `Sp_(2g)(Z)` is within rank
     `O(1)` of the sum-zero part of the permutation representation, through the invertible map
     `v -> v - (sum v) delta_(omega_0)`. So the principle survives the Becker--Lubotzky examples at least in
     `GL_d`, which is all that I1 needs. The unitary version was not checked.
   - **Warning over finite fields.** `kazhdan-group-rank-models-admit-no-expander-decomposition` shows that
     (T) gives no rank rounding of almost-invariant subspaces over `F_2`. Over `C` the unitary expansion
     inequality `b(W) >= kappa^2 dim W / 4` holds for genuine representations. So test over `C` first.
   - **Staffing.** One lane.
2. **Integer cosystolic filling for congruence covers (monomial row).** Hypothesis (IF) of Section 3 would give
   monomial floors `d^(-1/4)`, or dimension-free ones with bounded-entry fillings. It is the HS-row
   counterpart of the Gohla--Thom input for soficity. It is shared with sofic and Hamming lanes and may
   already be staffed there. It does not reach general tuples.
   - **Smaller task.** Verify the arithmetic-surface heuristic of Section 3: the embedding into `Gamma(m)`
     and the Toledo invariant modulo 3. That would give an explicit exponent near `3/10` for monomial models
     over `Gamma/Gamma(m)` at genus two.
3. **Operator side.** Conjecture 1.8 for `Gamma~_g` reduces, after Kazhdan splitting, to rounding diffuse
   models. That overlaps the open MF question for higher-rank lattices (`sl3z-purely-matricial-field`).
   Not a family-sized target.

Do not launch a family on `(SF1)` itself. The Schatten barrier of Section 2 shows that every known
dimension-free input stops at exponent `1/2`. A proof needs stability at growing Frobenius defect, a
supply of non-abelian independent tests, or operator control of corrections, and none of these is
available.

# Idea lane nh-qwep: Kirchberg tensor-norm separators for a non-hyperlinear group

Date: 2026-09-13. Target: `non-hyperlinear-group`.

Lens: Kirchberg's amenable-trace criterion used as a concrete norm-separation
target. This is an idea file. Nothing here is claimed established, and no Cairn
node is changed.

**Source levels.**
- **Search summaries only:**
  - Kirchberg's amenable-trace criterion, via arXiv:2206.01771;
  - Connes' injectivity criterion, via arXiv:math/9804026;
  - Kirchberg's WEP criterion, via Goldbring's QWEP notes and arXiv:1309.2034;
  - the "amenable traces" wording of Kim–Paulsen–Schafhauser.
- **Abstract fetched:** Kim–Paulsen–Schafhauser, arXiv:1707.01016.
- **Hand arguments:** the Fell-absorption and invariant-mean steps below.
- **Main nodes:** cited by id, read at origin/main 09b3b57e4.

## 0. Pinning the criterion

- **(K1)** A trace `tau` on a C*-algebra `A` is amenable iff
  `a (x) b^op -> tau(ab)` extends to a state on `A (x)_min A^op`.
- **(K2)** `Gamma = <S|R>` is hyperlinear iff the pullback of the canonical
  trace `tau_Gamma` to `C*(F_S)` is amenable. This is the Kirchberg / Connes
  embedding equivalence, taken as standard and not re-read here.
  - `C*(F_S)` has the LLP and is residually finite-dimensional.
  - So norms in `C*(F_S) (x)_min C*(F_S)^op` are suprema over pairs of
    finite-dimensional unitary representations.

The lens as first stated asked for `||sum_s u_s (x) ubar_s||_min < |S|`. That
premise is wrong, as approach 1 shows.

## Approach 1. Diagonal norm drop `||sum u_s (x) ubar_s||_min < |S|`: killed

- **Idea:** separate the canonical trace from amenable traces using the
  diagonal element alone.
- **What it would prove:** non-hyperlinearity of `Gamma` from one explicit
  norm computation.
- **Kill test, run by hand:**
  - **Full algebra:** the trivial representation of `F_S` or `Gamma` gives
    the value `|S|`, so the min norm is always at least `|S|`. No drop is
    possible in `C*(Gamma)` or in the pullback.
  - **Reduced algebra:**
    - By Fell absorption, the norm of `sum lambda_s (x) lambdabar_s` equals
      `||sum lambda_s||`. That is `< |S|` iff `Gamma` is nonamenable (Kesten),
      whatever the hyperlinearity of `Gamma`.
    - A hypertrace on `B(l^2 Gamma)` that is central for `lambda(Gamma)`
      restricts to an invariant mean on `l^infinity(Gamma)`, because
      `lambda_g M_f lambda_g^* = M_(g.f)`.
    - So `tau_Gamma` is amenable on `C*_r(Gamma)` only when `Gamma` is
      amenable.
  - **"= n for all unitaries":** this is Connes' injectivity criterion for
    finite factors. It detects injectivity, not embeddability in `R^omega`.
- **Verdict: killed.** The informative object is the pullback pairing of
  (K2), with signed off-diagonal coefficients.

## Approach 2. Equality-matrix separator on `C*(F_S) (x)_min C*(F_S)^op`: survives as reformulation, killed as a certificate route

- **Idea:**
  - Let `G_L(w,w') = 1[w = w' in Gamma]` for words of length at most `L`.
  - By (K1) and (K2), `Gamma` is non-hyperlinear iff for some `L` and some
    signed finitely supported `c`:

    ```text
    sum_(w,w') c_(w,w') G_L(w,w')  >  sup_(d, pi, sigma : F_S -> U(d))
                                        || sum c_(w,w') pi(w) (x) sigmabar(w') ||.   (EQ1)
    ```

  - The left side is the canonical pairing, realized as the vector state
    `delta_e` of the commuting left/right regular pair.
  - Signed coefficients defeat the trivial representation, e.g. penalty terms
    `-N (u_a (x) 1 + 1 (x) ubar_a)/2` on words `a != e` in `Gamma`.
- **What it would prove:** an explicit non-hyperlinear group, certified by
  one inequality on one ball.
- **Kill test, by reading nodes and source levels:**
  - A certificate for (EQ1) is an upper bound on a supremum over all
    matrix sizes that fails for the commuting regular pair.
  - `global-tracial-positivity-cannot-separate-group-trace` (ESTABLISHED)
    forbids certificates valid in every tracial von Neumann algebra.
  - Outer SDP-type hierarchies bound commuting-operator values, which
    dominate the left side, so they cannot certify (EQ1) either.
  - Main also shows fixed-form defect/trace inequalities for the Higman
    relators already fail in dimension three: `higman-qutrit-coefficient-bound`
    refutes coefficient 16, while `higman-u2-bound` proves coefficient 2 on
    U(2).
- **Verdict: exact reformulation only.**
  - Any separator must be matricial-only and non-uniform in form.
  - Nothing computable from above is available.

## Approach 3. The von Neumann-level tensor `C*(F) (x)_min L(Gamma)^op` vs `(x)_max`: killed (it detects WEP, not CEP)

- **Idea:** separate at the von Neumann level, where rapid-decay and
  operator-valued Haagerup inequalities give dimension-free upper bounds on
  min norms that are *not* valid for commuting pairs. That would escape the
  tracial wall of approach 2.
- **What it would prove:** non-hyperlinearity through explicit spectral
  bounds on `M_d(C*_r(Gamma))`.
- **Kill test, hand computation:**
  - Take `x = sum_s u_s (x) (lambda_(s^-1))^op`. The standard pair
    `(lambda o q, rho)` gives `<x delta_e, delta_e> = |S|`, so
    `||x||_max >= |S|`.
  - The spatial min norm is `sup_pi ||sum pi(s) (x) rho_(q(s))||`, which is
    `||sum Ind_N^F(pi|_N)(s)||` with `N = ker q`.
  - For `Gamma = F_2` (`N = 1`), Fell absorption gives `||sum lambda_s|| = 2 sqrt 3 < 4`.
  - So min differs from max even for the hyperlinear group `F_2`. This is
    consistent with Kirchberg's WEP criterion (`A` has WEP iff
    `A (x)_min C*(F_inf) = A (x)_max C*(F_inf)`) and non-injectivity of
    `L(F_2)`.
- **Verdict: killed.** Rapid-decay-type certificates live on this completion,
  so they certify non-injectivity, not non-embeddability. The CEP completion
  keeps `C*(F)` on both sides.

## Approach 4. Intermediate completions `C*_pi(G)`, `C*_D(G)` with `lambda <= pi`: killed as detectors

- **Idea:** look for min-continuity failures of the canonical pairing on
  exotic completions between the reduced and full algebras. There min norms
  might be more computable.
- **What it would prove:** the same as approach 2, on a friendlier algebra.
- **Kill test, repo node:**
  - `llp-regular-dominating-completion-forces-nonhyperlinear` records
    Paulsen–Rahaman–Samei Theorem 4.9: if `G` is nonamenable and the
    completion is proper, `C*(G) != C*_D(G)`, then `C*_D(G)` has no amenable
    trace.
  - The failure is therefore automatic for every nonamenable `G`. It carries
    information only when combined with a lifting property (LLP) back towards
    `C*(F_S)`.
  - That is exactly the LLP route already on main (Theorem 4.6 contraposed).
- **Verdict: killed** as an independent route. It reduces to the existing
  LLP nodes.

## Approach 5. Synchronous-correlation translation (Kim–Paulsen–Schafhauser): duplicate

- **Idea:**
  - Synchronous quantum approximate correlations correspond to amenable
    traces on game algebras. KPS give new characterisations of synchronous
    qa correlations and a new equivalence of Connes' embedding problem
    (arXiv:1707.01016 abstract; "amenable traces" per search summary).
  - For a linear-system solution group `Gamma` with central `J`, the
    regular-trace `J = -1` corner gives a synchronous `qc` correlation.
  - If that correlation lies outside `C_qa^s`, `Gamma` is non-hyperlinear.
- **Kill test, repo nodes:**
  - Main already has explicit rational separations: `p_tab in C_qc \ C_qa`
    (`lin-pzk-tableau-rational-qc-not-qa-correlation`) and the JNVWY game
    `G^sep` (`explicit-commuting-operator-separating-game`).
  - Both come from BCS traces, not group traces. The missing step is the
    open hole `non-ru-bcs-is-satisfiable-in-a-group-factor`, a different lens.
  - The natural Slofstra negative corners are already sofic:
    `slofstra-natural-negative-corner-image-is-sofic` (ESTABLISHED no-go).
- **Verdict: duplicate** of the groupification route.

## What this lens settles

1. **The one informative Kirchberg completion** for hyperlinearity is the
   pullback `C*(F_S) (x)_min C*(F_S)^op`, used with signed off-diagonal
   equality-matrix coefficients (EQ1).
2. **Three tempting completions** detect amenability or injectivity instead:
   - the diagonal norm on the full or reduced algebra (Kesten, Connes);
   - `C*(F) (x) L(Gamma)^op` (WEP);
   - proper exotic completions (Paulsen–Rahaman–Samei Theorem 4.9).
   Dimension-free spectral bounds, such as rapid-decay inequalities, only
   reach those completions.
3. **Separators for (EQ1)** must be matricial-only. Main's tracial wall and
   the Higman dimension-three counterexample fence the natural fixed-form
   candidates.

## Sources

- arXiv:2206.01771 (search summary): the amenable-trace min-tensor criterion.
- arXiv:math/9804026 (search summary): Connes' injectivity criterion.
- arXiv:1707.01016 (abstract): Kim–Paulsen–Schafhauser.
- arXiv:1309.2034 and Goldbring's QWEP notes (search summaries): Kirchberg's
  WEP criterion.
- Main nodes: `global-tracial-positivity-cannot-separate-group-trace`,
  `llp-regular-dominating-completion-forces-nonhyperlinear`,
  `lin-pzk-tableau-rational-qc-not-qa-correlation`,
  `explicit-commuting-operator-separating-game`,
  `slofstra-natural-negative-corner-image-is-sofic`,
  artifacts `higman-qutrit-coefficient-bound.md` and `higman-u2-bound.md`.

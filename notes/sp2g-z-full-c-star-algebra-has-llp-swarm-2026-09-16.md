# Swarm attack on `sp2g-z-full-c-star-algebra-has-llp` (2026-09-16)

Agent: swarm-sp2g-z-full-c-star-algebra-has.  Hole locked: the target itself.

## 0. Orientation

State on arrival (read from the graph):

- `symplectic-llp-positive-case-is-sp4`: only `g = 2` can be positive.
- `sp4-llp-failure-or-maslov-nonhyperlinear-extension`: LLP for
  `C^*(Sp_4(Z))` forces a nonhyperlinear finite Deligne cover.
- Scalar ISW Theorem A is dead on every subgroup of `Sp_4(Z)`
  (`isw-theorem-a-has-no-data-on-sp4-lattice`, finite-index version).
- The standard ISW affine group `Z^2 x| F` does not embed
  (`sp4-contains-no-isw-affine-subgroup`).
- The Theorem C mouth reduces to CE of Maslov-twisted group factors
  (`sp4-small-maslov-twisted-group-factors-are-ce`).

Unexplored before this session: permanence of LLP to QUOTIENTS by central
subgroups, applied to the Klingen parabolic, whose integral radical has a central
`Z` with quotient the ISW group `Z^2 x| SL_2(Z)`.

## 1. Literature gate (2026-09-16)

- **No fresh search.**  The WebSearch budget was exhausted for this session and
  the arXiv API returned HTTP 429, so no fresh 2024–2026 keyword sweep was
  possible.
- **What was read, from TeX source.**
  - Farah–Fritz–Winter, arXiv:2603.18456v2 (April 2026).  Line 266: "It seems to
    be open whether higher rank arithmetic groups always fail the (L)LP."  This
    is the most recent dated record found; it treats the question as open.  Also
    read: Proposition `c ext struct` (Packer–Raeburn fibres), Corollary `c ext`
    (all fibres LLP implies LLP), and Question `q:cocycles`.
  - Ioana–Spaas–Wiersma, arXiv:2006.01874: Theorem A, Corollary B, Remark
    `hereditary`, Theorem `NPS` (line 552, for arbitrary projective
    representations), the proof of Corollary B (cocycle `c = xt - yz`, twists
    `c_k`), and Claim `gap` in the second proof of Theorem A (lines 694–729).
- **Unverified pointers, used only through ISW's citations.**  NPS07 Lemma 1.1;
  Pisier 2020 Proposition 3.5; Kirchberg 1993 and Ozawa 2004 Corollary 3.17
  (Kirchberg's criterion).
- **Not searched.**  Theorem 3 below, in its crossed-product form: failure of the
  LLP for full crossed products of rotation algebras by `SL_2(Z)`.  No novelty is
  claimed.  A referee with search access should check for prior statements.
- **The root.**  No published result settling it was found in these sources.

## 2. Setup: the Klingen extension is ISW's central extension

Basis `(e1, e2, f1, f2)`, `J = [[0,I],[-I,0]]`, and:

```text
N(v,c) = I + X_v + cZ,   X_v(x) = omega(v,x) e1 + omega(e1,x) v,   Z(x) = omega(e1,x) e1,
L(g) = g on span(e2,f2), identity on e1, f1.
```

The script `experiments/sp2g-z-full-c-star-algebra-has-llp-2026-09-16/klingen_structure.py`
verifies:

- symplecticity;
- `N(v,c) N(w,d) = N(v+w, c+d+omega(v,w))`;
- `L(g) N(v,0) L(g)^{-1} = N(gv, 0)`;
- the centre is fixed by `L`;
- the order of `z mod k` is `k`.

**Consequences.**

- `E = {N(v,c) L(g)} <= Sp_4(Z)` is exactly `Z x_c Lambda`, where
  `Lambda = Z^2 x| SL_2(Z)` and `c((v,g),(w,h)) = omega(v, g w)`.  This is ISW's
  cocycle from the proof of Corollary B.
- **Correction.**  The integral radical has commutator `N(0,2)`.  It is
  `H_omega`, an index-two overgroup of `H_3(Z)`, not `H_3(Z)` as labelled in two
  existing nodes.  Their conclusions do not visibly depend on this.
- **Fibres.**  `A_t = C^*(Lambda, exp(2 pi i t c)) = C^*(E)/<u_z - e^{2 pi i t}>`.

## 3. What was proven (full proofs in `research/artifacts/klingen-central-quotient-2026-09-16.md`)

- **Theorem 1 / 1'** (`klingen-central-quotient-is-min-inexact`).
  - Statement: for EVERY `t in R`, `0 -> I_t -> C^*(E) -> A_t -> 0` is not exact
    after `(x)_min B(l^2)`, and `q_t` is not locally split.
  - Witness: ISW's gap element lifted to `C^*(E)`, with blocks
    `pi_n = rho_n(0, .)`.  Here the `rho_n` are genuine representations of `E`
    with `rho_n(z) = e^{2 pi i s_n}`, and `s_n -> t` are rationals with
    `0 < |s_n - t| < 1/2`.
  - Upper bound: the image has min-norm at most `D < m`, by Claim `gap`
    applied to cocycle `sigma_{t - s_n}`.
  - Lower bound: the distance to `I_t (x)_min B` is at least `m`, via the corona
    map `(rho_n (x) ev_n)_n` and the maximally entangled vector.
- **Theorem 3** (`klingen-twisted-fibres-all-fail-llp`).  For EVERY `t in R`, the
  fibre `A_t` fails the LLP.
  - This is ISW's second proof of Theorem A, with approximating cocycles
    `sigma_{s_n} -> sigma_t` instead of `-> 1`.
  - The min bound is as above.  For the max bound, `x -> [(pi_n(x) (x) 1)_n]` is
    an exact `sigma_t`-representation in the corona.
  - Crossed-product form: the full crossed product of the rotation algebra
    `A_{2t}` by `SL_2(Z)` fails the LLP, for all `t`, including irrational `t`.
- **Theorem 2** (`klingen-rational-twisted-fibres-fail-llp`).  At rational
  `t = p/q`, `A_t` contains `C^*(Lambda)` as the range of a ucp conditional
  expectation.  The twist is trivial on `qZ^2 x| SL_2(Z)`, and the bimodular
  group expectation descends to the fibre.
- **Lemma A.**  LLP passes to `A/I` when the sequence is min-exact against
  `B(l^2)`.
- **Lemma B.**  Local ucp splitting implies min-exactness.
- **Remark R1.**  Fibrewise LLP criterion for `C(X)`-algebras.
- **Corollary 1.2.**  The lifted ISW witness has max = min = `m` on `C^*(E)`.

**Development during the session.**

- The first draft had only `t = 0` for Theorem 1 and only rational `t` for the
  fibres (Theorem 2), with irrational fibres open.
- Re-reading ISW's Theorem `NPS` (stated for arbitrary projective
  representations) showed that Claim `gap` applies to `sigma_{t - s_n}` for any
  `t`.  This gave Theorems 1' and 3.

## 4. Approaches and where each dies

1. **Disproof via central quotient.**
   - The idea: `C^*(Sp_4(Z))` has the LLP, so `C^*(E)` has it, so `A_t` has it by
     Lemma A.  This contradicts Theorem 3.
   - It dies at Lemma A's hypothesis (EX), which fails unconditionally at every
     `t` (Theorem 1').
2. **Disproof via an ISW-type witness on `C^*(E)` directly.**
   - It dies at Corollary 1.2: witnesses built from `sigma_s`-projective blocks
     extend to genuine representations of `E`, so max = min for them.
   - A disproof would need cocycles on `Lambda` or `E` not of the form `sigma_s`.
   - The graph already closes scalar Theorem A on subgroups of `Sp_4(Z)`
     (`isw-theorem-a-has-no-data-on-sp4-lattice`,
     `isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals`).
3. **Proof of the root via FFW Corollary `c ext` on the Klingen extension.**
   - It dies at Theorem 3: every fibre fails the LLP.
4. **Positive direction in general.**
   - Nothing proved.
   - If the root is true, then by Lemma A, Theorem 3 and R1:
     - every central quotient of `C^*(E)` is min-inexact, which holds by
       Theorem 1', so this is no contradiction;
     - at every point of `T`, the fibrewise min norms of some `y` fail upper
       semicontinuity (norm inflow from neighbouring fibres).
   - This constrains the root but does not refute it.

## 5. Open directions noticed

- **Is `C^*(E)` itself LLP?**  `E = H_omega x| SL_2(Z)`.  Every fibre fails, every
  quotient is inexact, and lifted ISW witnesses self-compensate.
  - A decisive witness on `C^*(E)` must mix fibres in a way not captured by
    genuine finite-dimensional representations of `E`.
  - Does `(E, H_omega)` have relative (T)?  If it does, then H^2-type data on
    `H_omega` not of the form `sigma_s` would be the missing ingredient.
  - **Unchecked sketch that it does.**
    - Put `z` in the Kazhdan set.  An almost invariant vector then has small
      spectral mass for `pi(z)` away from `1`.
    - On the spectral part where `e^{2 pi i s}` has `0 < |s| < 1/2`, Claim `gap`
      holds uniformly.  This is the C(T)-algebra form: for `f` supported there,
      `||f(u_z) sum_i u_{g_i}|| <= ||f||_inf D`.
    - On `ker(pi(z) - 1)` the representation factors through `Lambda`.  Relative
      (T) of `(Lambda, Z^2)` then gives `Z^2`-invariant, hence
      `H_omega`-invariant, vectors.
    - The fibre at `z = -1` (`s = 1/2`) is not covered by Claim `gap`: there
      `sigma_{1/2}` is a coboundary on `Z^2`.  It is reached only through the
      mass bound.
    - Not written out.  Measurable disintegration and the epsilon bookkeeping are
      unchecked.
    - If it holds, then `C^*(E) = C^*(SL_2(Z)) (+) (1 - p) C^*(E)`, with `p` the
      central Kazhdan-type projection.  The LLP of `C^*(E)` would then reduce to
      the LLP of the ideal `(1 - p) C^*(E)`.  That the projection exists in
      `C^*(E)` for a normal subgroup pair is also unchecked.
- **Maslov cocycle on `E`.**  How does the graph's Maslov cocycle `b` on
  `Sp_4(Z)` restrict to `E`?  Not computed.

## 6. Files

- `research/artifacts/klingen-central-quotient-2026-09-16.md` (proofs)
- `research/klingen-central-quotient-is-min-inexact.md` and its route
  `research/klingen-central-quotient-min-inexact-proof.md`
- `research/klingen-twisted-fibres-all-fail-llp.md` and its route
  `research/klingen-twisted-fibres-all-fail-llp-proof.md`
- `research/klingen-rational-twisted-fibres-fail-llp.md` and its route
  `research/klingen-rational-twisted-fibres-fail-llp-proof.md`
- `experiments/sp2g-z-full-c-star-algebra-has-llp-2026-09-16/klingen_structure.py`

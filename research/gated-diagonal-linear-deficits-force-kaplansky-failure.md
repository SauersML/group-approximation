---
rg: 2
id: gated-diagonal-linear-deficits-force-kaplansky-failure
kind: claim
title: A pointer-gated diagonal linear Bernoulli deficit beyond its pointer needs a one-sided unit in F_q[G], so it exists only where Rokhlin entropy already collapses
distinct_from:
  cancellative-incidence-patterns-do-not-force-domination: that builds one shared-pointer parity gadget in a finite loop and shows by a zero-divisor identity that no group realizes that pattern; this bounds every gated monomial-diagonal code on every incidence pattern of every group with directly finite F_q[<E ∪ F>], and names uniqueness of inverses as the step the loop escapes.
  homomorphic-codes-cannot-compress-bernoulli-shifts: that excludes codes that are homomorphisms of the whole input; this handles codes that are nonlinear through a pointer and linear only in the value coordinates, and separates the deficit into a pointer part and a group-ring part.
  rokhlin-window-transport-is-dominated: that is condition (D) for all configurations, equivalent to Rokhlin maximality; this proves (D) for one structured class of codes on directly finite hosts and says what a counterexample in the class must be.
  pointer-gated-linear-codes-are-rank-dominated: that is the open rank inequality E d <= E r for gated linear codes with arbitrary matrices; this proves it for monomial-diagonal gating over directly finite group rings.
artifacts:
  - research/artifacts/pointer-gated-linear-witness-direct-finiteness-2026-09-17.md
---

**Setting.** Let `G` be a countable group, `q` a prime power, and `(k, E, F, psi)` a configuration as in
`bernoulli-rokhlin-deficit-has-a-finitary-witness`. Write `gap(psi) = I(x(1); y_F) - H(y_1)`, so that
`Phi < log q` iff `gap(psi) > 0`.

A code is **pointer-linear** if:
- the coordinates split into pointer bits `p` and value bits `v ∈ F_q^{k_V}`;
- `psi(x|_E) = (J(p|_E), L_J(v|_E))`, with `J` arbitrary and each `L_j` linear.

A pointer-linear code is **gated monomial-diagonal** if there are fixed `T_i ∈ F_q[G]` such that:
- on pointer value `j`, `L_j` outputs `γ_{i,j} h_{i,j} T_i` on coordinate `i` for `i ∈ I_j`, and
  nothing else;
- the functional `Σ_e c_e v_i(fe)` at codeword `f` is identified with `f T` in `F_q[G]`;
- `γ ∈ F_q^×` and `h ∈ G`.

The shared-pointer parity gadget (`T_i = Σ_{e ∈ E_val} e`) and the pointer star (`T_i = e_0`) are
examples, after the pointer and value bits are split.

**Claim (Theorem 1, Theorem 3, Proposition 5 and Corollaries 4 and 6 of the artifact).**

1. **Exact split, every incidence pattern.**

       gap(psi) = gap(J) + log q · ( E d(J_F) - E r(J_1) ),

   where:
   - `gap(J) = I(p(1); J_F) - H(J_1)`;
   - `d(j_F) = dim(row P_1 ∩ row L(j_F))` counts the value dimensions at site 1 recovered by the
     gated linear outputs;
   - `r(j) = rank L_j`.
2. **Direct finiteness.** Let `psi` be gated monomial-diagonal and suppose `F_q[<E ∪ F>]` is directly
   finite.
   - Then `P(d_i = 1) <= P(i ∈ I_{J_1})` for each coordinate. Hence `E d <= E r` and
     `gap(psi) <= gap(J)`.
   - Proof: a recovering combination is a left inverse of `T_i`. Direct finiteness makes it the unique
     inverse `T_i^{-1}`, independent of the pointers. Its support must lie in the active codewords, and
     stationarity bounds that probability by `P(i ∈ I_{J_1})`.
3. **Explicit Kaplansky pair.** Over any group, if `gap(psi) > gap(J)`, then some `T_i` supported in
   `E` has a left inverse supported in `F E E^{-1}` that is not a right inverse.
4. **Abelian homomorphic pointers.** If `J` is a homomorphism for a finite abelian group structure on
   the pointer alphabet, then `gap(J) <= 0` on every pattern, by characters evaluated on constants.
   So:
   - if `F_q[<E ∪ F>]` is directly finite, the configuration satisfies (D);
   - if it violates (D), `F_q[G]` is not directly finite. By
     `infinite-rokhlin-supremum-forces-surjunctivity` (Seward, Corollary 4.1),
     `h^Rok_sup(G) < infinity`, so `rho_{q'}(G) = 0` for every `q'`.

**Consequences.**

* **The class dies.** The class of pointer-gated monomial-diagonal codes with abelian homomorphic
  pointers contains the star and parity-gadget recipes with split coordinates. It can never give the
  first evidence of a Rokhlin deficit.
  - **Invariant:** direct finiteness of `F_q[<E ∪ F>]`.
  - **Step where every member dies:** uniqueness of the left inverse of `T_i`.
  - It dies on every incidence pattern of groups linear sofic over `F_q`
    (`linear-sofic-group-algebra-is-stably-finite`) and of Higman's group and its subgroups
    (`higman-group-algebras-embed-in-division-rings`).
  - On the binary Leavitt unit group, a deficit in the class is a Kaplansky counterexample.
* **Calibration.** In the finite loop of the firewall, the split parity gadget has `gap(J) <= 0`,
  `E r = 1` and `E d ≈ 3.87` at `t = 2`, with `Phi <= 0.855` bits. So `E d <= E r` fails for abstract
  cancellative patterns, and associativity enters exactly through uniqueness of inverses.
* **Where it stops.** The proof does not cover gated linear codes that mix coordinates or output
  several functionals per coordinate. Left inverses of columns are not unique, and the trace
  substitute only computes `dim` mod `p`. That case is the OPEN
  `pointer-gated-linear-codes-are-rank-dominated`, which holds over finite groups by counting.

**ESTABLISHED 2026-09-17** by [[gated-diagonal-linear-deficits-force-kaplansky-failure-proof]].
Not yet independently re-derived.

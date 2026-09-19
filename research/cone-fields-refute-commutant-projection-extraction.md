---
rg: 2
id: cone-fields-refute-commutant-projection-extraction
kind: claim
title: A cone field over O2 gives a corner-invisible central unitary at distance 2 from 1, refuting commutant projection extraction for groups without (T)
distinct_from:
  commutant-projection-extraction: that asserts a corner-invisible central unitary is trivial for every countable group; this is a counterexample to it, at H = Z x F_4, and so shows the residual hole needs group input.
  corona-corner-detection-criterion: that proves the corner-invisibility hypothesis for Kazhdan compression squares and leaves open whether it forces triviality; this shows that corner-invisibility by itself, even in its strongest form (a unique trace on C*(Theta(H))), does not force triviality.
  hs-invisibility-inflation-no-go: that says a corner is mandatory because HS-invisibility of the mark alone gives nothing; this goes further, showing that invisibility in every corner of the relative commutant also gives nothing without a group hypothesis.
  bounded-rank-corners-excluded: that excludes bounded-rank detecting corners for perfect Kazhdan sources; this excludes detecting corners of every rank, but only for a non-Kazhdan source.
  presentation-defect-does-not-control-off-commutant-mass: that is a no-go for conditional-expectation transfer of presentation defect onto a commutant; this is a no-go for extracting a spectral projection of a central unitary from the relative commutant.
  normal-kazhdan-defect-non-mf: that is the positive case where the mark lies in a normal (T) subgroup; this is the negative case where the only (T)-free input is centrality, and it keeps the positive case as the surviving form (Remark K).
---

**ESTABLISHED** (proposed; referee pending) through
`cone-fields-refute-commutant-projection-extraction-proof`.  Imports,
quoted from N. Brown, *On quasidiagonal C\*-algebras* (arXiv
math/0008181):

- Theorem 13.1 (Voiculescu, Duke Math. J. 62 (1991) 267–271): "Let A and B
  be homotopic C\*-algebras. Then A is QD if and only if B is QD."  Example
  3.16: "the cone (CA = C₀((0,1]) ⊗ A) and suspension (SA = C₀((0,1)) ⊗ A)
  over any C\*-algebra A are QD."
- Theorem 4.2 (Voiculescu): A is QD iff for each finite `F ⊂ A` and `ε > 0`
  there is a contractive completely positive `φ: A → B` with
  `dim B < ∞`, `‖φ(x)‖ ≥ ‖x‖ − ε` and `‖φ(xy) − φ(x)φ(y)‖ ≤ ε` on `F`.

Beyond these, only standard facts are used: QD passes to C\*-subalgebras and
unitizations, and extreme tracial states are factorial.

## Statement

Let `O_2 = C*(s_1, s_2)`, and let `h_1, ..., h_4` be the real and imaginary
parts of `s_1, s_2`, so `‖h_j‖ ≤ 1` and `C*(1, h_1, ..., h_4) = O_2`.  In
`C([0,1], O_2)` put

    u(t) = e^{i pi t} · 1,        w_j(t) = e^{i t h_j}     (j = 1..4),

and `A' = C*(u, w_1, ..., w_4)`.  Let `H = Z x F_4`, with `eps` the
generator of `Z` and `a_1, ..., a_4` free generators of `F_4`, and set
`Theta_0(eps) = u`, `Theta_0(a_j) = w_j`.  Then:

1. **(Embedding.)**  `A'` is quasidiagonal, and there are a norm matrix
   corona `Q = prod M_{d_n} / sum M_{d_n}` and a unital injective
   `*`-homomorphism `iota: A' → Q`.  So `Theta = iota ∘ Theta_0` is a
   homomorphism `H → U(Q)`.  The same holds with `Q` replaced by any norm
   ultraproduct `A_omega = prod_omega M_{d_n}`.
2. **(Unique trace.)**  `A'` has exactly one tracial state, `tau(f) = f(0)`,
   and `u(0) = 1`.
3. **(Corner-invisibility.)**  Let `B = Theta(H)' ∩ Q`.  For every nonzero
   projection `q ∈ B` and every tracial state `sigma` of `qQq`,

       ‖q Theta(eps) q − q‖_{2, sigma} = 0.

4. **(Nontriviality.)**  `‖Theta(eps) − 1‖ = 2`, and
   `sp(Theta(eps)) = { e^{i pi t} : 0 ≤ t ≤ 1 }`, the closed upper
   half-circle, which is a connected arc through `1`.

So `(Q, H, Theta, eps)` satisfies the hypothesis of
`commutant-projection-extraction` under any choice of normalized corner trace
and violates its conclusion.  **`commutant-projection-extraction` is false as
stated.**  It is also false in the approximate (contrapositive) form: with
`delta = 1`, no nonzero `q ∈ B` has `‖(Theta(eps) − lambda) q‖ < |lambda − 1|`
for any `lambda`.  If one did, `sigma(q |Theta(eps) − lambda|^2 q) < |lambda − 1|^2`
for a tracial state `sigma` of `qQq`, while by 2 the left side equals
`|u(0) − lambda|^2 = |1 − lambda|^2`.

The configuration is exactly the one that `corona-corner-detection-criterion`
clause 2 leaves open: a connected arc through `1`, with all trace mass at `1`.

## What this kills

Each item below dies because of invariant 2: `C*(Theta(H))` has a unique
trace, and that trace sits on the fiber where `Theta(eps) = 1`.  The
counterexample meets every hypothesis that the approaches below would use.

- **The group-free form of the hole.**  `commutant-projection-extraction` is
  stated "without any group-theoretic hypothesis beyond centrality".  That
  form is false.  Its note says any proof "must use either the vanishing of
  the trace mass off `1` or the (T) input".  The first option is closed:
  here the trace mass off `1` vanishes in the strongest possible sense, and
  the conclusion still fails.  Every surviving proof must use a property of
  `H` that `Z x F_4` lacks.
- **The real-rank-zero reduction.**  That reduction says "real rank zero of
  the relative commutant `B_omega` implies the claim".  So for this
  `Theta`, `B_omega = Theta(H)' ∩ A_omega` is **not** of real rank zero.
  More precisely, for a bump `f` at any `lambda ≠ 1` of the spectrum,
  `her_{B_omega}(f(Theta(eps)))` contains no nonzero projection.
- **The AW\*-masa reduction.**  No maximal abelian subalgebra of `B_omega`
  containing `Theta(eps)` is an AW\*-algebra.  If one were, the clopen
  spectral projection it supplies would contradict the corner computation
  in item 3.  Settling "whether masas of a matrix norm ultraproduct are
  AW\*" therefore cannot finish the hole in the group-free form.
- **Downstream.**  Two routes required the general claim:
  `torsion-free-non-mf-from-infinite-order-mark` and
  `lifted-thompson-t-eigencorners-via-projection-extraction`.  Both lose
  that prerequisite and must be re-based on an instance-specific statement.
  `lifted-thompson-t-centre-has-commutant-eigencorners` is untouched as an
  instance.  Thompson's `T` is not Kazhdan, though, so a Thompson analogue of
  this cone field is now the natural test against it (see Remark T).

## Remark K: what survives for Kazhdan sources

This remark is unconditional given one recalled import, and it is not part
of the established statement.  The import is standard: for a (T) group `H`
and a finite-dimensional irreducible representation `pi`, there is a central
projection `p_pi ∈ C*(H)` with `pi(p_pi) = 1` and `sigma(p_pi) = 0` for every
irreducible `sigma` not equivalent to `pi` (Akemann–Walter; Valette).

Assume `H` has (T) and `eps ∈ Z(H)`.  Then `Theta(p_pi) ∈ B`, and
`Theta(eps) Theta(p_pi) = pi(eps) Theta(p_pi)` exactly.

Now run the mechanism of this node for such an `H`.  Suppose `Theta_0(H)`
sits in a `C([0,1])`-field with `ev_t Theta_0(eps) = e(ct)` scalar for
`t > 0`, and suppose the base representation `ev_0 ∘ Theta_0` contains a
finite-dimensional `pi`.  Then `t ↦ ev_t Theta_0(p_pi)` is a norm-continuous
path of projections that is nonzero at `0`, hence nonzero for small `t`.  On
its range `eps` acts both by `pi(eps)` and by `e(ct)`, which is impossible
for all small `t`.

So **for Kazhdan `H` the cone mechanism with a finite-dimensional base
(which is what this node uses: the base is the trivial representation) is
impossible**.  A counterexample for the Kazhdan instance, for example the
(CPE\*) instance at `(Gamma~, z^m)` used by
`deligne-lattice-non-mf-forces-finite-parameter-group`, must have a base
fiber with no finite-dimensional subrepresentation that still carries all
corner traces.  For `Gamma~ = E_infinity` and `eps = z`, the natural such
base is the regular representation of `Sp_4(Z)`, reached along the
norm-continuous twisted-regular path `lambda_{c_t}` (the Maslov cocycle is
bounded).  But every fiber of that path carries the canonical trace, which
sees `z` as `e(ct) ≠ 1`, so that path is not a counterexample either.

## Remark T: Thompson test

The lifted Thompson group `T-bar` acts on `L^2(R)`, and `z` is the unit
translation.  Its Floquet fibers `rho_theta` have `rho_theta(z) = e(theta)`
scalar.  The single question to settle is whether `C*(rho_theta(T-bar))` is
traceless for `theta ≠ 0`, and whether the family forms an MF field over
`[0,1]`.  If both hold, this node's argument gives a counterexample to
`lifted-thompson-t-centre-has-commutant-eigencorners`.  That is posed only.

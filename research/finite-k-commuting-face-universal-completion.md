---
rg: 2
id: finite-k-commuting-face-universal-completion
kind: claim
title: Couple a finite face packet to a growing code without a larger universal completion
distinct_from:
  s3-cannot-be-a-homogeneous-parity-face-factor: that rules out S3 because its involution commuting graph has no mixed edges; this is the surviving finite-group search criterion.
  uniform-kazhdan-homogeneous-lcs-face-groups: that asks for the full growing code family and gap; this isolates the fixed finite algebraic packet needed by the proposed product construction.
---

OPEN, with the fixed-packet half solved.  The homogeneous Magic-Square faces
have universal group equal to the order-32 extraspecial Pauli group `K`.
What remains is to couple this packet to growing good-code columns without
creating a larger universal completion or an unrestricted multiplicity
algebra.

At positive rate an exact `K x F_2^r` target is now ruled out by the quadratic
mod-two-homology relator bound.  In the existing low-rate `Theta(r^2)` private
sampler that count is feasible, but packet-relative centrality is
Morita-neutral and leaves the contextual multiplicity escape untouched.  A
survivor must therefore use genuinely noncentral K labels, pass the finite
twisted-intertwiner distance criterion, and control the resulting extension
at quadratic occurrence size (or use a global actor).

`s3-cannot-be-a-homogeneous-parity-face-factor` shows that nonabelianity and
involution generation alone are insufficient, while the Magic Square solves
that fixed finite subproblem.  The load-bearing missing resource is now a
**noncentral code coupling with controlled universal completion**.

## Attempts

- **`K=S_3`.**  Refuted by
  `s3-cannot-be-a-homogeneous-parity-face-factor`: distinct transpositions do
  not commute, so every face relation remains valid in a free product of
  involution colors.
- **Repeat fixed K labels at positive density.**  This can improve the finite
  packet's empirical spectral weight but does not change the universal
  completion; an infinite kernel in the abelian-subgroup amalgam survives
  every repetition.
- **Use code distance alone for the product gap.**  Insufficient in
  nontrivial K sectors.  The exact replacement is the finite twisted-
  intertwiner condition of
  `fixed-k-code-product-gap-is-a-twisted-intertwiner-test`.
- **Use a homogeneous Magic-Square packet.**  This succeeds for the fixed
  factor: its universal face group is the extraspecial two-qubit Pauli group
  of order `32`.  However, the literal positive-rate direct product still
  fails.  The mod-two second-homology presentation bound requires
  `Omega(r^2)` relators for `K x (C_2)^r`, whereas bounded-width,
  bounded-occurrence faces provide only `O(r)`.  Only a controlled non-direct
  extension or a finite global actor remains open at positive rate.  This
  does not refute the existing private sampler's deliberately low-rate
  `Theta(r^2)` occurrence presentation.
- **Use packet-relative centrality in the low-rate sampler.**  Also
  insufficient.  On the Magic-Square packet's `J=-1` sector, every
  representation is `C^4 tensor M` and its commutant is the unrestricted
  multiplicity algebra `I_4 tensor B(M)`.  The sparse Clifford-cycle
  contextual escape tensors through unchanged.  Any survivor must use
  genuinely noncentral, twisted K labels rather than only commute the code
  variables with K.
- **Label every occurrence by a noncentral Pauli direction.**  Still
  insufficient when the packet action is pinned by inner conjugation.  If
  `r_i` has the same action on K as `k_i`, then `y_i=k_i^{-1}r_i` centralizes
  K; because the K labels satisfy every local face, all face relations reduce
  exactly to those on the `y_i`.  The presentation is Tietze-equivalent to
  `K x Gamma_H`, and the contextual multiplicity model survives.  A remaining
  packet construction must use genuinely outer/projective or multi-variable
  coupling, not an inner Pauli label field.
- **Use outer Clifford-normalizer labels.**  A fixed projective cocycle still
  does not help.  If `C_alpha C_beta=c(alpha,beta)C_(alpha beta)`, the
  multiplicity space can carry `conjugate(C_alpha)`, whose cocycle is inverse.
  Then `C_alpha tensor conjugate(C_alpha)` is an honest 16-dimensional label
  action, and tensoring any contextual code model gives an exact normalizing
  representation.  Outer labels pulled back from a locally satisfied finite
  automorphism system therefore reduce to affine phase shifts with a fixed
  absorber.  Only genuinely multi-occurrence coupling not factored through a
  finite local label solution remains.
- **General projective labels and higher-arity normalizer words.**  The
  conjugate-absorber argument is packet-independent: `C_g tensor
  conjugate(C_g)` turns every locally satisfied projective label pullback into
  an honest stationary action.  More generally, Schur factorization makes
  every ordinary word in normalizers of one irreducible packet equal to one
  fixed packet matrix tensored with one multiplicity word.  Exact
  satisfiability forces the packet matrix to be scalar, so arbitrary arity
  adds only affine phase equations on multiplicity.  The entire
  single-occurrence finite-packet lane is closed; a survivor must move between
  inequivalent sectors/corners, cease normalizing one common packet, or use a
  non-group-word compression relation.
- **Move between two inequivalent finite packet sectors.**  Pure sector
  transport still fails.  The finite K-type intertwiners form a projective
  groupoid; tensoring every arrow with its conjugate cancels the cocycle and
  gives an honest stationary bisection action.  Corner returns are fixed
  finite loop matrices tensored with the old multiplicity word, so every
  locally satisfied transport network admits the same contextual tensor
  escape.  The minimal remaining operation is an additive multi-path block
  in which one corner entry coherently sums several sector paths, not a
  normalizer bisection.
- **Use the minimal additive two-path corner cell.**  The explicit `D_8` HNN
  cell `V=t p_0+t^(-1)p_1` is a genuine nonnormal corner involution, but its
  multiplicity matrix is only `[[0,U^*],[U,0]]`; a block gauge removes `U`.
  Moreover a single compression `q w q` can be corner-unitary only when `w`
  normalizes `q`.  Hence the remaining construction needs multiple additive
  cells with a shared-block holonomy polynomial, not one stable word or one
  rank-one swap.

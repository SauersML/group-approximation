---
rg: 2
id: toeplitz-tail-retains-contextual-schur-density
kind: claim
title: A contextual Schur head survives or recurses inside the Toeplitz tail commutant
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
---

OPEN. Use the head-tail endomorphism of
`toeplitz-head-tail-unital-self-embedding` and the packet placement of
`schur-child-crosses-toeplitz-compressor` to prove the following uniform
microstate dichotomy.

On a positive-density forbidden packet carrier, either the locally placed
child/full Reynolds difference has a fixed positive-density component in

```text
Comm(alpha(Gamma)) minus Comm(Gamma),                           (TTR1)
```

or the residual `alpha(Gamma)` action which erases that component canonically
contains a new forbidden Schur carrier in the next Toeplitz tail. The carrier
loss and squared transport error must be at most a fixed multiple of the
named normalized-HS relator energy. Iteration must have a contraction factor
strictly below one, independent of matrix dimension and tail depth.

The local density in this dichotomy is now explicit rather than hypothetical.
After replacing the head by the finite full reset,
`symmetrized-full-reset-forces-fixed-reynolds-density` gives

```text
rank(E_C-E_B)/d^2=1/(2^(k+2)D^2).
```

The full reset simultaneously collapses the compatible packet-type cone to
one ray. Consequently the residual action in the second branch can erase the
wall only through its action on the common scalar multiplicity space; all
selector and radical-character leakage has already been symmetrized away.
The wall rank itself is structural, however, so the recurrence must also
retain the orientation supplied by the predicate surplus `2K_1n`; otherwise
the same wall is already present on inactive sectors and carries no soundness.

That orientation now has a canonical fixed-word formula:
`schur-predicate-is-character-density-difference` identifies it with
`Z_C-Z_B=P_f/(2D)` and proves
`tau(P_f)=4D^2||Z_C-Z_B||_2^2`. Hence the strongest useful form of the
dichotomy returns this explicit character-density difference in the residual
multiplicity algebra. It need not select individual packet copies or preserve
the whole Reynolds projection.

The first branch is paid by
`schur-wall-in-property-t-compressor-pays-hs-energy`; the second is summable
by `contractive-computation-ladder`. This is deliberately stronger than
recovering every externally fixed tail window: the recursion must act on the
same residual coefficient algebra which caused the loss in `(TTR1)`, thereby
excluding the spectator amplification in
`residual-action-can-erase-local-reynolds-density`.

The ring identity `sigma(a)=xay+eps(a)f` is the candidate bounded-cost return:
it reproduces the entire tail in one fixed formula rather than by a word whose
length grows with depth. What remains is to couple the shared BCS selector
projections to that formula using group words.

There is now an exact coefficient-root realization of that coupling.
`schur-idempotent-is-an-injective-toeplitz-defect` works over a fixed odd
finite splitting field and forms

```text
R_f=k[B_f]*_k k<x,y>/(yx=1,1-xy=P_f).
```

The packet algebra embeds, while every finite quotient kills the oriented
forbidden idempotent `P_f`. In `St_5(R_f)` the density becomes the literal
group word `x_12(P_f)`, and
`schur-toeplitz-root-mark-is-fd-invisible` proves that every exact
finite-dimensional unitary representation kills it. Thus the former
word-conversion problem is closed algebraically. Its robust content is
isolated as `hs-schur-toeplitz-root-defect-collapse`: replace the
dimension-dependent intersection of the finite root kernels by a contractive
weighted root-character recurrence. This is an alternative formulation of
the present conditional-expectation gate, not yet its proof.

The head algebra is also finitely actuated.  The characteristic-two formula
in `toeplitz-tail-plus-one-swap-generates` cannot be used verbatim over the
odd Schur splitting field, but
`schur-toeplitz-head-swap-exposes-the-steinberg-injectivity-fork` gives the
corrected involution `s_f=1-P_f-xP_fy+xP_f+P_fy` and proves
`R_f=<sigma(R_f),k[B_f],s_f>`.  Therefore no unbounded family of unrelated
head generators is needed.  The same audit records that finite recursive
presentation syntax is not yet closed: elementary shift injectivity and
Steinberg finite presentation currently live on opposite sides of an
unproved `St_5(sigma)` injectivity statement.  Analytically, the Schur
violation must still determine the action of the fixed actuator on the
residual multiplicity space.

The actuator can now be made part of the packet itself.
`schur-packet-head-actuator-generates-over-tail` embeds the `Q` child inside
`alpha(Gamma)`, scales the missing `p` generator by the head swap `s`, and
proves

```text
Gamma=<alpha(Gamma),B_f>.
```

Thus no algebraic generator remains outside the packet/tail incidence.  The
open content of this claim is strictly the dimension-free conditional
expectation alternative: the common tail commutant must retain packet mass or
recreate it in its residual multiplicity algebra.

There is now a second, sharper acceptable output of that alternative.
`coherent-summable-gap-clifford-tower` does not require selecting a finite
rank larger than the unknown matrix dimension.  It is enough that successive
residual tails produce jointly reducing carriers whose discarded traces are
summable and on which the returned relative Pauli cells accumulate.  Their
common meet then has positive trace and carries every finite Clifford rank,
contradicting finite dimensionality by
`summable-reducing-carriers-force-infinite-clifford-capacity`.  This makes the
needed conditional-expectation conclusion concrete: later tail carriers must
reduce all earlier head cells, not merely have large trace.

The compressor iterates also synchronize the selector carrier exactly, but
they do not amplify it by themselves.  The theorem
`toeplitz-schur-heads-share-child-but-have-rank-two` proves that every shifted
head shares the child and selector center pointwise, while all shifted missing
generators together have binary cocycle rank only two.  Therefore the recurse
branch must manufacture a new transverse child direction in the residual
commutant; simply applying `alpha` repeatedly to the one actuator can never
outrun residual dimension.

There is now an exact packet/residual factorization behind this request.
`toeplitz-finite-head-centralizes-deep-tail` identifies the first `N` tape
cells with `M_N(F_2)` and proves that `sigma^N(T)` acts as a scalar on that
whole head. Thus a fixed packet may be exactified in the head while the next
recursive challenge acts on its external multiplicity. What remains is the
weighted multiplicity inequality across successive head restrictions, not an
algebraic commutation problem.

## Attempts

- Merely place `B_f^Q` in `alpha(Gamma)` and `B_f` in `Gamma`: this dies by
  `residual-action-can-erase-local-reynolds-density`, since the rest of the
  compressed group may act irreducibly on the packet multiplicity.
- Recover every fixed collection of deeper Toeplitz heads: this gives only a
  growing hyperlinear profile; an arbitrary residual spectator can always be
  enlarged after the window is chosen.
- Active attack: use the explicit compression `a |-> y a x` to define the
  next carrier *inside the commutant of the residual action which erased the
  current carrier*. The missing estimate is a dimension-free conditional
  expectation inequality showing that loss of head Reynolds mass produces,
  with a strict contraction, selector mass in that compressed residual
  corner. The single head swap from
  `toeplitz-tail-plus-one-swap-generates` is the candidate bounded word which
  implements this transfer.
- Repeat the shifted packet head without changing its child: this now has an
  exact rank-two ceiling.  It preserves forbidden mass perfectly but produces
  only one Pauli capacity bit, irrespective of depth.
- Lift independent finite heads to a common Steinberg `K_2` sign: this also
  fails for the ordinary algebraic Toeplitz ring.  The localization boundary
  in `toeplitz-swindle-kills-head-k2-sign` makes the compact-head map
  `K_2(M_infinity(R))->K_2(T_R)` zero.  A viable central extension would have
  to use a genuinely global cocycle, not the finite-corner Steinberg symbol.
- Dinur's preprocess-power-compose architecture is now isolated as
  `hs-schur-packet-gap-amplification`. Classical graph powering supplies the
  needed anti-localization, while Schur packet composition is supposed to
  reset the local matrix scale. The unresolved point is not classical PCP
  soundness; it is synchronization of the contextwise HS exactifications on
  the shared selector words.
- The classical proof cannot itself supply that synchronization:
  `classical-pcp-gap-is-not-tracial-pvm-gap` records that a BCS may have a
  perfect tracial PVM assignment while having positive classical UNSAT. The
  appropriate input must be a quantum/Tailored-MIP answer-reduction theorem or
  a genuinely dimension-sensitive Schur multiplicity argument.
- Encode `P_f` as a Steinberg coefficient but leave the coefficient ring
  directly finite: this gives only a renamed root word and no orientation.
  The packet-headed Toeplitz envelope above supplies the missing strict
  defect. Exact finite-dimensional collapse is proved; its normalized-HS
  root-character propagation remains open.

---
rg: 2
id: fanizza-coherent-verifier-wandering-promotion
kind: claim
title: Promote the coherent Fanizza verifier reflection to one wandering Hecke word
distinct_from:
  balanced-router-pauli-holonomy-interface: that promotes two D8 packet reflections and asks a mixed return to trivialize their holonomy; this promotes one coherent-verifier reflection while retaining an infinite wandering normal form.
  compressed-reflection-kills-even-cesaro-mark: that proves the complete analytic passage from the corner approximation here to a finite-matrix Cesaro ceiling; this remains the algebraic construction of the wandering ordinary word and its packet compression.
---

OPEN.  Let `V_m` and the finite clock/flag carrier `Q` be the explicit
reflection and projection from
`uniform-clock-reflection-block-encodes-game-hamiltonian`.  Construct a
finitely presented group extension and an ordinary word `w` such that:

1. after fixed finite-packet exactification in every matrix microstate, the
   selected carrier `Q_U` has fixed positive mass and

   ```text
   ||Q_U(w(U)-V_m(U))Q_U||_2 <= omega(def);            (FCW1)
   ```

2. the native signal carrier lies in `Q_U`, with only a fixed computable
   packet loss;
3. the group normal form keeps `w^k` and `X_D^R w^k` pairwise distinct; and
4. a countably amplified perfect HALT representation extends, even though
   the selected compression of `w` is the finite-order reflection `V_m`.

By `compressed-reflection-kills-even-cesaro-mark`, `(FCW1)` itself gives an
`o(1)` upper bound for every fixed even marked Cesaro sum.  Thus no separate
weighted-state Dirichlet comparison is needed.  Clause 3 supplies canonical
linear Cesaro growth, and `wandering-mark-cesaro-amplifier` finishes.

There is now a sharper terminal audit.  By
`compressed-finite-order-wandering-is-terminal`, clauses 1 and 3 already
contradict hyperlinearity: compression to the reflection makes
`(w(U)^2-1)Q_U=o(1)`, whereas infinite order and finite support make
`(w^2-1)Q` nonzero in the regular group algebra.  Hence the Fanizza signal,
marked translates, and Cesaro amplification are not load-bearing after
`(FCW1)` has been established.  The strictly weaker live construction is
`localized-square-return-wandering-promotion`.

The exact tension is now explicit: `w` must be infinite and wandering in the
group regular normal form but look like the fixed reflection `V_m` after one
finite-dimensional packet compression.  A finite-edge graph-of-groups cell
cannot suffice, because its regular finite models reproduce the Hecke
compression.  The promotion must use a genuinely infinite-edge,
non-Bass--Serre, or finite-multiplicity return mechanism.

An infinite-edge self-similar return is not sufficient by itself either.
`self-similar-cylinder-return-regular-energy-floor` computes the exact
canonical obstruction: if the selected cylinder has density `alpha`, the
regular squared return defect is at least
`2 alpha-(2/pi)sin(pi alpha)`, even though the boundary/groupoid return can
be exact.  Hence a Nekrashevych, Toeplitz, or Leavitt normal form supplies a
noncanonical boundary carrier, not clause 1.  The surviving interface is a
matrix-only mechanism which promotes that cylinder mass to the canonical
packet while violating this regular Haar floor.

## Conjugate-product audit

The tempting word

```text
w=product_i t_i a_i t_i^(-1)
```

does not bypass this firewall.  The packet intertwiner's arbitrary
multiplicity unitary does cancel inside one conjugate on a selected type.
But `finite-graph-packet-compression-wandering-no-go`
shows that a representation-independent carrier return has only two normal
forms.  If every conjugate returns through an HNN edge relation, the stable
letters reduce and `w` belongs to a finite vertex packet.  If a stable letter
survives, then `q w q` lives on a nontrivial Hecke double coset, orthogonal to
the finite verifier `V_m` in the regular trace; residual finite quotients give
a fixed positive HS error.  Thus the multiplicity gauge is not the remaining
problem -- the incompatible pair is full carrier return versus ambient
wandering.

## Quantitative character-carrier audit

When the finite clock/flag line is groupified as a one-dimensional character
idempotent of a fixed packet `K`,
`character-carrier-wandering-floor` gives,
for every infinite-order candidate word,

```text
||Q w Q-V_m||_(2,regular)
 >= (1-1/sqrt(2))/sqrt(|K|).                           (FCW2)
```

The proof has an exact dichotomy.  If `w` fails to preserve the packet
character, a proper character-Hecke intersection loses at least half the
corner norm.  If it preserves the character, `w` reduces the corner, and
the reflection equation exposes the nonzero square-return word
`(w^2-1)Q`.  Hence every sufficiently canonical finite model has the same
positive floor up to profile error.  This does not refute the target--the
target is meant to exclude those canonical models and thereby prove
nonhyperlinearity--but it shows precisely that neither positive packet
density nor coherent reflection aggregation performs the promotion.  The
missing input is a dimension-independent matrix-only rule which overcomes
the explicit floor `(FCW2)` by making canonical microstates impossible.

## D16/Hadamard audit

`fanizza-verifier-d16-charger-globalizes-ground-support` diagonalizes the
coherent reflection in the flag-`X` basis.  It is selector-central with
blocks `I` and `sum_j e_(jj)(1-2L_j)`, and the transverse D16 commutator has
energy exactly four times the average losing mass.  But the native signal
carrier uses the transverse flag-`Z` line and is not reducing.  Making the
commutator a global relator forces every losing projection to vanish as an
operator, while the recorded HALT theorem supplies only a positive-signal
ground vector.  Hence the D16 cell reads the verifier Hamiltonian but does
not perform the required support localization or wandering promotion.

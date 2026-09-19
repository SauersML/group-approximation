# Shulman trace lifting: exact scope for the FALSE program

Date: 2026-08-10

## 1. Source correction

Two distinct Shulman papers are relevant, and conflating them creates a
false shortcut.

1. *The MF property for amalgamated free products*,
   [arXiv:2603.13564v2](https://arxiv.org/abs/2603.13564), proves that
   `A *_C A` is MF when `A` is separable MF and `C <= A` (Theorem 10), as
   well as the compatible-corona criterion for `A *_C B` (Theorem 20).
   It contains no theorem saying that hyperlinear traces on `A *_C A` are
   MF.
2. *Homotopy lifting, asymptotic homomorphisms, and traces*,
   [arXiv:2508.00125v5](https://arxiv.org/abs/2508.00125), proves in
   Corollary 35 that if `E` is Hilbert--Schmidt stable and `B` is homotopy
   dominated by `E`, then every hyperlinear trace on `B` is MF.

Thus the trace theorem has a homotopy-domination hypothesis. It is not a
trace-preserving addendum to symmetric-amalgam MF permanence.

## 2. The domination arrow points the wrong way for a symmetric double

Let

`B = A *_C A`.

Write `j_1:A -> B` for the first vertex inclusion and let

`p:B -> A`

be the fold homomorphism, equal to the identity on both vertex copies.
Then

`p compose j_1 = id_A`.

Consequently `A` is dominated by `B` (indeed, it is an exact retract of
`B`). Corollary 35 would need maps in the opposite direction whose
composition is homotopic to `id_B` in order to transfer trace lifting from
`A` to `B`.

The available fold maps only give

`j_1 compose p:B -> B`,

which collapses the second vertex copy onto the first. No homotopy from this
map to `id_B` is known. In particular, the theorem cannot currently be
applied with the HS-stable algebra `E=A` and the symmetric double as `B`.

This is a formal variance obstruction, not a missing estimate.

## 3. Exact stability obstruction

The following elementary consequence is useful for calibrating stability
proposals.

**Proposition (finite-representation invisibility versus HS stability).**
Let `Gamma` be a countable group and let `B` be a unital C-star completion of
the image of `C^*(Gamma)` carrying the canonical group trace `tau_Gamma`.
Suppose that `x in Gamma`, `x != 1`, has image `u_x in B`, and every
finite-dimensional star representation `pi:B -> M_d` satisfies

`pi(u_x)=1`.

If `B` is Hilbert--Schmidt stable, then `Gamma` is nonhyperlinear.

**Proof.** If `Gamma` were hyperlinear, the GNS von Neumann algebra of
`tau_Gamma` would embed trace-preservingly in a tracial matrix ultraproduct.
Equivalently, `tau_Gamma` would be a hyperlinear trace on `B`, represented by
a star homomorphism

`rho:B -> product_omega (M_(d_n), tr_(d_n))`.

Hilbert--Schmidt stability lifts `rho` to finite-dimensional star
representations `rho_n:B -> M_(d_n)`. By hypothesis every `rho_n` sends
`u_x` to `1`, hence `rho(u_x)=1`. But the canonical trace gives

`||rho(u_x)-1||_2^2 = tau_Gamma((u_x-1)^*(u_x-1)) = 2`,

because `x != 1`. This is a contradiction. End proof.

For the regular symmetric Kun--Thom double, the existing exact
finite-representation argument supplies precisely such an `x` in the fold
radical. Therefore HS stability of the **total double completion** would
produce an explicit nonhyperlinear group. This would be a major result, but
it points away from the desired hyperlinear-nonsofic conclusion.

## 4. MF traces do not close the fold certificate automatically

An MF trace is hyperlinear: operator-norm asymptotic multiplicativity implies
normalized-HS asymptotic multiplicativity. Hence an MF trace `tau` on the
symmetric double with

`tau((u_x-1)^*(u_x-1)) > 0`

would already give the desired hyperlinear image retaining the nonsofic
radical witness.

Theorem 10 only proves that the algebra `B` is MF. It yields at least one MF
trace, but it gives no reason for that trace to see the positive element
`(u_x-1)^*(u_x-1)`. In the present construction, the explicit MF trace
obtained by composing the profinite MF trace on `A` with the fold map
`p:B -> A` kills the fold radical.

Corollary 35 does not manufacture a new trace either: it upgrades an
**already given hyperlinear trace** to an MF trace. Thus applying it to the
canonical trace would require canonical-trace hyperlinearity, which is the
original missing conclusion.

## 5. Net consequence

The Shulman results leave three logically distinct gates:

1. algebra MF permanence for the untwisted symmetric double -- proved;
2. existence of an MF/hyperlinear trace seeing the fold radical -- open and
   sufficient for FALSE;
3. HS stability of the total completion -- open and sufficient instead for
   nonhyperlinearity.

The live FALSE target remains gate 2. Neither symmetric-amalgam permanence
nor homotopy trace lifting supplies it.

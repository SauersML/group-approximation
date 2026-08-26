---
rg: 2
id: cocycle-twisted-shift-freeness-galois-corner
kind: claim
title: Attack on twisted-shift amalgamated freeness via a Galois/crossed-product corner, isolating a bi-freeness input
distinct_from:
  fell-twist-freeness-via-haar-conjugation: that reduced to amalgamated strong freeness of a cocycle-twisted shift and disposed of the central case; this attacks the twisted case by realizing the shift inside a crossed product and reducing to bi-freeness of the ambient with the shift generator.
  strong-convergence-fell-shifted-hnn-model: that states the conditional; this works the sole hypothesis.
---

OPEN.  Continued attack on the estimate of
[[fell-twist-freeness-via-haar-conjugation]] (twisted case).  Steps graded.

**The object.**  `B_n = rho_n(L)'' ` on the `L`-regular corner
`H_n = l^2(L)^{(m_n)} (x) C^{k_n}`.  The Fell twist `W_n` acts as
`W_n = Sigma_n (x) sigma_n^{cocycle}` where `Sigma_n` is the left shift by a
generator on `l^2(L)` amplified, i.e. `W_n` implements on `B_n` the
`*`-automorphism `beta_n = Ad(W_n)` with
`beta_n(rho_n(l)) = rho_n(l) sigma_n(l)` (the `phi`-shear).  The ambient is
`A_n = rho_n(G x C)'' supseteq B_n`.  Want: `W_n` asymptotically free from
`A_n` over `B_n`.

## Step 1 -- the shear is a `B_n`-bimodule map `[PROVED]`

`beta_n` fixes `B_n`-central data and multiplies by the `B_n'`-valued cocycle
`sigma_n circ phi`.  Since `sigma_n(l) in B_n' cap A_n` (the `C`-part commutes
with `L`), `beta_n` is a `B_n`-`B_n`-bimodule automorphism.  So `W_n`
normalizes `B_n` and the pair `(A_n, W_n)` generates a crossed-product-like
algebra `A_n rtimes_{beta_n} Z` truncated at level `n`.  `[PROVED]`.

## Step 2 -- reduce to bi-freeness `[STANDARD framing]`

`W_n` is free from `A_n` over `B_n` iff, in Voiculescu's bi-free probability,
the left algebra `A_n` and the `B_n`-valued shift `W_n` are bi-free with
amalgamation over `B_n`.  For an honest *left* shift (Toeplitz/creation
operator) this is the model case of bi-freeness: the free shift is bi-free
from anything it does not see.  `[STANDARD for the untwisted shift]`.

## Step 3 -- the cocycle obstruction to bi-freeness `[GAP, the crux again]`

The twist `sigma_n circ phi` couples the shift to the `C`-part of `A_n`, and
`C = phi(L)`-generated: so `W_n` DOES see part of `A_n` (namely the `C`-copy)
through the cocycle.  Bi-freeness of `W_n` from `A_n` over `B_n` therefore
fails unless the `C`-part is itself free from the `G`-part over `L` -- which
is exactly the GKMP amalgam freeness `[PROVED, GKMP]` -- AND the shift is free
from that combined algebra.  The residual estimate is:

```text
the B_n-valued shift Sigma_n is asymptotically free over B_n from the
GKMP-free ambient A_n = (G-part) *_{B_n} (C-part),                    (T)
```

with the cocycle `sigma_n` carried along.  `[GAP]`.

## Step 4 -- what `(T)` reduces to `[GAP, but now a pure shift statement]`

Because the cocycle `sigma_n` lands in the `C`-part and the `C`-part is
GKMP-free from the `G`-part over `B_n`, the twist can be *absorbed* into the
`C`-factor: define `W_n'' = W_n . (1 (x) sigma_n^{-1}-tail)` so that `W_n''`
is the *untwisted* `B_n`-shift and `W_n = W_n'' . c_n` with `c_n` in the
`C`-factor.  Then `(T)` becomes:

```text
the untwisted B_n-shift W_n'' is asymptotically free over B_n from A_n,
AND the correction c_n in the (already free) C-factor does not spoil it.   (T')
```

The first clause of `(T')` is the standard free-shift/bi-freeness statement
`[STANDARD]`; the second clause is that multiplying a bi-free shift by an
element of one of the free faces preserves the amalgamated freeness of the
relevant alternating moments.  `[GAP -- this is now a finite bookkeeping of
B_n-valued moments, not a random-matrix theorem]`.

## Verdict -- genuine narrowing

The estimate is now reduced from "amalgamated strong freeness of a
cocycle-twisted shift" to two pieces: (i) the untwisted `B_n`-shift is free
over `B_n` from the ambient -- the standard free-shift model, `[STANDARD]`;
(ii) absorbing the cocycle correction `c_n`, which lives in the `C`-face that
is *already* GKMP-free from the `G`-face, preserves the alternating-moment
vanishing -- a `B_n`-valued moment computation.  If (ii) is a clean
consequence of GKMP freeness (as it appears, since `c_n` is in a free face),
then the whole prize closes.  I have NOT verified (ii) to the standard of a
proof: it requires checking that every alternating word
`a_0 W_n^{e_1} a_1 ...` has vanishing `B_n`-trace after the `c_n`-absorption,
across all reduced words, in the operator-norm/strong sense.  That check is a
finite-type but genuinely technical `B_n`-valued free-probability computation.

## Attempts

Steps 1--2 proved/standard; Step 3 identifies the cocycle coupling; Step 4
absorbs the cocycle into the free `C`-face, leaving (ii), a `B_n`-valued
alternating-moment vanishing, as the last unverified point -- now a
free-probability bookkeeping statement rather than a random-matrix estimate.

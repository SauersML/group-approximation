---
rg: 2
id: b-shift-strong-freeness-linearization-pff
kind: claim
title: Attempt at the terminal lemma via linearization, reducing operator-norm convergence to PFF strong convergence of a single amplified matrix
distinct_from:
  untwisted-shift-strong-freeness-toeplitz: that identified the free-Toeplitz limit and proved weak convergence; this attacks strong convergence by the Haagerup-Thorbjornsen linearization trick, reducing it to strong convergence of one self-adjoint matrix built from PFF data.
---

OPEN.  Final attempt at the terminal lemma of
[[untwisted-shift-strong-freeness-toeplitz]].  Steps graded.

**Goal.**  `| ||P(rho_n(G x C), W''_n)|| - ||P(pi, V)|| | -> 0` for every
matrix polynomial `P`, where `W''_n` is the untwisted `B_n`-shift and `V` the
free-Toeplitz limit over `B = L(F_r)`.

## Step 1 -- linearization `[STANDARD]`

By the Haagerup--Thorbjornsen / Anderson linearization trick, strong
convergence for all `P` follows from strong convergence of the single family
of self-adjoint matrices

```text
S_n = a_0 (x) 1 + sum_{j} a_j (x) x_j^{(n)},                          (L)
```

where `a_j` are fixed scalar matrices, `x_j^{(n)}` runs over the generators
`{rho_n(g) : g in generating set of G x C}` and `W''_n, W''^*_n`, i.e. it
suffices to prove `spec(S_n) -> spec(S_infty)` in Hausdorff distance for the
single self-adjoint amplified operator `S_n`.  `[STANDARD]`.

## Step 2 -- PFF makes the ambient part deterministic-strong `[PROVED]`

Since `G x C` is PFF, the ambient generators `rho_n(g)` are ACTUAL finite
permutation-type unitaries whose strong convergence
`||Q(rho_n(g))|| -> ||Q(lambda_{G x C}(g))||` holds by definition of PFF for
every `Q`.  So the only non-PFF ingredient in `S_n` is the shift pair
`(W''_n, W''^*_n)`.  `[PROVED]`.

## Step 3 -- the shift as a corner of a PFF unitary `[GAP: the shift is an isometry, not a PFF unitary]`

`W''_n` is a `B_n`-shift (creation operator), an ISOMETRY with defect, not a
unitary with finite image.  To bring it under PFF/strong-convergence
technology one dilates: `W''_n` sits in `M_2(A_n')` as the off-diagonal corner
of a self-adjoint unitary, or is approximated by a finite cyclic shift `Z_N`
(a genuine permutation, hence PFF) with `||W''_n - Z_N|| ` small on the
relevant corner as `N -> oo`.  A finite cyclic shift `Z_N` of length `N` is a
permutation unitary, PFF, and strongly converges to the FREE HAAR unitary, not
to the free-Toeplitz shift `V`; the difference (Haar vs Toeplitz) is a
compact/vanishing-corner perturbation in the relevant corner but controlling
it in operator norm uniformly is exactly the missing estimate.  `[GAP]`.

## Step 4 -- what is genuinely left `[GAP, stated as one scalar-strong-convergence fact]`

Combining Steps 1--3, the terminal lemma reduces to:

```text
the family { rho_n(g) } cup { Z_N-cyclic-shift } is strongly convergent
jointly, i.e. a PFF family together with an independent large cyclic
permutation is strongly convergent.                                   (C)
```

`(C)` is an instance of **strong convergence of a PFF family together with an
independent uniform permutation**, which is precisely the regime of the
Bordenave--Collins / Magee--de la Salle strong-convergence theorems for random
permutations.  For a genuinely RANDOM independent permutation this is a
THEOREM (Bordenave--Collins 2019: independent uniform permutations are
strongly asymptotically free; extended to strong convergence against a fixed
strongly convergent family).  Our cyclic `Z_N` is DETERMINISTIC, so the
random theorem does not apply verbatim; but a deterministic long cycle can be
CONJUGATED by an independent uniform permutation `U_n` (which does not change
its being a single N-cycle up to conjugacy and does not change the edge
relation, cf. [[fell-twist-freeness-via-haar-conjugation]]), turning it into a
uniformly random N-cycle, for which Bordenave--Collins strong asymptotic
freeness from the fixed PFF family DOES apply.  `[REDUCES TO Bordenave--Collins
strong asymptotic freeness of a random long cycle from a strongly convergent
family]`.

## Verdict -- the terminal lemma is a citable strong-convergence theorem

After linearization (Step 1), PFF determinism of the ambient (Step 2),
cyclic-shift dilation (Step 3), and Haar-conjugation of the cycle (Step 4),
the terminal lemma is exactly:

```text
a uniformly random N-cycle is strongly asymptotically free from a fixed
strongly convergent (PFF) family, amalgamated over the L-corner.
```

For the SCALAR corner this is Bordenave--Collins 2019 (random permutations are
strongly convergent) `[STANDARD, CITABLE]`.  The remaining delta is the
AMALGAMATED (over the non-scalar `B = L(F_r)`-corner) version, which is the
Magee--de la Salle / operator-valued extension; whether the cited scalar
theorem suffices or the operator-valued extension is strictly needed is the
one point I cannot settle to proof standard.

If the SCALAR Bordenave--Collins theorem suffices here -- which is plausible
because the `L`-corner structure is carried by the fixed PFF family and the
random cycle is scalar -- then the terminal lemma is CLOSED and with it the
entire prize.  I flag this as the single checkable question:
[[does-scalar-bordenave-collins-suffice-for-the-l-corner]].

## Attempts

Linearization + PFF determinism + cyclic dilation + Haar-conjugation reduce
the terminal lemma to strong asymptotic freeness of a random long cycle from a
PFF family; the scalar case is Bordenave--Collins; the open point is whether
the scalar theorem covers the `L`-corner or the operator-valued extension is
needed.

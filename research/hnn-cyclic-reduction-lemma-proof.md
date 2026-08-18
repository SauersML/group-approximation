---
rg: 2
id: hnn-cyclic-reduction-lemma-proof
kind: route
title: Cyclic reduction by rotating and deleting the seam pinch
target: hnn-cyclic-reduction-lemma
requires: []
artifacts:
  - GroupApproximation/Algebra/HNNTorsionFree.lean
---

# Direct word proof, with a source check against Collins' lemma

Let

```text
HNN(G,A,B,phi) = < G,t | t^-1 a t = phi(a), a in A >.
```

Write `x` in Britton-reduced form

```text
g_0 t^(eps_1) g_1 ... t^(eps_n) g_n,      eps_i in {+1,-1}.
```

Existence of such a spelling is the ordinary HNN normal-form theorem.  We
prove the exact dichotomy required by `HNNTorsionFree.ExistsCyclicConjugate`
by induction on the stable-letter length `n`.

## 1. Length zero is the base case

If `n=0`, then `x` lies in the base copy, so it has the required form
`g * of(b) * g^-1` (take `g=1`).

Assume henceforth `n>0`.

## 2. Absorb the head

Conjugating by `g_0^-1` and multiplying the two adjacent base coefficients
puts the conjugacy class in the head-absorbed form

```text
t^(eps_1) a_1 ... t^(eps_n) a_n.                         (*)
```

The original word was reduced, so every *internal* adjacent pair in `(*)`
satisfies the Britton chain condition.  Thus the only condition that can fail
for the `CyclicWord` interface is the one across the seam from `(eps_n,a_n)`
back to `eps_1`.

## 3. A bad seam shortens the stable-letter length

Suppose the seam condition fails.  Then the cyclic boundary is a Britton
pinch: the two boundary stable letters have opposite signs and the boundary
base coefficient lies in the corresponding associated subgroup.  Cyclically
rotate `(*)` by conjugating with its first stable-letter/base segment.  The bad
seam is now an *internal* subword, of one of the forms

```text
t^-1 a t       (a in A),
 t b t^-1      (b in B).
```

Apply the defining HNN relation (or its inverse) to replace that three-factor
subword by a single base-group coefficient.  Exactly two stable letters
disappear.  Free multiplication of the neighbouring base coefficients and,
if necessary, ordinary Britton reduction can only decrease the stable-letter
length further.  Hence the resulting conjugate of `x` has stable-letter
length `< n`.

Apply the induction hypothesis to that shorter conjugate.  Transitivity of
conjugacy gives the desired conclusion for `x`.

## 4. A good seam is the required cyclic word

If the seam does not fail, `(*)` is nonempty, is Britton-reduced at every
internal junction, and is Britton-reduced around the cyclic seam.  Taking its
letter list and coefficients gives precisely the repository's `CyclicWord`:
nonempty list, chain condition internally and at the seam, with the head
already absorbed.  Therefore `x` is conjugate to `c.elem phi` for that
`CyclicWord c`.

The induction terminates because the stable-letter length is a natural number
and every bad-seam step lowers it by at least two.  This proves the exact
interface, not merely the weaker statement that a minimal conjugate exists.

## Independent literature check

This is the standard cyclic-reduction theorem for HNN extensions.  A modern
source is Diekert--Duncan--Myasnikov, *Cyclic rewriting and conjugacy problems*,
arXiv:1206.4431, Theorem 5.2 (their restatement of Collins' lemma): every
element of an HNN extension is conjugate to a standard cyclically reduced
element.  Immediately before the theorem they describe the same algorithm:
continue Britton and cyclic reductions until a cyclically reduced form is
reached.  Their displayed standard form is the same head-absorbed cyclic word
used above.  This also matches the classical Lyndon--Schupp, Chapter IV,
cyclic-reduction argument cited by the claim.

Consequently [[hnn-cyclic-reduction-lemma]] is established.  The existing
route `hnn-torsion-theorem-proof` then establishes [[hnn-torsion-theorem]]
without any torsion hypothesis beyond torsion-freeness of the base.

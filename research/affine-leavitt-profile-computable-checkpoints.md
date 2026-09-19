---
rg: 2
id: affine-leavitt-profile-computable-checkpoints
kind: claim
title: The affine Leavitt root has computable double-exponential hyperlinear-profile checkpoints
distinct_from:
  leavitt-steinberg-quadratic-radius-pressure: that gives exact word-radius compression of the finite Heisenberg packets; this transfers each complete finite packet table through a fixed finite presentation and applies flexible HS exactification.
  slofstra-subexponential-hyperlinear-profile: that supplies a closed-form lower bound in the error parameter using a quantitative Higman embedding; this gives a computable checkpoint sequence whose error scales are not claimed to have a closed-form lower envelope.
  affine-leavitt-steinberg-hs-coefficient-decoder: that asks for one dimension-independent modulus collapsing the active root; this proves only increasingly strong finite-depth bounds at potentially rapidly shrinking moduli.
---

Fix a finite presentation of

```text
Gamma_A=St_5(L_A(S))
```

and let `w_A=x_13(A)`. There is an effectively computable sequence of
positive rationals `epsilon_n` such that

```text
hlp_Gamma_A(w_A;1,epsilon_n) >= .99 p^(2^n).              (ALP1)
```

Here `hlp(w;delta,epsilon)` is the least dimension of an
`epsilon`-representation of the fixed presentation keeping `w` at normalized
HS distance at least `delta` from the identity, with value `+infinity` when
no such tuple exists.

To compute `epsilon_n`, take the depth-`n` Heisenberg subgroup `H_n` from
`leavitt-prefixes-form-exponential-heisenberg-packet`. Choose one word in the
fixed generators of `Gamma_A` for each element of `H_n`, with the identity
represented by the empty word. For every pair `g,h in H_n`, the word

```text
q_g q_h q_(gh)^-1                                       (ALP2)
```

is null in the finite presentation. Enumerate van Kampen proofs in parallel
until proofs have been found for the entire finite multiplication table, and
let `B_n>=1` be the maximum area found. Put

```text
epsilon_n=1/(100 B_n).                                  (ALP3)
```

Every `epsilon_n`-representation evaluates the chosen representatives to an
all-pairs `.01`-homomorphism `H_n->U(d)`. If `w_A` has distance at least one,
Gowers--Hatami exactification cannot make the central root trivial, because
the compressed exact root lies within `.42` of it. The exact representation
therefore has dimension at least `p^(2^n)`, while flexible enlargement is at
most `(1-4(.01)^2)^-1`. Hence

```text
d >= (1-4(.01)^2) p^(2^n) > .99 p^(2^n),                (ALP4)
```

proving `(ALP1)`.

This is stronger than the non-effective compactness consequence of exact
finite-dimensional invisibility: both the threshold and the forced packet
dimension are computable from the fixed presentation. It still does not
prove nonhyperlinearity. The sequence `epsilon_n` may decay faster than any
useful prescribed function, and hyperlinearity permits the model dimension
to grow accordingly.

---
rg: 2
id: asymmetric-twist-descends-to-congruence-hnn-enemy
kind: claim
title: The swap involution twisted by an asymmetric coweight is a genuine HNN letter over a deeper congruence core
distinct_from:
  weyl-reverser-blocks-naive-swap-twist-descent: that refutes the descent for the self-dual twist h = diag(p,1,1/p), whose Weyl reverser h w_13 inverts the twist word; this proves the descent for the non-self-dual coweight g = diag(p^2,1/p,1/p), where the reverser transporter g Lambda cap Lambda g^(-1) is empty because the Cartan cell of g differs from that of g^(-1), so the obstruction vanishes and the ping-pong closes.
  swap-twist-centralizer-is-the-congruence-core: that computes the centralizer of the self-dual twist word; this reuses the same elliptic-hyperbolic axis argument for the asymmetric twist and then completes the remaining Britton injectivity, which the self-dual case cannot have.
  hnn-stable-letter-rounds-to-finite-order: that rounds a Haar letter down to finite-order letters over the SAME pair; this manufactures a Haar letter over a DEEPER pair from the swap involution, so composing the two regenerates enemies along the congruence tower.
---

**THEOREM (established here; proof in
`asymmetric-twist-descent-proof`).**  In
`E = Gamma *_Lambda (Lambda x <s>)` with `Lambda = SL_3(Z) <=
Gamma = SL_3(Z[1/p])`, let

```text
g = diag(p^2, 1/p, 1/p),      z_g = s (g s g^(-1)),
C_0(g) = Lambda cap g Lambda g^(-1)
       = { x in SL_3(Z) : p^3 | x_21, p^3 | x_31 },
```

a finite-index congruence-type subgroup containing `Lambda(p^3)`, hence
still co-dense in `Gamma`.  Then the marked homomorphism

```text
Gamma *_(C_0(g)) (C_0(g) x Z)  -->  E,    gamma |-> gamma,  t' |-> z_g
```

is INJECTIVE.  Consequently, in every canonical tracial model of `E` the
pair `(W*(pi(Gamma)), W*(L(C_0(g)), z_g))` is free with amalgamation over
`L(C_0(g))` with `z_g` Haar, and a canonical model of `E` yields a
canonical model of the deeper centralizer-HNN group
`G'_g = < Gamma, t' | [t', C_0(g)] = 1 >`.

**Why the Weyl obstruction is absent.**  A reverser would be an element
of `g Lambda cap Lambda g^(-1)`, nonempty exactly when the Cartan double
coset of `g` is self-dual.  The coweight of `g` is `(2,-1,-1)` and of
`g^(-1)` is `(1,1,-2)`: distinct dominant cells, so `K g K != K g^(-1) K`
in `SL_3(Q_p)` and the transporter is empty.  The self-dual twist
`h = diag(p,1,1/p)` has coweight `(1,0,-1)`, its own inverse's cell,
which is precisely why `weyl-reverser-blocks-naive-swap-twist-descent`
found the reverser there.  Asymmetry of the coweight is the exact
dividing line.

**Consequences for the enemy structure.**  Composing with
`hnn-stable-letter-rounds-to-finite-order` (applied to `G'_g`): any
canonical model of `E` produces a balanced free central involution over
`(C_0(g), Gamma)`, i.e. a canonical model of the deeper swap group
`E' = Gamma *_(C_0(g)) (C_0(g) x C_2)`.  The descent iterates: at each
stage twist by the (asymmetric) coweight again inside the smaller core.
So the ONE enemy that would make `E_p` hyperlinear must simultaneously
provide balanced free central involutions over an infinite strictly
decreasing chain of co-dense congruence-type cores, all inside one
sequence of microstates.  Every landed confinement or exclusion theorem
for a deeper pair therefore constrains the same single enemy.

## Attempts

- **Is the deeper pair's exact face also closed at p >= 11?**  The
  sector theorems (`odd-congruence-lambda-exact-sector-collapses`,
  `p-divisible-lambda-exact-mass-vanishes-at-large-primes`) are stated
  for the pair `(Lambda, Gamma)`.  Their proofs use co-density, the
  Weyl-orbit relations of the diagonal, and congruence Clifford theory
  at `p`-power levels -- all available for `(C_0(g), Gamma)` -- but the
  constants and the level-one transvection repair would need to be
  re-derived with `C_0(g)` in place of `Lambda`.  Not done; recorded as
  the natural continuation, since with it the deeper swap involution
  would again be outlier-confined, pushing the enemy's outlier
  obligation down the whole tower.

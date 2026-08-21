---
rg: 2
id: acceptance-return-is-one-corner-word
kind: claim
title: The Pauli-controlled acceptance return is one corner-word norm
distinct_from:
  pauli-zero-atom-removes-acceptance-source-deficit: that constructs the automatic positive Gram source and states the remaining trace moment; this identifies that moment exactly with one capacity-gated word norm.
  cyclic-acceptance-root-needs-kernel-reflection: that packages the additive Hecke return as a Steinberg coefficient; this uses the exact block unitary and needs no expansion of the acceptance product.
  global-covariance-misses-capacity-compression: that shows an uncompressed covariance word leaves a commutator with the capacity cut; this keeps the capacity cut inside the sole remaining coefficient.
---

Use the notation of
`pauli-zero-atom-removes-acceptance-source-deficit`.  Thus `W_game` is the
fixed block-encoded acceptance unitary, `P_0` is the zero-control atom, `Q`
is the commuting capacity projection, and

```text
G=P_0Q.                                                   (ACW1)
```

The remaining return scalar is

```text
eta_0(Q)
 =||G||_2^2-Re tau(G^* W_game G).                        (ACW2)
```

## Exact corner-word identity

### Theorem

In every finite tracial von Neumann algebra,

```text
2 eta_0(Q)=||(W_game-I)P_0Q||_2^2.                       (ACW3)
```

### Proof

Since `W_game` is unitary,

```text
||(W_game-I)G||_2^2
 =||W_game G||_2^2+||G||_2^2
   -2 Re tau(G^*W_gameG)
 =2||G||_2^2-2 Re tau(G^*W_gameG).
```

Substitute `(ACW2)`.  No commutation between `W_game` and `G` is used.  ∎

Consequently the open estimate `(PAZ12)` is exactly

```text
||(W_game-I)P_0Q||_2^2<=2K E_rel+o(1).                 (ACW4)
```

The finite game gap and the unique Pauli spin source give the opposite
inequality

```text
||(W_game-I)P_0Q||_2^2
 >=2(1-rho)2^(-m)tau(Q)-o(1).                          (ACW5)
```

Thus a group-word cell proving `(ACW4)` pays the complete marked capacity
mass immediately.

## Smallest algebraic packaging

The coefficient

```text
C_Q=(W_game-I)P_0Q                                     (ACW6)
```

is one fixed finite coefficient: `W_game` is one block unitary, `P_0` is a
fixed Pauli atom, and `Q` is the single capacity cut.  A Steinberg
linearization may therefore name one root `x_12(C_Q)`.  No orthogonal row,
individual verifier residuals, or expanded Hecke sum is logically needed.

As in `canonical-root-coordinate-is-binary-not-an-l2-authenticator`, merely
declaring that root trivial does not prove `(ACW4)`.  The required semantic
input is the one-coordinate, capacity-relative kernel reflection

```text
Phi(x_12(C_Q))=1
  implies C_Q=0 in L2 of every canonical matrix ultraproduct. (ACW7)
```

The gain is that `(ACW7)` authenticates a literal block-unitary corner rather
than an arbitrary additive coefficient row.  This is the narrowest current
matrix-only target.

## Firewalls

- In the exact perfect commuting witness, `G` is fixed by `W_game`, so
  `C_Q=0` while the native mark may remain nontrivial.
- In the canonical regular representation, the game gap need not hold and
  the return corner may survive.  Hence `(ACW7)` cannot be replaced by a
  universal tracial group-algebra identity.
- Setting `W_game=I` globally is invalid: it destroys the finite/infinite
  asymmetry.  Only the compressed corner `(ACW6)` may be forced to return.

The remaining construction problem is therefore precise: realize one
capacity-gated partial vector/corner in ordinary group syntax and prove
matrix-only kernel reflection for `(ACW6)` without imposing the same corner
identity in the regular trace.

## Attempts

- **Set `W_game=I` as an ordinary relator.**  This forces the whole verifier
  unitary to be trivial, not merely its action on the selected Gram corner,
  and destroys the exact-witness firewall.
- **Name `C_Q` by one Steinberg root and kill that root.**  This compresses
  the syntax, but `canonical-root-coordinate-is-binary-not-an-l2-authenticator`
  shows that a trivial root word does not by itself reflect the decoded
  coefficient norm.
- **Drop the capacity cut and use `(W_game-I)P_0`.**  The return then acts on
  the entire Pauli-zero atom rather than the marked source; the finite game
  contraction would incorrectly charge unmarked spectator mass.
- **Use only finite packet exactification.**  A tensor-product model can put
  the exact control/root tables and the positive capacity source in
  independent multiplicity reservoirs.  A genuinely mixed corner relation
  is still required.

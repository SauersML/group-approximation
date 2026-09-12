---
rg: 2
id: dual-singer-three-bit-incidence-retains-central-return
kind: claim
title: A second three-bit Singer incidence only reorders the same Pauli orbit and retains the central return gauge
artifacts:
  - experiments/dual_singer_pauli_incidence_audit.py
  - research/dual-singer-three-bit-incidence-fence-proof.md
distinct_from:
  native-inverse-pair-seven-orbits-retain-external-gauge: that computes the literal row-one inverse-pair orbit and its one Singer cross table; this classifies every possible second order-seven linear action on the same three-bit Pauli register.
  recentered-order-seven-heads-have-actor-holonomy: that inserts regular actor holonomy for the complete five-pair packet; this isolates the smaller primal--dual incidence module and proves that even two different Singer tables do not kill its central commutator.
---

**ESTABLISHED FINITE-MODULE FENCE.**  Let `V=F_2^3`, let `S` be any
order-seven element of `GL(V)`, and let `a in V\{0}` and
`phi in V^*\{0}`.  Then

```text
{S^k a:0<=k<=6}=V\{0},
{S^(-transpose k)phi:0<=k<=6}=V^*\{0}.                (DSI1)
```

Both orbit sums vanish.  The primal--dual incidence table

```text
A_(k,l)=<S^(-transpose l)phi,S^k a> in F_2             (DSI2)
```

has weight four in every row and every column, and therefore total weight
`28`.  This recovers the `7+21` count of
`native-inverse-pair-seven-orbits-retain-external-gauge` without depending
on the chosen Singer matrix or the chosen nonzero primal and dual vectors.

Now fix `a,phi` with `<phi,a>=1` and put the Pauli operators on `C[V]`

```text
X_a delta_x=delta_(x+a),       Z_phi delta_x=(-1)^<phi,x>delta_x.
```

On `H=H_+ direct_sum H_-`, take the occurrences to be the identity on
`H_+` and the indicated Pauli operators on `H_-`.  Their commutator is the
nontrivial central reflection

```text
E=1_(H_+) direct_sum (-1)_(H_-).                       (DSI3)
```

The permutation implementer of every `S in GL(V)` realizes its exact
action on both Pauli families.  Hence all forward and reverse seven-orbit
norms are one, every cross commutator is exactly the power of `E` prescribed
by `(DSI2)`, and `E` remains nontrivial.

Adding a second Singer action `R` on this same register does not add a new
orbit: its primal and dual orbits in `(DSI1)` are the same seven-element
sets in a different order.  The canonical permutation implementers realize
all multiplication relations in the finite actor group `<S,R>`, while the
same nontrivial `E` remains central.  Thus two different incidence matrices,
or indeed any finite family of order-seven linear actions on this fixed
three-bit register, cannot force the returned gauge to be trivial or identify
it with an external native transition gauge.

The MSI audit enumerates all `168` elements of `GL_3(F_2)`, all `48`
order-seven elements, and all nonzero primal/dual choices.  It finds `14`
ordered incidence tables, each with row and column weight four and total
weight `28`; every pair of Singer actions has the same nonzero primal orbit.

This is deliberately a fence only on a second **linear Singer incidence on
the existing three-bit Pauli register**.  It does not exclude an ordinary
EL20 word which exposes an uncancelled Leavitt prefix coefficient, types an
intermediate nonnormal occurrence on the signed carrier, or introduces a
cross relation outside the Pauli semidirect product.  Such a
coefficient-sensitive relation, rather than another Singer norm table, is
still required for the same-carrier gauge lock.

No Property `(T)`, Kazhdan input, trace hypothesis, literature result,
local computation, or Lean compilation is used.

DERIVATION
dual-singer-three-bit-incidence-fence-proof

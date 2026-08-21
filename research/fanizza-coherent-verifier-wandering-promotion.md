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

The exact tension is now explicit: `w` must be infinite and wandering in the
group regular normal form but look like the fixed reflection `V_m` after one
finite-dimensional packet compression.  A finite-edge graph-of-groups cell
cannot suffice, because its regular finite models reproduce the Hecke
compression.  The promotion must use a genuinely infinite-edge,
non-Bass--Serre, or finite-multiplicity return mechanism.

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

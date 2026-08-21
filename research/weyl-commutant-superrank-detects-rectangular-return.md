---
rg: 2
id: weyl-commutant-superrank-detects-rectangular-return
kind: claim
title: Normalized commutant superrank detects the first Leavitt rectangular escape
distinct_from:
  first-leavitt-weyl-cell-has-exact-rectangular-model: that constructs the source-multiplicity/target-factor trade and detects it by a standard polynomial; this gives an explicit finite-multiplicity scalar computed from squared trace moments.
  fixed-pi-degree-fingerprints-packet-label-factor: that uses one alternating polynomial evaluation on selected words; this averages conjugation over the whole fixed Heisenberg packet and reads the rank of its commutant projection.
---

ESTABLISHED.  Let `Q` be finite and let `rho:Q->U(d)` be exact.  The averaging
operator on Hilbert--Schmidt matrix space

```text
E_Q(T)=(1/|Q|) sum_(q in Q) rho(q) T rho(q)^*             (WCS1)
```

is the orthogonal projection onto `rho(Q)'`.  Its normalized supertrace is

```text
c_Q(rho)
 := rank(E_Q)/d^2
  = dim(rho(Q)')/d^2
  = (1/|Q|) sum_(q in Q) |tr_d(rho(q))|^2.                (WCS2)
```

The last formula follows from
`Tr_super(Ad(rho(q)))=|Tr(rho(q))|^2`.

Let `H_N(p)` be the finite Heisenberg group with `N` Weyl pairs and central
element `J`.  On a fixed nontrivial phase `J=zeta`, its unique irreducible
has dimension `p^N`.  Hence every representation on that phase is
`M_(p^N) tensor 1_m`, and

```text
c_(H_N,zeta)=p^(-2N),                                    (WCS3)
```

independently of the spectator multiplicity `m`.

For the depth-zero/depth-one affine-Leavitt packets this gives the fixed gap

```text
c_source-c_target=p^(-2)-p^(-4)>0.                        (WCS4)
```

The exact rectangular model realizes both values in the same ambient matrix
algebra by changing multiplicity, so `(WCS4)` alone is not a contradiction.
But any mixed return which identifies the target packet with the **same
source factor including its multiplicity reservoir** must identify their
commutant projections and therefore their normalized supertraces, violating
`(WCS4)`.

This is a genuinely matrix-coordinate observable: normalized superrank has
no analogue forcing equality in an arbitrary finite tracial von Neumann
algebra, while in matrices it is unchanged by common spectator
amplification.  It is also finite and robust.  Each `(WCS2)` uses only the
squared traces of one fixed finite group table; Gowers--Hatami exactification
transfers sufficiently accurate packet microstates to `(WCS3)` with a
dimension-independent error.

Thus the remaining affine mixed-loop theorem has either of two finite
sufficient endpoint forms:

1. return the selected `2p` target Pauli words to the source factor and use
   the `s_(2p)` floor `(FWC6)`; or
2. return the target commutant averaging projection to the source
   commutant and contradict `(WCS4)`.

The second form supplies the requested explicit multiplicity observable.
What remains open is proving from the mixed rank-five/six Steinberg loops
that the return preserves this normalized commutant projection rather than
paying for the target factor by shrinking its multiplicity.

---
rg: 2
id: x2-reduces-to-three-operator-packets
kind: claim
title: Local AFD for three-operator packets implies it for all finite packets
distinct_from:
  stw10-x2-reduces-to-finitely-generated-weakly-dense-witnesses: that bounds the witness ALGEBRA (finitely generated, weakly dense); this bounds the PACKET SIZE in Popa's criterion itself, from arbitrary finite to three operators, by an explicit clock-shift encoding.
  x2-local-afd-holds-on-abelian-packets: that solves the commuting locus; this is a quantifier reduction valid for all packets, and together they focus X(2) on one generic non-commuting triple (two unitaries and a contraction).
  popa-projection-formulations-of-x2: that is the equivalence of X(2) with the local-AFD criterion over all packets; this theorem shrinks the packet quantifier before that equivalence is applied.
artifacts:
  - research/artifacts/x2-shadow-avoidance-recon-2026-08-31.md
---

If Popa's local-AFD criterion holds for every packet of the form
`{u, w, x}` with `u, w ∈ U(R)` and `‖x‖ ≤ 1` — three operators, i.e.
six self-adjoint contractions — then it holds for every finite packet
of `R`.  Combined with `popa-projection-formulations-of-x2`:

```text
X(2)  ⟺  local AFD for all three-operator packets {u, w, x}.
```

The encoding: given self-adjoint contractions `b_1,…,b_m`, pass to
`R ⊗ M_m ≅ R` (local AFD is isomorphism-invariant) where the packet
becomes `{b_k ⊗ 1}`; take `u := 1⊗d` (clock), `w := 1⊗c` (shift),
`x := (1/m) Σ_k b_k ⊗ c^k`.  The gapped diagonal `h = 1⊗diag(1..m)`
is a Lipschitz function of the clock, every matrix-unit corner of `x`
carries one `b_k`, and near-commutation with the shift forces any
local-AFD projection for the triple to have near-equal diagonal
blocks — which defeats the dead-corner escape and lets the packet
data be decoded.  Proof: `x2-three-operator-reduction-proof`.

Consequences:

* X(2) is now a statement about THREE operators of `R` — the analogue
  of the classical few-operator normal forms.  With
  `x2-local-afd-holds-on-abelian-packets`, the surviving difficulty is
  one genuinely non-commuting triple; with the counterexample profile
  (`shadow-avoidance-fails-at-column-isometries`), a refuting triple
  must carry full-support non-normal mass with no 2-norm rate.
* The reduction consumes no hyperfiniteness — it holds in any II₁
  factor `N ≅ N ⊗ M_m`, so the same normal form applies to
  "is `N` quasidiagonal" for every McDuff factor; for `R` it composes
  with `stw10-x2-reduces-to-finitely-generated-weakly-dense-witnesses`
  in the orthogonal (algebra-level) direction.
* Constants: the tolerance transfer is `ε' = ε'(ε, m)` with
  `m`-dependent constants (Lagrange interpolation on the gapped
  spectrum is exponential in `m`); no uniformity in `m` is claimed or
  needed, since the packet is fixed before `ε'` is chosen.

---
rg: 2
id: full-label-chord-normalizer-proof
kind: proof_route
target: full-label-chord-normalization-kills-the-hilbert-hotel
uses:
  - translation-reset-leaves-a-compressed-gram-spectator
  - semisimple-trace-charts-cannot-authenticate-proper-fullness
---

The commutant of `End(V) tensor I_K` is `I_V tensor B(K)`, proving
`(FNC3)`.  Since `E,F` are label projections, `(FNC4)` follows immediately.

For the quantitative statement, let `P` be Weyl conjugation averaging and
put `eta=||U-P(U)||_2`.  Orthogonality of conditional expectation gives

```text
D_W(U)^2=2 eta^2.
```

The contraction `P(U)` has a polar unitary `V` in the commutant with
`||P(U)-V||_2<=eta`, hence `||U-V||_2<=2eta`.  The map
`U |-> E-EU^*FUE` is `2`-Lipschitz on unitaries, and its value at `V` is
`H`.  Therefore

```text
||q-H||_2<=4eta,
D_W(U)^2=2eta^2>=||q-H||_2^2/8.
```

For `q=E_0 tensor Q`, direct trace calculation gives `(FNC7)` and hence
`(FNC6)`.

Finally, prescribed covariance on fixed charts which generate `End(V)`
differs from one fixed label implementer by an element of the common
commutant, proving `(FNC8)`.  The external unitary cancels from the Gram, so
the finite label rank deficit persists in every amplification.

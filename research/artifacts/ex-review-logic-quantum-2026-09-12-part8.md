# EX review, logic and quantum: part 8. Mal'tsev tensor closure of coset-system models (ex-kac-quantum-compiler), and what stays unreviewed

Lane `ex-verify-logic-quantum`, 2026-09-13 02:55 CDT.  Index: `ex-review-logic-quantum-2026-09-12.md`.

## 8.0 Verdicts

| item | lane | verdict |
|---|---|---|
| `coset-system-models-are-closed-under-maltsev-tensor` (+ `-proof`) | kac-quantum-compiler | PASS |

## 8.1 Mal'tsev tensor closure: PASS

- **PVM.**  The atoms `p^s (x) (p'^t)^op (x) p''^u` are orthogonal projections summing to `1`, and each
  lies in exactly one `P^r`, `r = s t^-1 u`.
- **Coset closure.**
  - In `M'^op`, `(p'^t)^op (p'^(t'))^op = (p'^(t') p'^t)^op = (Y^*)^op`.
  - Coordinatewise, `(s,s')(t,t')^-1(u,u') = c d_1 d_2^-1 d_3 in cD` whenever all three pairs lie in
    `cD`.  So every surviving term of `P^r P^(r')` with `(r,r')` off `cD` has a factor indexed off
    `cD`.
- **Orthogonality.**
  - `X^* X' = p^(s') p^s p^σ p^(σ')` vanishes unless `σ = s`.
  - The trace `τ(p^(σ') p^(s') p^s)` vanishes unless `σ' = s'`.
  - Tensor products of HS-orthogonal families are HS-orthogonal, so squared norms add over tuples.
- **Additivity.**  Split by which pair is off `cD`, and use `sum_(t,t') ||Y||_2^2 = τ'(1) = 1`.  This
  gives `δ(P) <= δ(p) + δ(p') + δ(p'')`.
- **Unary sectors.**  `P^(π σ^-1 ρ)` dominates the product atom, whose trace is
  `(1-ε)(1-ε')(1-ε'') >= 1 - ε - ε' - ε''`.
- **Classes.**
  - Finite-dimensional tensor products are finite-dimensional.
  - `R^op ≅ R` gives `(R^U)^op` embeddable.
  - `R^U (x̄) R^U ⊂ (R (x̄) R)^U ≅ R^U`.
  - Product traces are traces.

## 8.2 Established nodes of the twelve lanes not re-derived in this review

Citation routes whose theorem numbers were not re-read at source here:
- `nlts-hamiltonians-from-good-qldpc-codes-citation` (Anshu--Breuckmann--Nirkhe v4);
- `commuting-hamiltonians-on-small-set-expanders-in-np-citation` (Aharonov--Eldar v1);
- `product-states-approximate-high-degree-2-local-citation` and
  `two-local-degree-amplification-gives-np-witnesses-citation` (Brandao--Harrow v2);
- `natarajan-vidick-games-pcp-amplification-error-citation` (Natarajan--Nirkhe v1);
- `small-set-expansion-hypothesis-implies-ugc-citation`,
  `affine-ug-easy-on-globally-hypercontractive-graphs-citation` and
  `affine-ug-easy-on-certifiably-hypercontractive-graphs-citation` (ex-ugc).

Node-level only, with artifacts not read line by line:
- part 4: the ugc-rounding-pgroups artifacts;
- part 5: `liftable-masa-in-every-model-iff-uniform-hs-kun-partitions`;
- part 6: `theorem-e-vertex-types-equidistribute-on-finite-sl-d-orbits` and
  `port-generated-square-completions-force-coset-support`.

Ledger nodes:
- `arithmetical-complexity-table-of-group-properties`.  Checked only that its famous cells (sofic and
  amenable on finite presentations) read OPEN.
- `residual-finiteness-two-generator-recursive-is-pi3-complete` and
  `residual-finiteness-of-enumerated-presentations-is-pi3-complete`.  These are pre-EX Lean-backed
  nodes that the lane touched.

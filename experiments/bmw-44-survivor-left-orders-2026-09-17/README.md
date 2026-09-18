# Non-left-orderability certificates for the parity kernels of 40_40 #193, #281, #332

Claim: `research/bmw-40-40-193-281-332-parity-kernels-not-left-orderable.md`.
Proof: `research/bmw-40-40-193-281-332-subgroup-cone-certificate-proof.md`.

The census file and the helper module `lo_census.py` are the ones in `../bmw-census-left-orders-2026-09-17/`.
The scripts below import `lo_census` from there. Run them from this directory.

## Result

For each of the classes `#193`, `#281` and `#332` of `census_40_40.json`, let `Γ` be the BMW group and `Γ^+` its
parity kernel. Then `Γ^+` contains a 4-generated subgroup `M` that is not left-orderable. So `Γ^+` is not
left-orderable. Reducibility plays no role.

`M = ⟨x, y, f x^{-1} f, g y^{-1} g⟩`, with `x = v_i v_j` and `y = h_k h_l`:

| class | x | y | f x^{-1} f | g y^{-1} g |
|---|---|---|---|---|
| #281 | `v0v1` | `h0h1` | `v3v1v0v3` | `h3h1h0h3` |
| #332 | `v0v1` | `h0h1` | `v3v1v0v3` | `h3h1h0h3` |
| #193 | `v1v3` | `h1h2` | `v2v3v1v2` | `h3h2h1h3` |

Each certificate `cert_<class>.json` is deletion-minimal. It has:
- `elements`: 333 nontrivial elements of `Γ^+`, in normal form `V-word|H-word`;
- `relations`: 420 triples `[p, q, c]`, each meaning `e_p · e_q = e_c`. No relation has product 1.

The CNF has these clauses:
- exactly one of `p_g`, `p_{g^{-1}}`, for each element and its inverse (490 variables);
- `p_a ∧ p_b → p_c`, one for each relation.

It is unsatisfiable. The positive cone of a left order would satisfy it, so no left order exists.

## Files

- `verify_cert.py census cert.json`: the independent checker. It uses only the 16 squares of the class. It checks:
  1. the squares form a bijection `H × V → V × H`;
  2. the rewriting system `{xx → 1, h v → v' h'}` is locally confluent. It terminates, so normal forms are unique;
  3. every element is nontrivial, in normal form, of even V- and H-length (so it lies in `Γ^+`), and not an involution;
  4. every relation holds, by rewriting the concatenated word;
  5. the CNF is UNSAT with Glucose 4, MiniSat 2.2 and CaDiCaL 1.5.3;
  6. a Glucose DRUP refutation passes a self-contained reverse-unit-propagation checker (about 20 lines).

  Output: `verify.log`. All three classes pass: UNSAT with every solver, and the RUP check is `True`. The DRUP
  proofs have 151 lemma lines for #281 and #332, and 291 for #193.
- `certgen.py census class R short i j f k l g out.json`: builds the positive-cone instance on the ball of radius
  `R` in `M`'s four generators and their inverses. One factor of each relation has generator length at most
  `short`. It then extracts a deletion-minimal unsat core (CaDiCaL assumptions). Output: `certgen.log`.
  - `R = 4`, `short = 2`, ball of 3169 elements.
  - Arguments used: `281 4 2 0 1 3 0 1 3`, `332 4 2 0 1 3 0 1 3`, `193 4 2 1 3 2 1 2 3`.
- `gen_search.py class R short`: tries all 144 subgroups of this shape for one class, at the same radius. The
  shape is `(i<j, f∉{i,j}, k<l, g∉{k,l})`.
  - `gs193.log`: one UNSAT subgroup for #193.
  - `gs332.log`: one UNSAT subgroup for #332.
  - `gs0.log`: calibration on class `#0`, the product class (`h v = v h`, so `Γ^+ = W_4^+ × W_4^+ ≅ F_3 × F_3`,
    which is left-orderable). 0 of 144 instances are UNSAT, as they must be.

## Why earlier SAT runs missed this

The earlier pipeline (`out_40_40.jsonl`, `bigsat*.log`) used balls in the eight letters of `Γ`. It reached radius
10 with one factor of length at most 2, and radius 8 with one factor of length at most 4. Those instances stayed
SAT.

The certificate elements have letter length up to 14, mostly 10 and 12. Two statistics for the 420 relations of
#281 (those of #193 are almost the same):
- about 173 involve an element longer than 10 letters, which lies outside every earlier ball;
- in 180 of them even the shorter factor has 6 or 8 letters, while the earlier runs allowed at most 4.

The ball in `M`'s generators contains these relations and has only 3169 elements.

# Exact certificate checker over the binary Leavitt unit group

`G = R^x`, `R = L_{F_2}(1,2) = F_2<s0,s1,t0,t1 | t_i s_j = delta_ij, s0t0 + s1t1 = 1>`.

This is the one shared Leavitt tool for every lane: Kaplansky direct finiteness, Gottschalk
surjunctivity, Kervaire--Laudenbach, and anything else needing Leavitt normal forms. Call it;
don't copy it. Pure Python 3.8, stdlib only. Nothing runs locally.

**Shared copy on MSI:** `/projects/standard/hsiehph/sauer354/nonsofic-certificates/current/experiments/nonsofic-certificates/`
(an archive of `origin/main`; its `VERSION` file names the commit).

```bash
msi login "srun -p msismall -t 00:10:00 -c 1 --mem=2G bash -lc 'module load python3; \
  cd /projects/standard/hsiehph/sauer354/nonsofic-certificates/current/experiments/nonsofic-certificates && \
  python3 certcheck.py /path/to/cert.json'"
```

## Conventions

- A monomial `(alpha, beta)` is `S[alpha]T[beta] = s_{alpha_1}...s_{alpha_k} t_{beta_l}...t_{beta_1}`.
  As an operator it replaces the prefix `beta` by `alpha`. This matches
  `experiments/depth_one_paired_leavitt_return_search.py`.
- Expressions: `s0 s1 t0 t1`, `S[01]T[10]` (= `s0 s1 t0 t1`), `1 + s0 t1`, `(1+s0t1)(1+s1t0)`,
  `(s0 + t1)^3`. The only constants are `0` and `1`. Write `S[01]`, not `s01`; the parser
  rejects the ambiguous form.
- Automata: alphabet `{0..k-1}`, memory list `M = (m_0..m_{r-1})`, rule table of `k^r` symbols
  indexed by `sum_i p_i k^i`, and `tau(x)(g) = mu(x(g m_0), ..., x(g m_{r-1}))`. The linear
  automaton of `a` in `F_2[G]` is `tau_a(x)(g) = sum_{h in supp a} x(gh)`, and
  `tau_a o tau_b = tau_{ab}`.
- Matrix units: `corner_matrix_unit(leaves, columns)` takes columns as bitsets (bit `i` =
  row `i`), the convention of `experiments/kaplansky_finite_drazin_seed.py` and the atlas charts.

## API (`sys.path.insert(0, <this directory>)`)

| module | contents |
|---|---|
| `leavitt` | `Elem` (normal form; `+ * ** star is_one is_zero key table()`), `OpTable` (second path), `Unit(val, inv)` (checked; `* ** inverse() order() is_identity() key`), `parse_elem`, `elem_from_json`, `S T s0 s1 t0 t1 ONE ZERO IDENTITY`, `one_plus_nilpotent`, `thompson_unit(domain, range)`, `corner_matrix_unit(leaves, columns)`, `psi2(a,b,c,d)`, `standard_units()` (`@e @u @v @w @g`), `set_dual(True)`, `dual_stats()` |
| `groupalg` | `GroupAlgebraElement(units)` (`+ * ** is_one is_zero augmentation evaluate star support`), `matmul`, `identity_matrix`, `is_identity_matrix` |
| `ca` | `CellularAutomaton(k, memory, rule)`, `compose`, `compose_is_identity`, `equal`, `garden_of_eden(tau, cells, values)`, `linear_automaton(a)`, `shift_automaton(k, h)` |
| `kl` | `reduce_word`, `invert_word`, `exponent_sum`, `verify_normal_closure(c, w, factors)` |
| `certcheck` | CLI and `check_certificate(dict)` |

Two equality paths. Path 1 is the Diamond-lemma normal form (basis: `alpha`, `beta` not both
ending in `1`). Path 2 is prefix tables: the action on sequences with a generic tail, composed
and added directly without using the rewriting rules. `set_dual(True)` recomputes every
product by path 2 and checks that no element gets two normal forms. Any disagreement raises
`PathDisagreement`, which is a bug and never an answer. `certcheck.py` runs in dual mode unless
given `--no-dual`. Searches may switch dual mode off; re-check the final certificate with it on.

## Certificate formats

Every certificate has `"type"` and an optional `"units"` object. Units are defined in order,
each one of:
`{"val": EXPR, "inv": EXPR}` (checked), `{"word": "a b^-1 c^3"}` (earlier names),
`{"thompson": {"domain": [...], "range": [...]}}`, `{"corner_matrix": {"leaves": [...], "columns": [...]}}`,
`{"one_plus_nilpotent": EXPR}`.
Built-in names: `@e`; `@u = 1+s0t1`; `@v = 1+s1t0`; `@w = s0t1+s1t0`; `@g = uv`, of order 3.
A unit word is a space-separated string of names with optional integer exponents.

| type | fields | PASS proves |
|---|---|---|
| `kaplansky-df` | `alpha`, `beta`: lists of unit words | `alpha beta = 1 != beta alpha` in `F_2[G]`. This refutes Kaplansky direct finiteness, and Gottschalk via `tau_beta` |
| `stable-finiteness` | `A`, `B`: `d x d` arrays of such lists | `AB = I != BA` over `F_2[G]` |
| `gottschalk-ca` | `alphabet`; `tau`, `sigma`: `{"memory": [words], "rule": [...]}` or `"rule_bits"`; `orphan`: `{"cells": [words], "values": [...]}` | `sigma o tau = id` (exhaustive over `N.M`) and the pattern is a Garden of Eden (exhaustive backtracking), so `tau` is injective and not surjective |
| `kl-equation` | `equation`: syllable string (`x`, `x^-1`, unit names); `coefficient`: unit word; `factors`: `[{"conj": syllables, "sign": n}]` | `c = prod h_j w^{n_j} h_j^-1` in `G * <x>`, with `c != 1` and exponent sum `!= 0`. So `w` has no solution over any overgroup, and `G` is not hyperlinear |
| `normal-closure-membership` | same | membership only (controls) |

Exit status: 0 PASS, 1 FAIL, 2 malformed. `--expect` compares against a certificate's `"expect"`
field. `examples/` holds controls, each with its expected outcome.

## Validation

`python3 selftest.py` checks:
- the Leavitt relations and the defect `t0 s0 = 1 != s0 t0`;
- 400 random products against path 2 and against the third implementation;
- the involutions `u, v, w` and the order-three `g` of `leavitt-corner-idempotent-unital-surjection`;
- the rank-three lifts of `leavitt-rank-three-unit-lift` (sums `t0` and `s0`, `u3 = v3 = g`);
- the finite Drazin seed (order 180, `T^4 = T^2`, `h = T^2`, `v = T^3`, `(Tf)^2 = 0`,
  natural evaluations), recomputed inside `F_2[R^x]`;
- the automaton identities `tau_a o tau_b = tau_{ab}`, and the Garden-of-Eden search against brute force;
- normal-closure reduction;
- the `examples/` controls.

Run 2026-09-11 (MSI job 438223): 71 checks, 0 failures.

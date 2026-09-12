# Exact certificate checker over R^x = L_(F_2)(1,2)^x (2026-09-11)

Code: `experiments/nonsofic-certificates/`. Claim: `leavitt-unit-certificate-predicates-are-decidable`.
Shared MSI copy: `/projects/standard/hsiehph/sauer354/nonsofic-certificates/current/`.
Lanes call it; they do not copy it.

## What PASS means

| certificate | checked exactly | consequence of PASS |
|---|---|---|
| `kaplansky-df` | `alpha beta = 1` and `beta alpha != 1` in `F_2[R^x]` | `F_2[R^x]` is not directly finite (Kaplansky). The linear automaton `tau_beta` is injective and not surjective (Gottschalk) |
| `stable-finiteness` | `AB = I != BA` for `d x d` matrices over `F_2[R^x]` | `F_2[R^x]` is not stably finite |
| `gottschalk-ca` | `sigma o tau = id` on all `k^|N.M|` patterns, and exhaustive backtracking finds no preimage of the orphan pattern | `tau` is injective and not surjective, so `R^x` is not surjunctive |
| `kl-equation` | `c != 1`, `eps(w) != 0`, and `c = prod h_j w^(e_j) h_j^(-1)` after free-product reduction | `w` has no solution in any overgroup, which violates Kervaire--Laudenbach, so `R^x` is not hyperlinear |

## Trust base

- Python, not a proof assistant. The kernel of trust is `leavitt.py`, `groupalg.py`, `ca.py`,
  `kl.py` and the JSON reader in `certcheck.py`.
- Two equality paths that share only the expression parser.
  - Path 1 is the normal form: reduce `t_i s_j -> delta_ij` and `s1 t1 -> 1 + s0 t0`, giving the
    basis `S[alpha]T[beta]` with `alpha, beta` not both ending in `1`.
  - Path 2 is prefix tables: for each leaf `u` of a complete prefix code, record
    `f e_(u.T) = sum e_(x.T)` for a generic tail `T`; compose and add tables directly; compare
    after merging sibling leaves. It never uses the rewriting rules. Faithfulness: `R` is
    simple, and the table of a nonzero element is nonzero.
  - In dual mode, which `certcheck.py` uses by default, every normal-form product is recomputed
    by table composition, and every group-algebra key is checked for a unique normal form.
- A third implementation, `experiments/depth_one_paired_leavitt_return_search.py` (uniform-depth
  expansion), agrees on random products.
- PASS is a machine check. Before announcing any counterexample, re-check the certificate
  independently, at minimum in dual mode on a clean copy of `origin/main`.

## Costs

- `compose_is_identity` enumerates `k^|N.M|` patterns: about a second per million in Python.
- `garden_of_eden` is exhaustive backtracking over `Omega.M`, with constraints ordered by overlap.
- `--no-dual` roughly halves the cost of long products.

## Validation run: MSI job 438223, Python 3.8.3, dual mode, 2.7 s

71 checks, 0 failures. 20313 products were cross-checked by prefix tables, and 212 group
elements were registered with unique normal forms.

- **Relations and parser.** `t_i s_j = delta_ij`; `s0 t0 + s1 t1 = 1`, also in tables;
  `t0 s0 = 1` while `s0 t0 != 1` (both paths); `S[01]T[10] = s0 s1 t0 t1`;
  `s1 t1 = 1 + s0 t0`; `(1+s0t1)(1+s1t0)` expands correctly; the ambiguous `s01` is rejected.
- **Path agreement.** On 400 random triples, normal form and tables agree on products, sums,
  associativity, distributivity, the star anti-automorphism and equality. The normal form also
  agrees with `depth_one_paired_leavitt_return_search.multiply` on 400 random products.
- **Standard units.** `x^2 = y^2 = 0`; `xy = s0t0` and `yx = s1t1`; `u, v, w` are distinct
  involutions with `u + v + w = 0`; `g = uv` has order exactly 3 and `g + g^-1 = 1`
  (`leavitt-corner-idempotent-unital-surjection`).
- **Rank-three lifts** (`leavitt-rank-three-unit-lift`). All units verify; `u1 + u2 + u3 = t0`
  and `v1 + v2 + v3 = s0` with each triple distinct; `u3 = v3 = g`. Orders: `u1` and `v1` are
  involutions, and `u2`, `v2` have no order at most 12.
- **Chart units and random words.** The chart transvections of both GL(4,2) atlas charts and
  the Thompson unit swapping `0` and `1` are involutions. 60 random words, the largest with a
  34-monomial normal form, carry correct inverses.
- **Drazin seed** (`research/artifacts/kaplansky-finite-drazin-seed-2026-09-08.json`),
  recomputed inside `F_2[R^x]` with `corner_matrix_unit` on the leaves `000, 001, 010, 011`:
  - the parent and child matrices generate a group of order 180;
  - the supports have sizes 2, 8, 28 and 76;
  - `e^2 = e` and `eT = Te = T`;
  - `T^4 = T^2`, and `e, T, T^2, T^3` are independent, so `m_T = X^4 + X^2`;
  - `h = T^2`, `v = T^3`, `h^2 = h`, `Tv = vT = h`, `hvh = v`;
  - `(Tf)^2 = 0` and `Tf != 0`;
  - the natural evaluations match the JSON.
- **Group algebra.** `[g]+[g^2]` is idempotent with `pi = 1`; `[u]+[v]+[w]` is a nonzero element
  of `ker pi` with augmentation 1. `e([u]+[v]+[w])e = 0`, which matches
  `leavitt-evaluation-kernel-hits-augmentation-one` (inside `F_2[S_3]`, `k` and `e` are central
  and `ek = 0`). `pi(t~) = t0` and `pi(s~) = s0`; `t~ s~ != 1` while `pi(t~ s~) = 1`. The star
  reverses products.
- **Automata.**
  - the shift by `g^-1` inverts the shift by `g`, and the shift has no Garden of Eden on `{e,u}`;
  - for `tau_{1+[u]}`, the pattern `(1,0)` on `{e,u}` is a Garden of Eden, `(1,1)` has a preimage,
    and the identity is not a left inverse;
  - `tau_a o tau_b = tau_{ab}` on 25 random pairs;
  - backtracking agrees with brute force on 40 random instances with alphabets 2 and 3;
  - `id o tau = tau` on 10 random automata.
- **Normal closure.** `x^-1 (x g x^-1) x = g` passes as a control; the singular equation is
  rejected as a KL certificate; `h w h^-1 h w^-1 h^-1` reduces to the empty word; random words
  times their inverses reduce to the empty word.
- **Examples.** All six controls in `examples/` give their expected outcomes.

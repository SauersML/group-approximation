# (C2) is a core: computation record (2026-09-18, w11-048)

Proof: `research/rank-five-degree-one-two-cell-configuration-is-a-core-proof.md`. Pure Python 3,
single-threaded, no dependencies.

## Reproduce

```sh
python3 verify_core.py 12     # the certificate, about 1 s
python3 cert.py 16 11         # diagnostics at R = 16 for M = 0..11 (a few minutes, grows ~2.3x per M)
```

## `verify_core.py 12` output

```
1. R0 = [('e', 0, -1), ('b', 0, 1), ('c', 3, 1), ('b', 0, -1), ('a', 0, -1), ('e', -2, 1)]
   R1 = [('b', 0, 1), ('c', 3, 1), ('b', 0, -1), ('a', 0, -1), ('a', 0, -1), ('b', 0, 1), ('c', 2, 1), ('b', -1, -1)]
2. Phi kills R0^(k), R1^(k) (checked k = -3, 0, 5; the general case is phi^k of k = 0)
3. theta = {'p': 'p', 'q': 'q', 'r': 'r', 's': 'qsr'}  psi = {'p': 'q', 'q': 'r', 'r': 'qsr', 's': 'SPR'}  gates = [['p', 'r', 's'], ['P', 'Q', 'R'], ['q', 'S']]  (train-track check passed)
4. V_{M+1} = <phi V_M, A, phi^-1 B> for M = 4..7
5. M0 = 8: rank 22 = 2*M0+6, all vertices beyond radius 12 legal, ball datum has 106 vertices;
   step on the datum: ok (dprime=12) ; rank(Z) - rank(Z') = 0 ; output datum = input datum (fixed point)
   direct: rank V_M = 2M+6 for M < M0.  CONCLUSION: rank V_M = 2M+6 for all M >= 0.

```

## `cert.py 16 11` output (robustness check, not needed by the proof)

`V` is the vertex count of the direct fold of `θ(V_M)`, and `ball size` is `|Δ_16|`. The
"prediction" compares `step(Δ(X_{M-1}))` with `Δ(X_M)`. It fails for `M ≤ 4`, as expected, since
the shift Lemma 3.1 needs `M ≥ 4`.

```
theta {'p': 'p', 'q': 'q', 'r': 'r', 's': 'qsr'} theta^-1 {'p': 'p', 'q': 'q', 'r': 'r', 's': 'QsR'} psi {'p': 'q', 'q': 'r', 'r': 'qsr', 's': 'SPR'}
M 0 V 60 rank 6 want 6 legal beyond R True ball size 42 step ok (dprime=36) rank drop 0 moves
M 1 V 66 rank 8 want 8 legal beyond R True ball size 48 step ok (dprime=36) rank drop 0 moves
   step prediction matches actual datum: False
M 2 V 75 rank 10 want 10 legal beyond R True ball size 57 step ok (dprime=36) rank drop 0 moves
   step prediction matches actual datum: False
M 3 V 78 rank 12 want 12 legal beyond R True ball size 60 step ok (dprime=36) rank drop 0 moves
   step prediction matches actual datum: False
M 4 V 86 rank 14 want 14 legal beyond R True ball size 70 step ok (dprime=20) rank drop 0 moves
   step prediction matches actual datum: False
M 5 V 178 rank 16 want 16 legal beyond R True ball size 103 step ok (dprime=20) rank drop 0 moves
   step prediction matches actual datum: True
M 6 V 394 rank 18 want 18 legal beyond R True ball size 121 step ok (dprime=20) rank drop 0 moves
   step prediction matches actual datum: True
M 7 V 898 rank 20 want 20 legal beyond R True ball size 132 step ok (dprime=20) rank drop 0 moves
   step prediction matches actual datum: True
M 8 V 2072 rank 22 want 22 legal beyond R True ball size 140 step ok (dprime=20) rank drop 0 fixed point
   step prediction matches actual datum: True
M 9 V 4804 rank 24 want 24 legal beyond R True ball size 140 step ok (dprime=20) rank drop 0 fixed point
   step prediction matches actual datum: True
M 10 V 11158 rank 26 want 26 legal beyond R True ball size 140 step ok (dprime=20) rank drop 0 fixed point
   step prediction matches actual datum: True
M 11 V 25932 rank 28 want 28 legal beyond R True ball size 140 step ok (dprime=20) rank drop 0 fixed point
   step prediction matches actual datum: True
```

## Direct window folds without the train track (`run5.py`, discovery only)

`python3 run5.py 1 M` directly folds an earlier window family, `⟨C, E, φE, φ^j A, φ^j B⟩`,
in the original basis. Every fold was injective (rank = number of generators). The
generator length grows by about 2.3x per step (`maxlen` 16, 38, 90, 210, 488, … for `M = 0, 1, …`),
so no direct check covers all `M`. That is why the certificate is used. `verify_core.py` makes
the direct checks only for `M < 8`.

## Files

- `fbc.py`: word arithmetic, `φ`, `φ⁻¹`, `tofib` (fibre normal form), and the relator check.
- `fold2.py`: Stallings folding with union-find (`SG`).
- `tt2.py`: `θ` and `ψ = θφθ⁻¹`, both asserted.
- `cert.py`: gates, the train-track assertion, `Vgens`, the ball datum and the step map.
- `verify_core.py`: the end-to-end replay of every finite fact in the proof.
- `tt_search.py`: search for a rose train track among Nielsen conjugates of `φ` (depth 2), which
  found `θ`.
- `run5.py`: direct window folds.

# (C2) is admissible: unimodularity record (2026-09-18, w11-048)

This part supports `admissible-ab-nonzero-two-cell-base-exists`.

## Reproduce

Each command runs single-threaded in under 2 seconds.

    python3 verify_unimodular.py     # self-contained check of sum_z c_z d_z = 1 in ZG
    python3 certuni.py               # rebuilds d from the ZF/J solution and checks it again
    python3 solveQ.py 3              # exact rational solve of the pruned system, radius 3
    python3 searchJ.py 1009 0:2 0:3  # rank test mod 1009 of the pruned system
    python3 gamma2.py                # the group Gamma'' = <t,x,y | R_0, R_1> of (A5)

## `verify_unimodular.py` output

    phi(u_0) = w and phi(u_1) = g w g^-1 in F(x,y), with g = x^-1 y
    c_a has 3 terms, d_a has 4 terms
    c_b has 6 terms, d_b has 1 terms
    c_c has 3 terms, d_c has 1 terms
    c_d has 6 terms, d_d has 3 terms
    c_e has 2 terms, d_e has 7 terms
    sum_x c_x d_x = {('', 0): 1}
    CONCLUSION: c is unimodular over ZG, so (C2) is admissible (pd I_{G/H} <= 1)

## How the certificate was found

The search reduces the problem to the free group ring:
- `c_a = α_0 + y α_1` with `α_1` a unit, so `y ≡ τ = −α_0 α_1⁻¹` modulo `c·ZG`.
- `c_e` gives `y⁻¹` modulo `c·ZG` in the same way.
- So `N = ZG / c·ZG ≅ ZF / J`, with `F = F_4` and `J` the smallest right ideal that is stable
  under `T(h) = τ φ⁻¹(h)` and contains the reductions of `c_b, c_c, c_d` and of `T T⁻¹ − 1`
  (`redJ.py`).

`searchJ.py` asks whether `1 ∈ J` using generators `M^k(g), M^k(T g)` times the words of the
radius-`R` ball in `F_4`, where `M = T²` modulo `J`. It prunes rows met by one column and then
compares ranks mod `p`:

    p 1009 K 0 R 2 (650, 16, 53, 'no', 16)
    p 1009 K 0 R 3 (4570, 132, 391, 'SOLVABLE', 132)

The runs K = 1, 2, 3 at R = 3 and K = 0, 1, 2 at R = 4 are also solvable. `solveQ.py 3` solves
the K = 0, R = 3 system exactly over Q. The solution has 9 nonzero coefficients, all `±1`:

    exact solution True
    9 nonzero
    ['-1', '1']

`certuni.py` carries each generator with its expression `Σ_z c_z E_z`, pulls the solution back
to `d ∈ ZG^5`, and prints `CERTIFICATE True`. The words of `d` in `verify_unimodular.py` are
this `d`, rewritten in `x, y`.

## `gamma2.py` (the route of (A5))

`R_0` has length 391 and `t`-exponent 1. `R_1` has length 350 and `t`-exponent 2. Setting
`t = 1` returns `w` and a conjugate of `w`. GAP gives `AbelianInvariants(Γ'') = [0, 0]`, which
equals that of `G`, as it must since `N = ⟨⟨t⟩⟩` is perfect.

## Files (unimodularity)

- `verify_unimodular.py`: the self-contained certificate check.
- `zg.py`: `ZG` arithmetic in the normal form `u y^m`, and Fox derivatives.
- `redJ.py`: the reduction `N ≅ ZF/J`, with `τ`, `T`, `T⁻¹` and the generators of `J`.
- `searchJ.py`: the pruned rank test mod `p`.
- `solveQ.py`: the exact rational solve.
- `certuni.py`: the back-translation to `d` and the check.
- `gamma2.py`: the relator-slide group `Γ''`.
- `a5check.py`: the homomorphisms `Γ'' → A_5` with `t ≠ 1`.

## `a5check.py` output (A6)

    18 homs Gamma'' -> A5 with t != 1 (x fixed up to conjugacy)
    t,x,y = ((3, 1, 0, 2, 4), (0, 2, 1, 4, 3), (1, 3, 0, 4, 2))

GAP `GQuotients(Γ'', H)` gives the following, with `t ≠ 1` in every quotient found:

| `H` | epimorphisms | with `t ≠ 1` |
|---|---|---|
| `S_4` | 0 | 0 |
| `A_5` | 2 | 2 |
| `S_5` | 5 | 5 |
| `PSL(2,7)` | 2 | 2 |
| `A_6` | 0 | 0 |

Coset enumeration of `⟨x,y⟩` in `Γ''` ran out of memory at 2 GB. That was consistent with an
infinite index, and the finite quotients then showed `t ≠ 1`.

## `solvcheck.py` output (perfectness sanity check)

Every homomorphism of `Γ''` to a solvable group must kill `t`, because `N = ⟨⟨t⟩⟩` is perfect.
This is the check that the slide construction is right:

    S4 order 24 homs 144 with t != 1: 0
    D5 order 10 homs 40 with t != 1: 0
    D6 order 12 homs 72 with t != 1: 0
    Z3wrZ2 (deg 6) order 18 homs 162 with t != 1: 0
    AGL(1,5) order 20 homs 140 with t != 1: 0

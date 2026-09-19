# Rose mapping torus of the (C2) pair: canonical-cycle test

These are the computations behind `research/c2-rose-mapping-torus-has-no-one-lift-core.md`, parts
(T2)–(T4). The scripts import `fbc.py`, `fold2.py` and `cert.py` from
`experiments/c2-free-by-cyclic-2026-09-18/`.

## Files

- `verify_cycle.py` checks (T2) and (T3).
  - It builds the chain `z` of the loops `−[Q x_2] + [X_2 s x_2] − 2[pQ] − 2[qR]` in `Γ_N`, and the
    chain of their `φ`-images.
  - It merges prefix cosets only through exact memberships `φ^k(ab^{-1}) ∈ T_M ⊂ N`, with `|k| ≤ 3`.
  - It then compares the two chains, and checks the `S_9` certificate and the pushforward to `X_L`.
- `bases.py` does (T4). It is a breadth-first search over elementary Nielsen moves on the fibre
  basis, and applies the index-9 pushforward test to each basis.
- `srq.g` is a GAP low-index search. It finds the index-9 representation used as the certificate.

## Commands and outputs

Run `python3 verify_cycle.py ../c2-free-by-cyclic-2026-09-18 8`. It takes about 2 s and prints:

```
coset classes used: 4  of 50 representatives
z = {('r', 'Q'): -2, ('s', 'Q'): 2, ('p', 'S'): 1, ('r', 'S'): 1, ('s', 'S'): -1, ('p', ''): -2, ('r', ''): 2}
phi-invariant (f_N# z = z): True
letter sums: {'p': -1, 'q': 0, 'r': 1, 's': 1}
lifts of the P-cell in supp z: [(('p', 'S'), 1), (('p', ''), -2)]
Sr in some window (would merge the two P-lifts): False
points fixed by pi(H): [4]   image of that point under pi(y x^-1 y^-1 x): [2]
z pushed to X_L: {('r', 1): -2, ('s', 1): 2, ('p', 2): 1, ('r', 2): 1, ('s', 2): -1, ('p', 4): -2, ('r', 4): 2}
P-cell coefficients in X_L: {('p', 2): 1, ('p', 4): -2}
```

How to read the output:
- The key `(e, a)` means the lift of the 2-cell `σ_e` at the vertex `Na`. Here `''`, `S` and `Q`
  stand for `1`, `s⁻¹` and `q⁻¹`.
- A key `(e, i)` in `X_L` means the lift over the point `i` of the index-9 cover.
- The line `Sr in some window: False` is not used in the proof. Distinctness comes from the `S_9`
  line: the points `4`, `2` and `1` are pairwise distinct.

Run `python3 bases.py ../c2-free-by-cyclic-2026-09-18 3`. It takes about 20 s and prints:

```
bases tested: 57725  survivors of the index-9 test: 0
```

With depth 2 it prints `bases tested: 1777  survivors of the index-9 test: 0`.

Run `gap -q srq.g`. It finds a subgroup of index 9, with `|π(G)| = 362880` and `|π(H)| = 40320`, so
`π(G) = S_9` and `π(H) = S_8`. It uses no SmallGroups library, only
`LowIndexSubgroupsFpGroup` and `FactorCosetAction`. The proof does not depend on GAP. The
representation `x ↦ (3,4,6,5)(7,8,9)`, `y ↦ (1,2,3)(5,7,8)` is hard-coded in `verify_cycle.py` and
`bases.py`, and `verify_cycle.py` checks the relator and the fixed point of `H` independently.

## Scope

- (T4) covers exactly the listed bases, meaning those within three elementary Nielsen moves of
  `(p,q,r,s)`.
- It says nothing about roses outside that ball, about non-rose marked graphs, or about other
  fibrations of `G`.

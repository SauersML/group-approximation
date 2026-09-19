# (C2): primitive-class tests for c_H (w15-048, 2026-09-19)

Supports `research/c2-fibred-realizations-reduce-to-a-primitive-class.md`, parts (R5) and (R6).

## Set-up

`common.py` imports `fbc.py` from the w11 experiment `experiments/c2-free-by-cyclic-2026-09-18`,
found through `W11DIR` or the sibling directory. It defines:
- `U`, a word for `c_H`: `−[Q x_2] + [X_2 s x_2] − 2[pQ] − 2[qR]`;
- the fibre generators `a_0, b_0, c_0, e_0` of `N`;
- the index-9 action `x ↦ (3,4,6,5)(7,8,9)`, `y ↦ (1,2,3)(5,7,8)` of the rose node, with base
  point 4.

## (R5) Index 9: `J = L ∩ F_4`

```
$ python3 coker.py        # or twisted.py, which also runs it
index 9 rank H_1(J) = 28  rank im H_1(N) = 27  coker invariants (non-1): [0]
c_H in H_1(J): gcd of coordinates = 1  nonzero: {(1,'r'): -2, (1,'s'): 2, (2,'r'): 1, (2,'s'): -1, (4,'r'): 2}
$ python3 twisted.py
psi = [0 x14, 1, 0,0,0, 1, 0,0, 1, 0, 1, 0,0,0,0]      # the unique character of J killing N
  nonzero entries of c(t): 5   gcd over Q[t]: 1
  c(t) = {(1,'r'): -2, (1,'s'): 2, (2,'r'): 1, (2,'s'): -1, (4,'r'): 2}
   mod p gcd: t**200  (p = 2,3,5,7; t^200 is the unit used to clear negative powers)
```

The printed outputs above are abridged.

- `im H_1(N)` is the `φ^{±1}`-closure of the classes of `a_0, b_0, c_0, e_0`, and it is saturated
  of corank 1.
- `c_H` is primitive in `H_1(J)`.
- The `Z`-twisted Fox vector is constant, with an entry `1`, so it is unimodular.

By Lemma B, these are the conditions that an `F_4`-primitive `q ∈ N` with `[q] = c_H` would impose
on `J`, and all of them hold.

## (R6) Searches for an F_4-primitive representative

The Whitehead minimiser is `whitehead.py`. It uses type-II Whitehead automorphisms and cyclic
reduction, and a class is primitive iff its minimal length is 1. Self-test:
`python3 whitehead.py` prints `self-test ok s pqPQ`.

`search.py` confirms, in `H_1(J)`, the decomposition `c_H = 2[rP] + 2[QsRq] + [SpSrs]` and that
`pQ, qR, rS, F_1, F_2, F_3` fix the base point.

```
$ python3 search.py check
check ok: BASEN fix 4; 2[F2] + 2[F3] + [F1] = c_H in H_1(J)
$ python3 search.py 0                 # all 30 orderings of F1 F2 F2 F3 F3
tested 30 best minimal length 11 ('QsRqSpSrsrPQsRqrP', 'qRQspSSPrrq')
$ python3 search.py 2 3000            # N-conjugators of length <= 2 (seed 1)
tested 2901 best minimal length 11 ('QsRqrPSpSrsQsRqrP', 'QRsqPSSprrQ')
$ python3 climb.py 20 400 1           # 20 restarts x 400 commutator moves in q0[N,N]
overall best 12 rPrPQsRsRqSpSrs
```

No `F_4`-primitive representative was found. The best Whitehead-minimal cyclic length is 11. The
hill-climb never improved on its starting word.

This is heuristic evidence only. The coset `q_0[N,N]` is infinite, and neither search is
exhaustive in any sense.

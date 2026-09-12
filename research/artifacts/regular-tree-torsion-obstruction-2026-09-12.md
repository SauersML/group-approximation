# Regular-tree torsion obstruction for the self-similar route to fp residually finite Boone–Higman

Lane `bh-fp-rf-self-similar`, 2026-09-12. This is the supporting artifact for
`regular-tree-torsion-orders-have-primes-at-most-degree` and
`cycle-transposition-lef-group-has-no-regular-tree-action`.

## What landed and why

The open claim `every-fp-rf-group-embeds-in-fp-self-similar-group` asks for a
finitely presented self-similar overgroup of every finitely presented residually
finite group. Its condition (N1), residual `W_d`-ness, had been recorded as a
screen with no known violator. This artifact records the following.

1. **Torsion form of (N1).** A finite-order automorphism of `T_d` has an order
   whose prime factors are all at most `d`. So one element of large prime order
   rules out every regular tree.
2. **An explicit residually finite violator with easy word problem.** The group
   `Gamma = <sigma, tau> <= prod_(n>=3) Sym(Z/n)`, with `sigma` the rotations and
   `tau` the transposition `(0 1)`, has these properties:
   - it is residually finite;
   - its word problem is solvable in polynomial time;
   - it contains `Alt(p)`, supported on the single coordinate `p`, for every
     prime `p >= 5`.

   So it embeds in no `Aut(T_d)`.
3. **The precise remaining step.** An fp residually finite group with torsion of
   infinitely many prime orders would refute the embedding claim. One source of
   such a group would be a finitely presented residually finite overgroup of
   `Gamma`, which a positive answer to the Kharlampovich–Myasnikov–Sapir
   residually finite Higman embedding question (arXiv:1204.6506 §1.1.7) would
   supply. So the self-similar route to `fp-residually-finite-boone-higman` and
   a residually finite Higman embedding theorem cannot both hold.

## Sources read in this session

- Zaremsky, arXiv:2405.09722v2, the full text (pdftotext). Definition 2.1
  requires only `G <= Aut(T_d)` with every section of every element in `G`; no
  transitivity or finite-state condition. Theorem 1.1, Citations 2.3 and 2.4,
  Corollary 4.5 and Example 4.7 were checked against that text.
- Kharlampovich–Myasnikov–Sapir, arXiv:1204.6506, the full text (pdftotext).
  - §1.1.7 poses the residually finite Higman embedding question; it is quoted
    in `rf-higman-embedding-for-decidable-groups`.
  - §1.2: fp RF groups have solvable word problem (McKinsey).
  - The groups `G(M)` are a split extension of an elementary abelian group of
    prime exponent by a metabelian group (§1.6, and §4: Lemma 4.14, Theorem 4.17).
- Kassabov–Nikolov, arXiv:math/0602446. Only grep-level reading: Theorem 2,
  Questions 5 and 6, Theorem 12, §4.1 (`EL_3`).

No literature search was possible: the session's web search budget was
exhausted. So whether a finitely presented residually finite group with
unbounded prime torsion is already known was **not checked**.

## Machine check (MSI, python3/3.10.9_anaconda2023.03_libmamba, numpy + sympy)

The script `gamma_check.py` below has md5 `d023da5a0e5b7bcf19ab3ea79545bd00`
both locally and on MSI. It was run in `/scratch.global/sauer354/bhfprf`. It
checks three things:

1. **Support of `g_p`.** For primes `5 <= p <= 31`, `g_p = [c_(p+1), c_(p-1)]`
   is supported exactly on coordinate `p`, and is even there.
   - Coordinates up to `4l+4` are checked directly, where `l` is the word length.
   - All larger coordinates are covered through `e(g_p) = 0` and the fixed
     `Z`-model window, by step 2 of `cycle-transposition-lef-group-proof`.

   So this is a certificate for all coordinates at those primes.
2. **Normal closure.** For `5 <= p <= 23`, rotation and transposition generate
   `Sym(Z/p)`, and the normal closure of `g_p` has order `p!/2`.
3. **Word-problem criterion.** On 3,023 words (structured commutators plus
   3,000 random words of length at most 18), the criterion of step 2 was
   compared against brute force over coordinates `3..240`: 165 were trivial and
   there were 0 mismatches.

Output (EXIT=0):

```text
(1) support of g_p, certified on all blocks: blocks 3..4l+4 checked directly,
    larger blocks through e(g_p) = 0 and the Z-model window (step 2 of the proof)
  p= 5 len=  96 blocks<=   388: support=[5] e=0:True Zwindow fixed:True even:True -> OK
  p= 7 len= 128 blocks<=   516: support=[7] e=0:True Zwindow fixed:True even:True -> OK
  p=11 len= 192 blocks<=   772: support=[11] e=0:True Zwindow fixed:True even:True -> OK
  p=13 len= 224 blocks<=   900: support=[13] e=0:True Zwindow fixed:True even:True -> OK
  p=17 len= 288 blocks<=  1156: support=[17] e=0:True Zwindow fixed:True even:True -> OK
  p=19 len= 320 blocks<=  1284: support=[19] e=0:True Zwindow fixed:True even:True -> OK
  p=23 len= 384 blocks<=  1540: support=[23] e=0:True Zwindow fixed:True even:True -> OK
  p=29 len= 480 blocks<=  1924: support=[29] e=0:True Zwindow fixed:True even:True -> OK
  p=31 len= 512 blocks<=  2052: support=[31] e=0:True Zwindow fixed:True even:True -> OK
(2) normal closure of g_p in Sym(Z/p) = <sigma_p, tau_p>
  p= 5: <sigma,tau> = Sym(p): True; |normal closure| = p!/2: True -> OK
  p= 7: <sigma,tau> = Sym(p): True; |normal closure| = p!/2: True -> OK
  p=11: <sigma,tau> = Sym(p): True; |normal closure| = p!/2: True -> OK
  p=13: <sigma,tau> = Sym(p): True; |normal closure| = p!/2: True -> OK
  p=17: <sigma,tau> = Sym(p): True; |normal closure| = p!/2: True -> OK
  p=19: <sigma,tau> = Sym(p): True; |normal closure| = p!/2: True -> OK
  p=23: <sigma,tau> = Sym(p): True; |normal closure| = p!/2: True -> OK
(3) word-problem criterion versus brute force on blocks 3..240
  3023 words checked, 165 trivial, 0 mismatches -> OK
ALL_OK
```

The proofs in the Cairn routes do not depend on this check; it is independent
confirmation of the support computation and of the word-problem criterion.

## Script

```python
#!/usr/bin/env python3
"""Machine check for `cycle-transposition-lef-group-has-no-regular-tree-action`.

Gamma = <sigma, tau> <= prod_{n>=3} Sym(Z/n), sigma_n: x -> x+1, tau_n = (0 1).
Letters: 's' = sigma, 'S' = sigma^-1, 't' = tau. A word x_1...x_l is the composition
x_1 o ... o x_l, so the rightmost letter acts first.
"""
import math
import random

import numpy as np
from sympy import primerange
from sympy.combinatorics import Permutation, PermutationGroup


def winv(w):
    return ''.join({'s': 'S', 'S': 's', 't': 't'}[c] for c in reversed(w))


def comm(a, b):
    return a + b + winv(a) + winv(b)


def c_k(k):
    return comm('t', 's' * k + 't' + 'S' * k)


def g_p(p):
    return comm(c_k(p + 1), c_k(p - 1))


def support(w, nlo, nhi):
    """Blocks n in [nlo, nhi] on which w acts nontrivially."""
    ns = np.arange(nlo, nhi + 1, dtype=np.int64)
    mods = np.repeat(ns, ns)
    pts = np.concatenate([np.arange(n, dtype=np.int64) for n in ns])
    pos = pts.copy()
    for c in reversed(w):
        if c == 's':
            pos = (pos + 1) % mods
        elif c == 'S':
            pos = (pos - 1) % mods
        else:
            pos = np.where(pos == 0, 1, np.where(pos == 1, 0, pos))
    block_index = np.repeat(np.arange(len(ns)), ns)
    return [int(ns[i]) for i in np.unique(block_index[pos != pts])]


def block_perm(w, n):
    pos = np.arange(n, dtype=np.int64)
    for c in reversed(w):
        if c == 's':
            pos = (pos + 1) % n
        elif c == 'S':
            pos = (pos - 1) % n
        else:
            pos = np.where(pos == 0, 1, np.where(pos == 1, 0, pos))
    return [int(v) for v in pos]


def zmodel_fixes_window(w):
    l = len(w)
    xs = np.arange(-l - 1, l + 2, dtype=np.int64)
    pos = xs.copy()
    for c in reversed(w):
        if c == 's':
            pos = pos + 1
        elif c == 'S':
            pos = pos - 1
        else:
            pos = np.where(pos == 0, 1, np.where(pos == 1, 0, pos))
    return bool(np.all(pos == xs))


def exp_sum(w):
    return w.count('s') - w.count('S')


def criterion(w):
    l = len(w)
    return exp_sum(w) == 0 and not support(w, 3, 4 * l + 4) and zmodel_fixes_window(w)


ok = True

print("(1) support of g_p, certified on all blocks: blocks 3..4l+4 checked directly,")
print("    larger blocks through e(g_p) = 0 and the Z-model window (step 2 of the proof)")
for p in primerange(5, 32):
    w = g_p(p)
    l = len(w)
    sup = support(w, 3, 4 * l + 4)
    e0 = exp_sum(w) == 0
    zfix = zmodel_fixes_window(w)
    even = Permutation(block_perm(w, p)).is_even
    good = sup == [p] and e0 and zfix and even
    print(f"  p={p:2d} len={l:4d} blocks<= {4*l+4:5d}: support={sup} e=0:{e0} Zwindow fixed:{zfix} even:{even} -> {'OK' if good else 'FAIL'}")
    ok &= good

print("(2) normal closure of g_p in Sym(Z/p) = <sigma_p, tau_p>")
for p in primerange(5, 24):
    S = PermutationGroup([Permutation(block_perm('s', p)), Permutation(block_perm('t', p))])
    full = S.order() == math.factorial(p)
    N = S.normal_closure(PermutationGroup([Permutation(block_perm(g_p(p), p))]))
    good = full and 2 * N.order() == S.order()
    print(f"  p={p:2d}: <sigma,tau> = Sym(p): {full}; |normal closure| = p!/2: {2*N.order()==S.order()} -> {'OK' if good else 'FAIL'}")
    ok &= good

print("(3) word-problem criterion versus brute force on blocks 3..240")
random.seed(20260912)
tests = [c_k(k) for k in range(0, 14)]
tests += [comm(c_k(k), c_k(j)) for k in range(2, 17) for j in range(2, 17)]
tests += ['tt', 'sS', 'Ss', 'ssSS', 'tsSt', comm('t', 'sssss' + 't' + 'SSSSS')]
for _ in range(3000):
    l = random.randint(1, 18)
    tests.append(''.join(random.choice('sSt') for _ in range(l)))
mism = ntriv = checked = 0
for w in tests:
    if 4 * len(w) + 4 > 240:
        continue
    checked += 1
    brute = not support(w, 3, 240)
    crit = criterion(w)
    ntriv += brute
    if brute != crit:
        mism += 1
        print("  MISMATCH", w, brute, crit)
print(f"  {checked} words checked, {ntriv} trivial, {mism} mismatches -> {'OK' if mism == 0 else 'FAIL'}")
ok &= mism == 0

print("ALL_OK" if ok else "SOMETHING_FAILED")
```

#!/usr/bin/env python3
"""Check the compressed special words of the distorted Boone group H_M.

H_M = < G_M, s | [s,t] = [s,x] = 1, s^-1 y s = y^m >.  The configuration of the
compiled machine on input n is f(n) = (A, encList m front(n)) with

    front(n) = [c_cons] + reverse(trNat n)   (trNat = binary digits, LSB first)

(Lean: IndexMapComputable.map_enc_trInit, encCfg_initQCfg,
TrNatRecurrence.trNat_eq_cons).  The proof node claims:

 (1) Horner word  Y(d_0..d_N) = y^d_0 s^-1 y^d_1 s^-1 ... s^-1 y^d_N s^N
     represents y^(sum d_i m^i) in <y, s | s^-1 y s = y^m> = BS(1,m);
 (2) for the input encoding n(v) whose LSB-first bits are
         1^e 0 beta(v_0) ... beta(v_{l-1}) 1
     the word Y(front(n(v))) equals, letter for letter,
         y^c_cons s^-1 y^c_1 . phi(v)^-1 . s^-1 y^c_0 (s^-1 y^c_1)^e . s^(e+2) . psi(v)
     with phi(a) = rho(a)^-1, rho(a) = prod over reversed bits of beta(a) of s^-1 y^c_bit,
     psi(a) = s^k: a pattern in two free-monoid homomorphisms;
 (3) the special word has length O(m (e + k l)), while the uncompressed
     Boone word x^a y^b ... has length about m^(e + k l).

(1) is checked in the faithful representation y -> [[1,1],[0,1]],
s -> [[1/m,0],[0,1]] of BS(1,m).  (2) is checked as an equality of free words
after free reduction.
 (4) the most-significant-first Horner word: y^B = s^-(N+1) Z(v) in BS(1,m), with
     Z(v) = prod_{j=N..0} s y^d_j = C1 . phi(v) . C2 letter for letter, phi a single
     free-monoid homomorphism with no inverses.  Since s commutes with t and x in
     H_M, u^-1 t u = Z^-1 (x^-a t x^a) Z, so the halting word is a pattern in ONE
     homomorphism with four occurrences.
Single-threaded, a few seconds.
"""
from fractions import Fraction
import random

def mat_mul(a, b):
    return [[a[0][0]*b[0][0] + a[0][1]*b[1][0], a[0][0]*b[0][1] + a[0][1]*b[1][1]],
            [a[1][0]*b[0][0] + a[1][1]*b[1][0], a[1][0]*b[0][1] + a[1][1]*b[1][1]]]

def gen_mats(m):
    y = [[Fraction(1), Fraction(1)], [Fraction(0), Fraction(1)]]
    yi = [[Fraction(1), Fraction(-1)], [Fraction(0), Fraction(1)]]
    s = [[Fraction(1, m), Fraction(0)], [Fraction(0), Fraction(1)]]
    si = [[Fraction(m), Fraction(0)], [Fraction(0), Fraction(1)]]
    return {('y', 1): y, ('y', -1): yi, ('s', 1): s, ('s', -1): si}

def evaluate(word, m):
    g = gen_mats(m)
    acc = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]]
    for letter in word:
        acc = mat_mul(acc, g[letter])
    return acc

def power(gen, e):
    return [(gen, 1 if e >= 0 else -1)] * abs(e)

def inv(word):
    return [(g, -e) for (g, e) in reversed(word)]

def free_reduce(word):
    out = []
    for letter in word:
        if out and out[-1][0] == letter[0] and out[-1][1] == -letter[1]:
            out.pop()
        else:
            out.append(letter)
    return out

def horner_word(digits):
    w = []
    for i, d in enumerate(digits):
        if i > 0:
            w += power('s', -1)
        w += power('y', d)
    w += power('s', len(digits) - 1)
    return w

def horner_value(digits, m):
    return sum(d * m**i for i, d in enumerate(digits))

def tr_nat(n):
    """Mathlib trNat read through its halving recurrence: LSB first."""
    bits = []
    while n > 0:
        bits.append(n % 2)
        n //= 2
    return bits

def encode_input(v, e, k, beta):
    """n(v): LSB-first bits 1^e 0 beta(v_0) ... beta(v_{l-1}) 1."""
    bits = [1] * e + [0]
    for a in v:
        bits += beta[a]
    bits += [1]
    return sum(b << i for i, b in enumerate(bits)), bits

def check_one(rng):
    m = rng.randint(2, 9)
    c_cons, c0, c1 = (rng.randint(1, m - 1) for _ in range(3))
    alphabet = list(range(rng.randint(1, 4)))
    k = max(1, (len(alphabet) - 1).bit_length())
    beta = {a: [(a >> j) & 1 for j in range(k)] for a in alphabet}
    e = rng.randint(0, 5)
    v = [rng.choice(alphabet) for _ in range(rng.randint(0, 6))]
    n, bits = encode_input(v, e, k, beta)
    assert tr_nat(n) == bits, (n, bits)
    code = {0: c0, 1: c1}
    front = [c_cons] + [code[b] for b in reversed(tr_nat(n))]
    b_val = horner_value(front, m)
    # (1) the Horner word represents y^b in BS(1,m)
    Y = horner_word(front)
    M = evaluate(Y, m)
    assert M == [[1, b_val], [0, 1]], (m, front, M)
    # (2) the pattern form, letter for letter
    def rho(a):
        w = []
        for bit in reversed(beta[a]):
            w += power('s', -1) + power('y', code[bit])
        return w
    phi = lambda word: sum((inv(rho(a)) for a in word), [])
    psi = lambda word: power('s', k * len(word))
    pattern = (power('y', c_cons) + power('s', -1) + power('y', c1)
               + inv(phi(v))
               + power('s', -1) + power('y', c0)
               + sum((power('s', -1) + power('y', c1) for _ in range(e)), [])
               + power('s', e + 2) + psi(v))
    assert free_reduce(pattern) == free_reduce(Y), (v, e, k)
    # (4) one-homomorphism form (MSB-first Horner): y^B = s^-(N+1) Z with
    #     Z = prod_{j=N..0} s y^d_j = C1 . phi1(v) . C2,
    #     phi1(a) = prod over the bits of beta(a), LSB first, of s y^c_bit.
    Z = sum((power('s', 1) + power('y', d) for d in reversed(front)), [])
    MZ = evaluate(power('s', -(len(front))) + Z, m)
    assert MZ == [[1, b_val], [0, 1]], (m, front, MZ)
    phi1 = lambda word: sum((sum((power('s', 1) + power('y', code[bit]) for bit in beta[a]), [])
                             for a in word), [])
    C1 = sum((power('s', 1) + power('y', c1) for _ in range(e)), []) + power('s', 1) + power('y', c0)
    C2 = power('s', 1) + power('y', c1) + power('s', 1) + power('y', c_cons)
    assert free_reduce(C1 + phi1(v) + C2) == free_reduce(Z), (v, e, k)
    # (3) sizes
    N = len(front) - 1
    assert N == e + 2 + k * len(v)
    return len(Y), b_val

def main():
    rng = random.Random(20260917)
    trials = 3000
    worst_ratio = 0.0
    for _ in range(trials):
        length, b_val = check_one(rng)
        worst_ratio = max(worst_ratio, length)
    print(f"checked {trials} random (m, codes, alphabet, e, v): Horner identity in BS(1,m) "
          f"and pattern form both hold; MSB-first Horner identity and one-homomorphism form Z = C1 phi(v) C2 hold")
    # size comparison on a fixed machine-sized example
    m, c = 7, 3
    for l in (4, 16, 64):
        front = [c] * (l + 1)
        compressed = len(horner_word(front))
        uncompressed = horner_value(front, m)  # the exponent b, i.e. |y^b|
        print(f"digits={l+1:3d}  compressed |Y| = {compressed:5d}   uncompressed |y^b| = {uncompressed:.3e}")

if __name__ == "__main__":
    main()

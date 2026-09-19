#!/usr/bin/env python3
"""Swapped J-copies: exact homogeneous kernel 0, approximate kernel map of rank n.

For a J-copy F_2^n \\ 0 (one homogeneous equation per line) we perform the n
greedy swaps of the proof of Lemma J' in
research/exact-kernel-rank-does-not-exclude-flip-violators-proof.md and check:

  A. every swap pair uses 6 fresh points, a_i+b_i+c_i+d_i = e_i, degrees are
     unchanged (regularity), and the 2n new triples are distinct non-lines;
  B. GF(2) rank of the swapped homogeneous system = 2^n - 1 (kernel 0);
     control: the unswapped J-copy has kernel dimension exactly n;
  C. line redundancy: the J-copy with the 2n swapped-out lines deleted still
     has kernel dimension exactly n (only linear functions), and so does the
     J-copy with 2n random lines deleted (trials);
  D. Phi(v) = v kills every equation of the swapped copy except exactly the 2n
     new triples; prints the dirty fraction rho = 2n / #equations.

Prints ALL PASS and exits 0 on success.
"""
import random
import sys

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def lines_of(n):
    pts = range(1, 2 ** n)
    out = set()
    for u in pts:
        for v in pts:
            if u < v and (u ^ v) > v:
                out.add((u, v, u ^ v))
    return sorted(out)


def rank_gf2(rows):
    piv = {}
    r = 0
    for row in rows:
        while row:
            h = row.bit_length() - 1
            if h in piv:
                row ^= piv[h]
            else:
                piv[h] = row
                r += 1
                break
    return r


def row(tri):
    m = 0
    for p in tri:
        m ^= 1 << (p - 1)
    return m


def greedy_swaps(n, rng=None):
    used = set()
    swaps = []
    pts = list(range(1, 2 ** n))
    for i in range(n):
        e = 1 << i
        cand_q = [q for q in pts if q not in used and (q ^ e) not in used and q != e]
        if rng:
            rng.shuffle(cand_q)
        done = False
        for q in cand_q:
            p = q ^ e
            # line l = {a, b, q} with a + b = q, all points fresh, avoiding p
            for a in pts:
                b = a ^ q
                if a >= b or a in used or b in used or p in (a, b) or a == q or b == q:
                    continue
                blocked = used | {a, b, q}
                for c in pts:
                    d = c ^ p
                    if c >= d or c in blocked or d in blocked or c == p or d == p:
                        continue
                    swaps.append(((a, b, q), (c, d, p)))
                    used |= {a, b, q, c, d, p}
                    done = True
                    break
                if done:
                    break
            if done:
                break
        if not done:
            return None
    return swaps


def run(n, trials):
    L = lines_of(n)
    V = 2 ** n - 1
    check(len(L) == V * (V - 1) // 6, f"n={n}: line count")
    base_rank = rank_gf2([row(t) for t in L])
    check(V - base_rank == n, f"n={n}: J-copy kernel dim {V - base_rank} != n")

    sw = greedy_swaps(n)
    if sw is None:
        print(f"n={n}: greedy swap selection fails (proof needs n >= 7)")
        return n >= 7 and FAIL.append(f"n={n}: greedy failed")
    # A
    allpts = [p for (l1, l2) in sw for p in l1 + l2]
    check(len(set(allpts)) == 6 * n, f"n={n}: swap points not fresh")
    for i, ((a, b, q), (c, d, p)) in enumerate(sw):
        check(a ^ b == q and c ^ d == p, f"n={n}: not lines")
        check(a ^ b ^ c ^ d == 1 << i, f"n={n}: sum != e_{i}")
    removed = set()
    new = []
    for (a, b, q), (c, d, p) in sw:
        removed |= {tuple(sorted((a, b, q))), tuple(sorted((c, d, p)))}
        new += [tuple(sorted((a, b, p))), tuple(sorted((c, d, q)))]
    Lset = set(L)
    check(removed <= Lset and len(removed) == 2 * n, f"n={n}: removed lines")
    check(all(t not in Lset for t in new) and len(set(new)) == 2 * n, f"n={n}: new triples")
    eqs = [t for t in L if t not in removed] + new
    deg0 = [0] * (V + 1)
    deg1 = [0] * (V + 1)
    for t in L:
        for p in t:
            deg0[p] += 1
    for t in eqs:
        for p in t:
            deg1[p] += 1
    check(deg0 == deg1 and len(set(deg1[1:])) == 1, f"n={n}: regularity")
    # B
    r = rank_gf2([row(t) for t in eqs])
    check(r == V, f"n={n}: swapped kernel dim {V - r} != 0")
    # C
    r2 = rank_gf2([row(t) for t in L if t not in removed])
    check(V - r2 == n, f"n={n}: deleted-lines kernel dim {V - r2} != n")
    rng = random.Random(n)
    for _ in range(trials):
        dele = set(rng.sample(L, 2 * n))
        r3 = rank_gf2([row(t) for t in L if t not in dele])
        check(V - r3 == n, f"n={n}: random deletion kernel dim {V - r3}")
    # D
    dirty = [t for t in eqs if t[0] ^ t[1] ^ t[2] != 0]
    check(sorted(dirty) == sorted(new), f"n={n}: Phi dirty set")
    rho = len(dirty) / len(eqs)
    print(f"n={n}: J kernel {n}, swapped kernel {V - r}, deleted-lines kernel {V - r2}, "
          f"degree {deg1[1]}, dirty fraction rho = {len(dirty)}/{len(eqs)} = {rho:.3e}")


def main():
    for n in (6, 7, 8, 9):
        run(n, trials=5 if n <= 8 else 2)
    if FAIL:
        print("FAILED", len(FAIL))
        sys.exit(1)
    print("ALL PASS")


if __name__ == "__main__":
    main()

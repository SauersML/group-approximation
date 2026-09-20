"""For the characters fed to climb3.py, record the zero twist types c_A = 0
(2 <= |A| <= n-1), the sum, and dim H^i of the Aomoto complex (A(P_n), a /\\)
for i <= n-3 over two primes (vanishing over F_p implies vanishing over Q).
Characters are given as lists over pairs (i,j), 0-indexed, lexicographic order,
exactly as in climb3.py.  Usage: python3 check_chars.py n 'a_json' ['a_json' ...]"""
import sys, os, json, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "zp-bf-n-r-first-leaf-star-resonance-2026-09-16"))
from os_resonance_bf import aomoto, PRIMES  # noqa: E402

def main():
    n = int(sys.argv[1])
    pairs0 = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for s in sys.argv[2:]:
        v = json.loads(s)
        a = {(i + 1, j + 1): x for (i, j), x in zip(pairs0, v)}   # 1-indexed for aomoto
        zt = []
        for k in range(2, n):
            for A in itertools.combinations(range(n), k):
                if sum(a[(i + 1, j + 1)] for i, j in itertools.combinations(A, 2)) == 0:
                    zt.append("".join(str(i + 1) for i in A))
        dims = [aomoto(n, a, n - 3, P) for P in PRIMES]
        print(json.dumps({"a": v, "sum": sum(v), "zero_types_1idx": zt, "aomoto_H0..n-3": dims}))

if __name__ == "__main__":
    main()

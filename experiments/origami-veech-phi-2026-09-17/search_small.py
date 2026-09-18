"""Find small origamis (B, C transitive on n squares, [B,C] != I) that carry an exact
permutation representation of Z^2 x| SL_2(Z) apart from the relator [b,c]:
permutations S, T with all other relators exactly trivial."""
import itertools
import sys
from perm import mul, inv, comm, ident, transitive, isos, relators, perm_rank_defect


def cycle_type_reps(n):
    def parts(m, mx):
        if m == 0:
            yield []
            return
        for k in range(min(m, mx), 0, -1):
            for rest in parts(m - k, k):
                yield [k] + rest
    for p in parts(n, n):
        perm = list(range(n))
        pos = 0
        for k in p:
            for i in range(k):
                perm[pos + i] = pos + (i + 1) % k
            pos += k
        yield tuple(perm)


def exact_lift(b, c):
    Bi = inv(b)
    Ts = list(isos((b, c), (b, mul(b, c))))
    Ss = list(isos((b, c), (c, Bi)))
    for s in Ss:
        for t in Ts:
            R = relators(b, c, s, t)
            if all(R[k] == ident(len(b)) for k in R if k != "[b,c]"):
                return s, t
    return None


def main(nmax):
    found = []
    for n in range(2, nmax + 1):
        for b in cycle_type_reps(n):
            for c in itertools.permutations(range(n)):
                if not transitive((b, c)) or comm(b, c) == ident(n):
                    continue
                r = exact_lift(b, c)
                if r:
                    found.append((n, b, c, r))
                    print("n=%d B=%s C=%s rank[B,C]-I=%d S=%s T=%s" % (
                        n, b, c, perm_rank_defect(comm(b, c)), r[0], r[1]))
                    sys.stdout.flush()
        print("done n=%d, total found %d" % (n, len(found)))


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 5)

"""Finite input for the depth-shift lemma (Lemma D, i = 1).

For depth j (types = off-diagonal components of C_{j+1} x_R C_{j+1}):
  (P_j)  every type of level >= 1 contains a pair of principal vertices
         (vertices of C_{j+1} over the base of C_1);
  (T_j)  the number of level->=1 types equals the number of all types at
         depth j-1 (with the injectivity argument of the artifact this
         gives surjectivity onto the types of C').
Also prints, per level i, the number of types and their largest size.
Usage: python3 principal_types.py jmax
"""
import sys
from pb import core, iota, KEYS


def components(nb):
    V = len(nb)
    seen = {}
    comps = []
    for c in range(V):
        for d in range(c + 1, V):
            if (c, d) in seen:
                continue
            comp = [(c, d)]
            seen[(c, d)] = len(comps)
            st = [(c, d)]
            while st:
                x, y = st.pop()
                for i in range(4):
                    u, v = nb[x][i], nb[y][i]
                    if u >= 0 and v >= 0:
                        key = (u, v) if u < v else (v, u)
                        if key not in seen:
                            seen[key] = len(comps)
                            comp.append(key)
                            st.append(key)
            comps.append(comp)
    return comps


def main():
    jmax = int(sys.argv[1])
    C = [core(i) for i in range(jmax + 2)]
    ios = [iota(C[i + 1], C[i]) for i in range(jmax + 1)]
    total = {}
    for j in range(jmax + 1):
        nb = C[j + 1][0]
        V = len(nb)
        down = [list(range(V))]          # down[k][v] = image of v in C_{j+1-k}
        for k in range(j + 1):
            prev = down[-1]
            down.append([ios[j - k][x] for x in prev])
        img = {i: down[j + 1 - i] for i in range(j + 2)}   # image in C_i
        principal = set(v for v in range(V) if j == 0 or img[1][v] == 0)
        comps = components(nb)
        total[j] = len(comps)
        bylev = {}
        bad = 0
        for comp in comps:
            c, d = comp[0]
            lev = max(i for i in range(j + 1) if img[i][c] == img[i][d])
            s = bylev.setdefault(lev, [0, 0])
            s[0] += 1
            s[1] = max(s[1], len(comp))
            if lev >= 1 and not any(x in principal and y in principal
                                    for x, y in comp):
                bad += 1
        ge1 = sum(v[0] for k, v in bylev.items() if k >= 1)
        print('j', j, '|C_j+1|', V, 'principal', len(principal),
              'types', len(comps),
              'by level (count, max size)', sorted(bylev.items()),
              '| P_j: level>=1 types without principal pair', bad,
              '| T_j: level>=1 types', ge1,
              'types at depth j-1', total.get(j - 1))
        sys.stdout.flush()


if __name__ == '__main__':
    main()

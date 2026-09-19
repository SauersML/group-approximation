# Nonnegative 3x3 integer matrices with det +-1 whose rows are pairwise incomparable.
# Such a matrix = a unimodular cone (columns) lying in no half of any edge split of Delta.
import sys, itertools, json
K = int(sys.argv[1])
V = [v for v in itertools.product(range(K + 1), repeat=3) if any(v)]
def leq(a, b): return all(x <= y for x, y in zip(a, b))
def comp(a, b): return leq(a, b) or leq(b, a)
def det(a, b, c):
    return (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0]) + a[2]*(b[0]*c[1]-b[1]*c[0]))
n = len(V); bad = []; unimod = 0
for i in range(n):
    a = V[i]
    for j in range(i + 1, n):
        b = V[j]
        if comp(a, b): continue
        cr = (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
        for k in range(j + 1, n):
            c = V[k]
            d = cr[0]*c[0] + cr[1]*c[1] + cr[2]*c[2]
            if d != 1 and d != -1: continue
            if comp(a, c) or comp(b, c): continue
            bad.append((a, b, c))
print(json.dumps({"K": K, "incomparable_unimodular_row_triples": len(bad), "examples": bad[:12]}))

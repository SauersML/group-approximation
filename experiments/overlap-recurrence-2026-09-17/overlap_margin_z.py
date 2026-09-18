import sys

def fixpoint(sub, start, n):
    w = start
    while len(w) < n:
        w = "".join(sub[c] for c in w)
    return w[:n]

subs = {
    "fibonacci": ({"0": "01", "1": "0"}, "0"),
    "tribonacci": ({"0": "01", "1": "02", "2": "0"}, "0"),
    "thue-morse": ({"0": "01", "1": "10"}, "0"),
    "period-doubling": ({"0": "01", "1": "00"}, "0"),
    "chacon": ({"0": "0010", "1": "1"}, "0"),
}
N = 400000
for name, (sub, st) in subs.items():
    y = fixpoint(sub, st, N)
    best = []
    for L in list(range(8, 60, 1)) + list(range(60, 3000, 7)):
        w = y[:L]
        occ = []
        i = y.find(w)
        while i != -1 and i < N - 3 * L:
            occ.append(i)
            i = y.find(w, i + 1)
        if len(occ) < 10:
            continue
        g = max(occ[j + 1] - occ[j] for j in range(len(occ) - 1))
        best.append((L - g, L, g))
    best.sort(reverse=True)
    print(name, "best margins L-maxgap:", best[:4], "ratio min", min(g / L for _, L, g in best))

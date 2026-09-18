# Independent cross-check of sphere_nop.cpp: balance via the split form
# (no J with y(J) > y(J^c) and w(J) < w(J^c)), full search over 0 <= y <= x, y not in {0, x}.
import itertools, sys
def parts(N, s, mx=None):
    if mx is None: mx = N
    if s == 0:
        if N == 0: yield ()
        return
    for v in range(min(mx, N - (s - 1)), 0, -1):
        for rest in parts(N - v, s - 1, v): yield (v,) + rest
def balanced(x):
    s = len(x); N = sum(x)
    masks = list(range(1 << s))
    for y in itertools.product(*[range(v + 1) for v in x]):
        t = sum(y)
        if t == 0 or t == N: continue
        w = [a - b for a, b in zip(x, y)]
        ok = True
        for m in masks:
            yJ = sum(y[i] for i in range(s) if m >> i & 1); wJ = sum(w[i] for i in range(s) if m >> i & 1)
            if 2 * yJ > t and 2 * wJ < N - t: ok = False; break
        if ok: return True
    return False
s, N0, N1 = map(int, sys.argv[1:4])
for N in range(N0, N1 + 1):
    tot = bad = 0; ex = []
    for x in parts(N, s):
        tot += 1
        if not balanced(x):
            bad += 1; ex.append(x)
    print(f"s={s} N={N} shapes={tot} bad={bad}", *ex[:4]); sys.stdout.flush()

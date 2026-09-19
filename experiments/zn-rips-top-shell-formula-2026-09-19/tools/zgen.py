import sys, itertools
n, r = int(sys.argv[1]), int(sys.argv[2])
def rec(i, rem, x):
    if i == n - 1:
        if rem == 0:
            nz = [v for v in x if v]
            if nz and nz[-1] > 0: print(' '.join(map(str, x + [0])))
        return
    for v in range(-rem, rem + 1):
        rec(i + 1, rem - abs(v), x + [v])
rec(0, r, [])

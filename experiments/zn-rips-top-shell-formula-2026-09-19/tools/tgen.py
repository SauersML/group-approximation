import sys
# tgen.py n r: top-shell points x in Z^n with |x|_1 = r and x_n >= 1 (Top minus Z0)
n, r = int(sys.argv[1]), int(sys.argv[2])
def rec(i, rem, x):
    if i == n - 1:
        if rem >= 1: print(' '.join(map(str, x + [rem])))
        return
    for v in range(-rem, rem + 1):
        rec(i + 1, rem - abs(v), x + [v])
rec(0, r, [])

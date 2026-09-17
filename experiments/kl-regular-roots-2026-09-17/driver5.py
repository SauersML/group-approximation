import time
from regroots import mul, ident
from certify import certify
n = 8
e = ident(n)
c6 = (1, 2, 3, 4, 5, 0, 6, 7)
C6 = [e]; x = e
for _ in range(5):
    x = mul(x, c6); C6.append(x)
def parse(s):
    w = []
    for tok in s.split():
        if tok == 't': w.append(('t', 1))
        elif tok == 'T': w.append(('t', -1))
        else: w.append(('g', C6[int(tok) % 6]))
    return w
for s in ['5 T 0 t 3 T 5 t 5 T 1', '2 T 5 t 5 T 1']:
    t0 = time.time()
    roots, cert, open_ = certify(parse(s), n, pairs=True)
    print(s, 'roots', roots, 'certified-nonregular (points or ordered pairs)', cert, 'open', len(open_), 'time %.1f' % (time.time() - t0), flush=True)
    for tb in open_:
        from regroots import closure
        el, _ = closure([c6, tb], n, 50000)
        print('  open root', tb, 'group order', len(el) if el else '>50000')

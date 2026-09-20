"""Hunt for deep < law on doubly malnormal nested pairs A <= B <= F(a,b):
B malnormal in F of rank rB, and A malnormal in F (hence malnormal in B),
as in the phi-chain L_{j+1} < L_j < L.
Usage: python3 malpair.py pairs n seed maxk rB sA LB LA
"""
import random
import sys
from chains import W, analyse, transitive
from malnormal import malnormal, rank
from randchains import rword, tostr


def main():
    pairs, n, seed, maxk, rB, sA, LB, LA = [int(x) for x in sys.argv[1:9]]
    rng = random.Random(seed)
    hist, gaps, tried = {}, 0, 0
    while tried < pairs:
        us = [tostr(W(tostr(rword(rng, 'ab', LB)))) for _ in range(rB)]
        if '' in us or rank(us) != rB or not malnormal(us)[0]:
            continue
        ws = []
        for _ in range(sA):
            ww = rword(rng, list(range(rB)), LA)
            s = ''.join(us[i] if e == 1 else us[i][::-1].swapcase() for (i, e) in ww)
            s = tostr(W(s))
            if s:
                ws.append(s)
        if not ws or rank(ws) != len(ws) or not malnormal(ws)[0]:
            continue
        tried += 1
        while True:
            PA = list(range(n)); rng.shuffle(PA)
            PB = list(range(n)); rng.shuffle(PB)
            if transitive(PA, PB):
                break
        dk, lk, dw = analyse(PA, PB, ws, us, maxk)[:3]
        hist[(dk, lk)] = hist.get((dk, lk), 0) + 1
        if dk is not None and (lk is None or dk < lk):
            gaps += 1
            print('GAP deep', dk, 'law', lk if lk is not None else '>%d' % maxk,
                  'A', ws, 'B', us, 'PA', PA, 'PB', PB, 'witness', dw, flush=True)
    print('pairs', pairs, 'n', n, 'seed', seed, 'maxk', maxk, 'rB', rB, 'sA', sA,
          'LB', LB, 'LA', LA, 'gaps', gaps, 'hist', sorted(hist.items(), key=str))


if __name__ == '__main__':
    main()

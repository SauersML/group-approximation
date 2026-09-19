"""Random nested pairs A <= B <= F(a,b): hunt for deep(Q) < law(Q).

B = <u_1..u_r> with random reduced words u_i in a,b (length <= LB);
A = <w_1..w_s> with w_i random words in the u's (length <= LA), rewritten in a,b.
For each pair, several random transitive Q of size n; exact deep, law (cap maxk).
Usage: python3 randchains.py pairs qs n seed maxk rB sA LB LA [par]
  par=1: each w_i has even exponent sum in every u_j, so A lies in the kernel
  of B -> (Z/2)^r and the relative rank of B over A is r at Q = point.
"""
import random
import sys
from chains import W, analyse, transitive


def rword(rng, letters, L):
    w = []
    for _ in range(rng.randint(1, L)):
        while True:
            x = (rng.choice(letters), rng.choice((1, -1)))
            if not w or not (w[-1][0] == x[0] and w[-1][1] == -x[1]):
                break
        w.append(x)
    return w


def tostr(w):
    return ''.join(l if e == 1 else l.upper() for (l, e) in w)


def main():
    pairs, qs, n, seed, maxk, rB, sA, LB, LA = [int(x) for x in sys.argv[1:10]]
    par = len(sys.argv) > 10 and sys.argv[10] == '1'
    rng = random.Random(seed)
    hist = {}
    gaps = 0
    for _ in range(pairs):
        us = [tostr(W(tostr(rword(rng, 'ab', LB)))) for _ in range(rB)]
        us = [u for u in us if u]
        if not us:
            continue
        ws = []
        for _ in range(sA):
            while True:
                ww = rword(rng, list(range(len(us))), LA)
                if not par or all(sum(e for (i, e) in ww if i == k) % 2 == 0
                                  for k in range(len(us))):
                    break
            s = ''
            for (i, e) in ww:
                s += us[i] if e == 1 else ''.join(c.swapcase() for c in reversed(us[i]))
            s = tostr(W(s))
            if s:
                ws.append(s)
        if not ws:
            continue
        done = 0
        while done < qs:
            PA = list(range(n)); rng.shuffle(PA)
            PB = list(range(n)); rng.shuffle(PB)
            if not transitive(PA, PB):
                continue
            done += 1
            dk, lk, dw, va, vb, ns, nl = analyse(PA, PB, ws, us, maxk)
            key = (dk, lk)
            hist[key] = hist.get(key, 0) + 1
            if dk is not None and (lk is None or dk < lk):
                gaps += 1
                print('GAP deep', dk, 'law', lk if lk is not None else '>%d' % maxk,
                      'A', ws, 'B', us, 'PA', PA, 'PB', PB, '|GA|', va,
                      '|GB|', vb, 'witness', dw)
                sys.stdout.flush()
    print('pairs', pairs, 'qs', qs, 'n', n, 'seed', seed, 'maxk', maxk,
          'rB', rB, 'sA', sA, 'LB', LB, 'LA', LA, 'gaps', gaps,
          'hist', sorted(hist.items(), key=str))


if __name__ == '__main__':
    main()

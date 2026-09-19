# H = <b,c,d,e | r> as a one-relator group inside G = F_4 x|_phi <y>, and its Moldavanskii level rewriting.
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
W11 = os.environ.get('W11DIR', HERE)
sys.path.insert(0, W11)
from fbc import red, inv, tofib
from fold2 import SG
HXY = {'a': 'XyxYx', 'b': 'Xyyyx', 'c': 'XYxyx', 'd': 'y', 'e': 'xyX'}
def hinv(u): return ''.join(c.swapcase() for c in reversed(u))
def toxy(u): return red(''.join(HXY[c] if c.islower() else inv(HXY[c.lower()]) for c in u))
U0, U1 = 'dEbcBADDed', 'bcBAAbDcBd'
R = 'eDDEdd' + 'bCB' + 'eDDEdd' + 'bDcBd'          # u1 after eliminating a via u0
A_WORD = hinv('bCB' + 'eDDEdd')                     # a = (bCB eDDEdd)^-1
EPS = {'b': 3, 'c': 0, 'd': 1, 'e': 1}
def eps(u): return sum(EPS[c.lower()] * (1 if c.islower() else -1) for c in u)
def levelize(u, lift):
    """Rewrite an eps-0 word over gens into symbols (g, j) = d^j g0 d^-j, where g = g0 d^EPS[g] (lift[g] = EPS)."""
    out, j = [], 0
    for c in u:
        g = c.lower()
        if g == 'd': j += 1 if c == 'd' else -1; continue
        if c.islower(): out.append((g, j, 1)); j += lift[g]
        else: j -= lift[g]; out.append((g, j, -1))
    assert j == 0
    return out
def g0xy(g): return toxy(g + 'D' * EPS[g])
def symF(g, j): return tofib('y' * j + g0xy(g) + 'Y' * j) if j >= 0 else tofib('Y' * (-j) + g0xy(g) + 'y' * (-j))

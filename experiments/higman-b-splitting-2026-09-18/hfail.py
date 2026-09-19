"""Test beta = b d for beta'' (the B-part of beta R beta^-1, see twists.py) outside Lambda_B.
Certificate of beta'' notin Lambda_B: a vertex a^j1 c^k1 ... of T_B (depth <= 3) that beta'' moves.
Such a beta shows that hypothesis (H_e) of the reduction lemma fails: in Q_B = Gamma/Lambda_B,
beta R beta^-1 is not in A, so <<R>>_{Q_B} is not contained in A.
usage: python3 hfail.py e"""
import sys, itertools
e = int(sys.argv[1])
sys.argv = [sys.argv[0], str(e), '1']
from pathstab import push, red, inv, m

def left(s, word, j):
    """word * s^j = s^j' * word'  (word in B); as in twists.py and ball.py."""
    w2, i2 = push(s, -j, inv(word))
    return (-i2) % m, inv(w2)

R = [('a', -1), ('c', -1), ('a', 1), ('c', 1)] * 2

def twist(beta):
    """beta R beta^-1 = alpha . beta''  (as in twists.py)."""
    alpha = []; cur = beta
    for (s, j) in R:
        j2, cur = left(s, cur, j)
        alpha.append((s, j2))
    return red(alpha), red(list(cur) + list(inv(beta)))

def act(gword, vert):
    """action of a B-word on the vertex a^j1 c^k1 a^j2 ... of T_B (as in ball.py)."""
    out = []; beta = gword
    for idx, x in enumerate(vert):
        s = 'a' if idx % 2 == 0 else 'c'
        x2, beta = left(s, beta, x)
        out.append(x2)
    return tuple(out)

def moves_cL1(word):
    """image of the vertex c L1 = (0,1) (distance 2 from L1 in T_B) under a B-word."""
    return act(word, (0, 1))

beta = (('b', 1), ('d', 1))
alpha, b2 = twist(beta)
print('e=%d m=%d beta=b d  S_beta=%s  beta\'\'=%s' % (e, m, alpha, b2))
if b2:
    img = moves_cL1(b2)
    print('e=%d beta\'\' sends vertex c L1=(0,1) to %s: %s' % (e, img, 'MOVED, so beta\'\' notin Lambda_B and (H_e) fails' if img != (0, 1) else 'fixed'))
else:
    print('e=%d beta\'\' = 1' % e)

"""Genuine generators: F = ker(P_Y -> P_Z) (3 meridians A_12, A_13, A_14 of the walls of A_y outside A_z) and
meridians of the 12 walls of A_x outside A_z (they normally generate N = ker(P_X -> P_Z)), as H_4 words;
their images in the three shadows (sign convention: s4^2 -> +Delta^2 of the V0 cluster)."""
import numpy as np
from mono import SIM, SMAT, W, idx, name, Ax, Ay, Az, is_wall, SH, read_braid, is_pure, free_reduce

SGN = -1


def meridians(letters):
    """positive-lift meridians w s_j^2 w^-1 for the reflections of the parabolic on 'letters', one per wall."""
    seen = {}
    frontier = [([], np.eye(4))]
    for depth in range(16):
        nxt = []
        for w, M in frontier:
            for j in letters:
                k = idx(M @ SIM[j - 1])
                if k is not None and k not in seen:
                    seen[k] = w + [j, j] + [-g for g in reversed(w)]
            for j in letters:
                nxt.append((w + [j], M @ SMAT[j - 1]))
        frontier = nxt[:2000]
    return seen


def rho(a, word):
    return [SGN * g for g in read_braid(SH[a], word)]


MX = meridians([2, 3, 4]); MY = meridians([1, 2, 3])
NZ = {k: w for k, w in MX.items() if not is_wall(W[k], Az)}
FY = {k: w for k, w in MY.items() if not is_wall(W[k], Az)}
if __name__ == '__main__':
    print('walls of A_x', len(MX), 'non-Z', len(NZ), '; walls of A_y', len(MY), 'non-Z', len(FY))
    for lab, dct in (('F', FY), ('N', NZ)):
        for k, w in sorted(dct.items(), key=lambda kv: len(kv[1])):
            assert is_pure(w)
            print(lab, name(k), 'len', len(w), ['V%d:%s' % (a, free_reduce(rho(a, w))) for a in range(3)])

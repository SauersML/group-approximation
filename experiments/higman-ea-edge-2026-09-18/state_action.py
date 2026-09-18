"""Full tower-type state action of the free group Phi = <alpha, gamma> (flavour b).

State s = (h, A, G):
  h = alpha-exponent so far (the height),
  A = formal sum over alpha-letters so far of eps [G at that letter]   (full alpha-types),
  G = formal sum over gamma-letters so far of eps [(h, A) at that letter]  (full gamma-types).
alpha^e : (h, A, G) -> (h + e, A + e[G], G)
gamma^e : (h, A, G) -> (h, A, G + e[(h, A)])
S^b_r(u) = 0 for all r >= -1  iff  u fixes the state 0 (see the proof file).

We check that the orbit map u -> u.0 is injective on all reduced words of length <= L,
i.e. no nontrivial reduced word of length <= 2L fixes 0.
Usage: python3 state_action.py L
"""
import sys

_intern = {}


def key(obj):
    """Intern a hashable object as a small int."""
    k = _intern.get(obj)
    if k is None:
        k = len(_intern)
        _intern[obj] = k
    return k


def fs_add(fs, k, e):
    """fs is a frozen formal sum: a sorted tuple of (key, coeff)."""
    d = dict(fs)
    d[k] = d.get(k, 0) + e
    if d[k] == 0:
        del d[k]
    return tuple(sorted(d.items()))


def act(state, letter):
    h, A, G = state
    if letter in ('a', 'A'):
        e = 1 if letter == 'a' else -1
        return (h + e, fs_add(A, key(('G', G)), e), G)
    e = 1 if letter == 'c' else -1
    return (h, A, fs_add(G, key(('HA', h, A)), e))


INV = {'a': 'A', 'A': 'a', 'c': 'C', 'C': 'c'}


def main():
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    zero = (0, (), ())
    seen = {zero: ''}
    frontier = [('', zero)]
    total = 1
    for length in range(1, L + 1):
        new = []
        for w, s in frontier:
            for x in 'aAcC':
                if w and INV[x] == w[-1]:
                    continue
                t = act(s, x)
                wx = w + x
                if t in seen:
                    print('COLLISION', seen[t], wx)
                    return 1
                seen[t] = wx
                new.append((wx, t))
        frontier = new
        total += len(new)
        print(f'length {length}: {len(new)} reduced words, all states distinct (total {total})')
    print(f'no nontrivial reduced word of length <= {2 * L} fixes 0 (flavour b)')
    return 0


if __name__ == '__main__':
    sys.exit(main())

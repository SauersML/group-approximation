"""Depth reduction on the dyadic F-orbit.

Claim checked: every dyadic y = 0.p (p ends in '1', depth k = |p| >= 2) has a word g of
length <= 3 in x0^{+-1}, x1^{+-1} with depth(g y) < k.

(1) Direct exhaustive check for k = 2..K.
(2) Prefix-reading reduction: for every u in {0,1}^5 we take the witness g_u found for the
    depth-6 point 0.u1, compute the prefix image q (g(0.u w) = 0.q w for all w, valid since
    |u| >= |g|+2), and assert |q| < 5. Then depth(g_u(0.u v)) = |q| + |v| < |u| + |v| for every
    v ending in '1', so the claim holds for all k >= 6.  We also re-verify g_u on random v.
"""
import itertools, json, random, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from dyadic_depth_distance import x0, x0i, x1, x1i, check

GEN = {'a': x0, 'A': x0i, 'b': x1, 'B': x1i}
K = int(sys.argv[1]) if len(sys.argv) > 1 else 12


def apply(word, s):
    for c in reversed(word):  # rightmost letter acts first
        s = GEN[c](s)
    return s


WORDS = [''.join(w) for l in range(1, 4) for w in itertools.product('aAbB', repeat=l)]


def witness(p):
    for w in WORDS:
        t = apply(w, p)
        if t != '' and len(t) < len(p):
            return w
    return None


def main():
    assert check()
    out = {'K': K, 'direct': {}, 'prefix_reduction': {}}
    for k in range(2, K + 1):
        worst = 0
        for bits in itertools.product('01', repeat=k - 1):
            p = ''.join(bits) + '1'
            w = witness(p)
            assert w is not None, p
            worst = max(worst, len(w))
        out['direct'][str(k)] = worst
    rng = random.Random(1)
    for bits in itertools.product('01', repeat=5):
        u = ''.join(bits)
        w = witness(u + '1')
        assert w is not None and len(w) <= 3
        # prefix image: act on u followed by a long marker tail and strip the tail
        tail = '1' + ''.join(rng.choice('01') for _ in range(20)) + '1'
        img = apply(w, u + tail)
        assert img.endswith(tail), (u, w)
        q = img[: len(img) - len(tail)]
        assert len(q) < 5, (u, w, q)
        for _ in range(50):
            v = ''.join(rng.choice('01') for _ in range(rng.randint(0, 30))) + '1'
            t = apply(w, u + v)
            assert t == q + v, (u, v, w)
        out['prefix_reduction'][u] = {'word': w, 'q': q}
    out['max_witness_length'] = max(out['direct'].values())
    out['all_prefix_images_shorter'] = True
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()

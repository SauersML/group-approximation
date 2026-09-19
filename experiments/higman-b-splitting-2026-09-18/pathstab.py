"""Exact computation in Gamma(3,m) = H4(3)/<<a^m,b^m,c^m,d^m>>, m = 2^e, with the
B-splitting Gamma = L1 *_B L2, L1 = B.<a>, L2 = B.<c>, B = <b,d> = Z/m * Z/m.
Pushing rules (valid in Gamma):
  a^i b^q = b^(q t^i) a^i,  a^i d^p = d^p a^(i 3^p)     (t = 3^-1 mod m)
  c^i b^q = b^q c^(i 3^q),  c^i d^p = d^(p t^i) c^i
An element of B is a reduced alternating tuple of (letter, exponent mod m).
R^-1 = s1...s8 = c^-1 a^-1 c a c^-1 a^-1 c a.  x_k = s_k^-1 x_(k-1) s_k.
If x0 in B and every x_k (k<=8) lies in B, then x8 = R x0 R^-1 and w = x8 x0^-1 is
an element of B that lies in <<R>>; w != 1 iff x8 != x0 as reduced words."""
import sys, itertools
e = int(sys.argv[1]) if len(sys.argv) > 1 else 4
maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 4
m = 2**e
t = pow(3, -1, m)

def red(word):
    out = []
    for (g, x) in word:
        x %= m
        if x == 0: continue
        if out and out[-1][0] == g:
            y = (out[-1][1] + x) % m
            out.pop()
            if y: out.append((g, y))
        else:
            out.append((g, x))
    return tuple(out)

def push(s, i, word):
    """s^i * word = word' * s^j ; returns (word', j)."""
    res = []
    for (g, x) in word:
        if s == 'a':
            if g == 'b': res.append(('b', x * pow(t, i % m, m))); 
            else: res.append(('d', x)); i = i * pow(3, x, m)
        else:  # s == 'c'
            if g == 'b': res.append(('b', x)); i = i * pow(3, x, m)
            else: res.append(('d', x * pow(t, i % m, m)))
        i %= m
    return red(res), i

def conj(s, eps, word):
    """(s^eps)^-1 word s^eps ; returns word or None if not in B."""
    w2, j = push(s, -eps, word)
    return w2 if (j + eps) % m == 0 else None

SEQ = [('c', -1), ('a', -1), ('c', 1), ('a', 1)] * 2

def chain(x0):
    x = x0
    for (s, eps) in SEQ:
        x = conj(s, eps, x)
        if x is None: return None
    return x

def inv(word):
    return red([(g, -x) for (g, x) in reversed(word)])

def words(L):
    for start in 'bd':
        letters = [start if k % 2 == 0 else ('d' if start == 'b' else 'b') for k in range(L)]
        for exps in itertools.product(range(1, m), repeat=L):
            yield tuple(zip(letters, exps))

if __name__ == '__main__':
    found = 0; stab = 0
    for L in range(1, maxlen + 1):
        for x0 in words(L):
            x8 = chain(x0)
            if x8 is None: continue
            stab += 1
            if x8 != x0:
                found += 1
                if found <= 5:
                    w = red(list(x8) + list(inv(x0)))
                    print('e=%d x0=%s  R x0 R^-1=%s  w=%s' % (e, x0, x8, w))
        print('e=%d length<=%d: path-stabilizer elements %d, non-commuting %d' % (e, L, stab, found))

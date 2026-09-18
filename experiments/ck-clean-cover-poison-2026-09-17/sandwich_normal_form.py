#!/usr/bin/env python3
"""Check the normal form of U = Z[T]<p,q>/(p(1-g)q - 1) with T = free group F(a,b).

Group letters are freely reduced nonempty strings over a,A,b,B. A word is a tuple
of letters, each either ('G', reduced string) or 'p' or 'q'. Irreducible words have
no two adjacent group letters and no subword p g q. Elements of N are dicts
word -> integer coefficient.

Checks, over all irreducible words up to a length bound and a few group letters:
  1. every operator output is a combination of irreducible words;
  2. lambda_t lambda_t' = lambda_{tt'} and lambda_{t} lambda_{t^-1} = id;
  3. lambda_p lambda_q - lambda_p lambda_g lambda_q = id  (the defining relation);
  4. ev(W) = W for irreducible W (independence of the basis).
Run: python3 sandwich_normal_form.py   (exits nonzero on failure)
"""
import itertools, sys

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}

def red(s):
    out = []
    for c in s:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return ''.join(out)

def ginv(s):
    return ''.join(INV[c] for c in reversed(s))

G = 'ab'  # the prescribed g != 1

def irreducible(w):
    for i in range(len(w) - 1):
        if w[i] not in ('p', 'q') and w[i + 1] not in ('p', 'q'):
            return False
    for i in range(len(w) - 2):
        if w[i] == 'p' and w[i + 2] == 'q' and w[i + 1] == ('G', G):
            return False
    return True

def add(d, w, c):
    d[w] = d.get(w, 0) + c
    if d[w] == 0:
        del d[w]

def lam_t(t, vec):
    out = {}
    for w, c in vec.items():
        if w and w[0] not in ('p', 'q'):
            u = red(t + w[0][1])
            nw = ((('G', u),) if u else ()) + w[1:]
        else:
            nw = ((('G', t),) if t else ()) + w
        add(out, nw, c)
    return out

def lam_q(vec):
    out = {}
    for w, c in vec.items():
        add(out, ('q',) + w, c)
    return out

def lam_p(vec):
    out = {}
    for w, c in vec.items():
        if len(w) >= 2 and w[0] == ('G', G) and w[1] == 'q':
            add(out, ('p', 'q') + w[2:], c)
            add(out, w[2:], -c)
        else:
            add(out, ('p',) + w, c)
    return out

def apply_word(word, vec):
    for x in reversed(word):
        vec = lam_p(vec) if x == 'p' else lam_q(vec) if x == 'q' else lam_t(x[1], vec)
    return vec

def main():
    glets = [('G', s) for s in ['a', 'b', 'A', 'ab', 'Ba', 'aa', 'bA']]
    letters = glets + ['p', 'q']
    words = [()]
    for L in range(1, 5):
        for w in itertools.product(letters, repeat=L):
            if irreducible(w):
                words.append(w)
    fails = 0
    for w in words:
        e = {w: 1}
        for op in (lambda v: lam_t('a', v), lam_q, lam_p):
            if not all(irreducible(x) for x in op(e)):
                fails += 1
        for t1, t2 in [('a', 'b'), ('ab', 'B'), ('A', 'a'), ('ba', 'A')]:
            if lam_t(t1, lam_t(t2, e)) != lam_t(red(t1 + t2), e):
                fails += 1
        if lam_t('ab', lam_t(ginv('ab'), e)) != e:
            fails += 1
        lhs = lam_p(lam_q(e))
        for ww, c in lam_p(lam_t(G, lam_q(e))).items():
            add(lhs, ww, -c)
        if lhs != e:
            fails += 1
        if apply_word(w, {(): 1}) != e:
            fails += 1
    print(f"irreducible words checked: {len(words)}; failures: {fails}")
    sys.exit(1 if fails else 0)

if __name__ == '__main__':
    main()

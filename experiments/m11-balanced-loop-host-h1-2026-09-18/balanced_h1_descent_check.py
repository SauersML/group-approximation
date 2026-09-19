"""Checks the local lemmas behind H_1(R°) = Z/55, R° = <M_11, b, C>,
b = (b, alpha, beta, 1, ..., 1), C = (1, 1, 1, C, b alpha, C^-1, 1, ..., 1).
Points are 0..10 (point i+1 of the text is i here); right actions.
chi = e_b + e_C.  Checked on all words of length <= 5 over {alpha, beta, b, C}^{+-1}:
 (M) sum_x chi(w|_x) = chi(w)                        (mass identity)
 (N) nf(w|_x) <= nf(w), nC(w|_x) <= nC(w)            (b/C-letter counts do not grow)
 (S) if nf(w|_x) = nf(w) and nC(w|_x) = nC(w), then w|_x is a word over {b, C}^{+-1}
 (P) a word over {b, C}^{+-1} with both kinds of letter has no stable point
Also: b has order exactly 55 on level 3, and b^55 acts trivially on level 4.
"""
import itertools
D = 11
alpha = [(x + 1) % D for x in range(D)]
beta = list(range(D))
for cyc in ([1, 2, 3, 4, 8], [5, 10, 7, 11, 6]):
    for i in range(len(cyc)):
        beta[cyc[i] - 1] = cyc[(i + 1) % len(cyc)] - 1
inv = lambda p: [p.index(y) for y in range(D)]
ROOT = {('a', 1): alpha, ('a', -1): inv(alpha), ('be', 1): beta, ('be', -1): inv(beta)}
SEC = {('b', 1): {0: [('b', 1)], 1: [('a', 1)], 2: [('be', 1)]},
       ('b', -1): {0: [('b', -1)], 1: [('a', -1)], 2: [('be', -1)]},
       ('C', 1): {3: [('C', 1)], 4: [('b', 1), ('a', 1)], 5: [('C', -1)]},
       ('C', -1): {3: [('C', -1)], 4: [('a', -1), ('b', -1)], 5: [('C', 1)]}}
LET = [('a', 1), ('a', -1), ('be', 1), ('be', -1), ('b', 1), ('b', -1), ('C', 1), ('C', -1)]

def move(t, x):
    return ROOT[t][x] if t in ROOT else x

def section(w, x):
    out = []
    for t in w:
        out += SEC.get(t, {}).get(x, [])
        x = move(t, x)
    return out

def reduce(w):
    st = []
    for t in w:
        if st and st[-1][0] == t[0] and st[-1][1] == -t[1]:
            st.pop()
        else:
            st.append(t)
    return st

chi = lambda w: sum(e for (s, e) in w if s in ('b', 'C'))
nf = lambda w: sum(1 for (s, e) in w if s in ('b', 'C'))
nC = lambda w: sum(1 for (s, e) in w if s == 'C')

bad = {'M': 0, 'N': 0, 'S': 0, 'P': 0}
count = 0
for L in range(1, 6):
    for w in itertools.product(LET, repeat=L):
        w = list(w)
        if reduce(w) != w:
            continue
        count += 1
        secs = [reduce(section(w, x)) for x in range(D)]
        if sum(chi(s) for s in secs) != chi(w):
            bad['M'] += 1
        for s in secs:
            if nf(s) > nf(w) or nC(s) > nC(w):
                bad['N'] += 1
            if nf(s) == nf(w) and nC(s) == nC(w) and any(t[0] in ('a', 'be') for t in s):
                bad['S'] += 1
        if all(t[0] in ('b', 'C') for t in w) and nC(w) and nC(w) < nf(w):
            for x in range(D):
                s = reduce(section(w, x))
                if nf(s) == nf(w):
                    bad['P'] += 1
print("reduced words checked:", count)
print("failures:", bad)

def perm(w, n):
    """permutation of X^n (as tuples) induced by the word w"""
    res = {}
    for v in itertools.product(range(D), repeat=n):
        cur, img = list(w), []
        for x in v:
            y = x
            for t in cur:
                y = move(t, y)
            img.append(y)
            cur = section(cur, x)
        res[v] = tuple(img)
    return res

def is_id(w, n):
    return all(k == v for k, v in perm(w, n).items())

orders = [k for k in range(1, 56) if is_id([('b', 1)] * k, 3)]
print("smallest k with b^k trivial on level 3:", orders[:1])
print("b^55 trivial on level 4:", is_id([('b', 1)] * 55, 4))
print("all local lemmas hold:", not any(bad.values()) and orders[:1] == [55])

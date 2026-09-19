"""Exact sections of syllable words in the letter-level model of Bbar_e (levels.py), for any e.
A word is a list of syllables ('b', i) / ('d', j), composed right to left (the last syllable acts
first). From the model  b^i = (0, r -> d^(i 3^r)),  d^j = (j, r -> b^j):
the section of the word at a letter x is the syllable word obtained by walking the syllables from
right to left with the current letter y (start y = x): b^i emits d^(i 3^y mod n) (y unchanged),
d^j emits b^j and moves y -> T^j y. The image letter is the final y. Syllable length is preserved.
Prints the image of the vertex R = (-1,-1,1,1,-1,-1,1,1) under beta = b o d (the letters of the
twisted relator S_beta) and the section beta^R, for comparison with hfail-output.txt of w13.
usage: python3 symsec.py e
"""
import sys
e = int(sys.argv[1]); m = 2 ** e; n = m // 4; T = pow(3, -1, m)
def section(word, x):
    y = x; out = []
    for (s, k) in reversed(word):
        if s == 'b': out.append(('d', k * pow(3, y, n) % n))
        else: out.append(('b', k % n)); y = y * pow(T, k, m) % m
    return list(reversed(out)), y
R = [(-1) % m, (-1) % m, 1, 1, (-1) % m, (-1) % m, 1, 1]
beta = [('b', 1), ('d', 1)]
img = []; g = beta
for x in R:
    g, y = section(g, x); img.append(y)
print("e=%d beta = b o d: image of R = %s" % (e, img))
print("e=%d beta^R = %s" % (e, g))

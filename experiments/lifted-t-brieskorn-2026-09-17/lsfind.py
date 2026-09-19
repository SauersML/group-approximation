"""Find palindromic positive words Y in alpha, beta (length <= 17), starting and ending
with alpha^2, that commute with X = beta alpha beta in T.  Used to recover the second
Lochak-Schneps commutation relation."""
import itertools
from pl import ID
from run import alpha, beta

x = beta * alpha * beta
xi = x.inverse()
cache = {}


def ev(word):
    r = ID
    for ch in word:
        r = r * (alpha if ch == "a" else beta)
    return r


hits = []
for half in range(1, 9):
    for mid in ["", "a", "b"]:
        for t in itertools.product("ab", repeat=half):
            s = "".join(t)
            if not s.startswith("aa") or "aaaa" in s or "bbb" in s:
                continue
            word = s + mid + s[::-1]
            if "aaaa" in word or "bbb" in word:
                continue
            y = ev(word)
            if x * y == y * x:
                hits.append(word)
for h in sorted(set(hits), key=len):
    print(len(h), h)

"""Magnus rewriting of G_2 = <a,t | (a^(t^2))^-1 [a,a^t] a^(t^2) [a,a^t]^-2>
in both coordinate directions.  Convention: x^s = s^-1 x s, [x,y] = x^-1 y^-1 x y.
Letters: 'a','A' (=a^-1), 't','T'."""
def inv(w): return ''.join(c.swapcase() for c in reversed(w))
def conj(x, s): return inv(s) + x + s
def comm(x, y): return inv(x) + inv(y) + x + y
def red(w):
    out = []
    for c in w:
        if out and out[-1] == c.swapcase(): out.pop()
        else: out.append(c)
    return ''.join(out)
a, t = 'a', 't'
a1 = conj(a, t); a2 = conj(a, t + t)
u = comm(a, a1)
rel = red(inv(a2) + u + a2 + inv(u) + inv(u))
print("relator:", rel, "length", len(rel))

def rewrite(w, stable):
    """Rewrite w (stable letter has exponent sum 0) in letters x_e = s^e x s^-e,
    where x is the other generator; returns list of (index, exponent)."""
    other = 'a' if stable == 't' else 't'
    e = 0; out = []
    for c in w:
        if c.lower() == stable:
            e += 1 if c == stable else -1
        else:
            out.append((e, 1 if c == other else -1))
    return out, e

for s in ['t', 'a']:
    rw, tot = rewrite(rel, s)
    assert tot == 0
    idx = [i for i, _ in rw]
    lo, hi = min(idx), max(idx)
    print(f"\nstable letter {s}: exponent sum {tot}; letters x_{lo}..x_{hi}")
    print(" rewritten:", ' '.join(f"x{i-lo}^{e}" for i, e in rw))
    for ext in (lo, hi):
        occ = [e for i, e in rw if i == ext]
        print(f"  extreme x{ext-lo}: occurrences {len(occ)}, exponents {occ}, exponent sum {sum(occ)}")

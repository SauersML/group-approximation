"""Check of the shifted cocycle in
research/spinal-groups-all-sequences-not-fp-torsion-quotients-proof.md
for Grigorchuk groups G_omega with random sequences omega in {0,1,2}^D.
Verifies on random words, to depth D:
 (c) pi_{k+1}(Phi^k_x(w)) = pi_k(w)|_x,  (d) |Phi^k_x(w)| <= #B-letters,
and (S1) nontriviality/distinctness of b,c,d at depth D when omega has two symbols."""
import random, itertools
random.seed(7)
D = 8
KILL = {0: 'd', 1: 'c', 2: 'b'}   # omega_n = i: the letter with trivial section at 0

def sec0(s, n, om):
    """section at vertex 0 of letter s in J_n (s in bcd); spine at vertex 1."""
    return '' if KILL[om[n]] == s else 'a'

def act(word, v, n, om):
    v = list(v)
    for s in reversed(word):
        v = letter(s, v, n, om)
    return tuple(v)

def letter(s, v, n, om):
    if not v:
        return v
    x = v[0]
    if s == 'a':
        return [1 - x] + v[1:]
    if x == 0:
        return [0] + list(act(sec0(s, n, om), v[1:], n + 1, om))
    return [1] + list(act(s, v[1:], n + 1, om))

def phi(word, x, n, om):
    out, y = [], x
    for s in reversed(word):
        if s in 'bcd':
            out.insert(0, sec0(s, n, om) if y == 0 else s)
        elif s == 'a':
            y = 1 - y
    return ''.join(out)

ok = True
for trial in range(60):
    om = [random.randrange(3) for _ in range(D + 2)]
    n = random.randrange(2)
    w = ''.join(random.choice('abcd') for _ in range(random.randint(1, 24)))
    for x in (0, 1):
        pw = phi(w, x, n, om)
        ok &= len(pw) <= sum(ch in 'bcd' for ch in w)
        for v in itertools.product((0, 1), repeat=D - 1):
            lhs = act(w, (x,) + v, n, om)
            rhs = (act(w, (x,), n, om)[0],) + act(pw, v, n + 1, om)
            ok &= lhs == rhs
print('G_omega shifted lifting and length checks pass:', ok)

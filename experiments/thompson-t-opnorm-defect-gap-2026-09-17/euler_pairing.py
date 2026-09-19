"""Evaluate the Lochak--Schneps relators on lifts to R (the central extension T-bar).

alpha-bar(x) = x + 1/4; beta-bar = the lift of beta = C_cfp^-1 with beta-bar(0) = 1/2.
Each relator r evaluates on the lifts to a translation x -> x + e(r), e(r) in Z
(the value in the centre <z> of T-bar, z(x) = x + 1).
For c in N cap [F,F] this gives the Euler pairing e(c) (connecting map H_2(T) -> Z
of the central extension), independent of the choice of lifts.
Convention 'right': the leftmost letter of a word is applied first.
"""
import json
from fractions import Fraction as Fr
from pl_circle import inverse, ev
from verify_ls import C_cfp, REL

beta = inverse(C_cfp)


def lift_ev(f, f0, x):
    """Lift of circle map f with lift value f0 at 0; f is increasing degree one."""
    n = x // 1
    y = ev(f, x - n)          # in [0,1)
    # choose integer so that the lift is continuous: lift(t) in [f0, f0+1) for t in [0,1)
    base = f0 + ((y - f0) % 1)
    return base + n


def alpha_bar(x):
    return x + Fr(1, 4)


def alpha_bar_inv(x):
    return x - Fr(1, 4)


beta0 = ev(beta, Fr(0))  # = 1/2
binv = inverse(beta)
binv0 = ev(binv, Fr(0))
# the lift of beta^-1 must be the inverse of beta-bar: beta-bar^-1(0) = t with beta-bar(t)=0.
# beta maps [3/4,1) onto [0,1/2), so beta-bar maps [-1/4,0) onto [-1,-1/2): beta-bar^-1(0) = binv0 - 1 or binv0.


def beta_bar(x):
    return lift_ev(beta, beta0, x)


def make_beta_bar_inv():
    for cand in (binv0, binv0 - 1, binv0 + 1):
        g = lambda x, c=cand: lift_ev(binv, c, x)
        if all(beta_bar(g(Fr(k, 17))) == Fr(k, 17) for k in range(-20, 20)):
            return g
    raise RuntimeError


beta_bar_inv = make_beta_bar_inv()
G = {"a": alpha_bar, "A": alpha_bar_inv, "b": beta_bar, "B": beta_bar_inv}


def evaluate(word, x):
    for ch in word:           # leftmost applied first
        x = G[ch](x)
    return x


def translation(word):
    pts = [Fr(k, 64) for k in range(0, 64)] + [Fr(1, 3), Fr(2, 7)]
    vals = {evaluate(word, x) - x for x in pts}
    assert len(vals) == 1, (word, vals)
    return vals.pop()


if __name__ == "__main__":
    e = {k: translation(w) for k, w in REL.items()}
    for k, v in e.items():
        print(f"e({k}) = {v}")
    ePent, eA, eB = e["(ba)^5"], e["a^4"], e["b^3"]
    ec0 = 12 * ePent - 15 * eA - 20 * eB
    print("c_0 = r_P^12 r_a^-15 r_b^-20 ;  e(c_0) =", ec0)
    json.dump({k: str(v) for k, v in e.items()} | {"e(c_0)": str(ec0)},
              open("out_euler_pairing.json", "w"), indent=1)

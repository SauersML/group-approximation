from hlib import *
for u in (U0, U1, R): print(u, 'trivial in G:', tofib(toxy(u)) == '')
print('a = ', A_WORD, 'equals XyxYx in G:', tofib(toxy(A_WORD) + inv(HXY['a'])) == '')
L = levelize(R, EPS)
print('levelized r:', ' '.join(f"{g}{j}{'' if s>0 else '^-1'}" for g, j, s in L))
for g in 'bce':
    js = [j for h, j, s in L if h == g]; print(g, 'range', min(js), max(js))

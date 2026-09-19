import sys
sys.path.insert(0,'/home/user/group-approximation/experiments/h4-artin-complex-6cycles-2026-09-17')
from garside import Coxeter, Artin
W=Coxeter(4,{(0,1):3,(1,2):3,(2,3):5}); G=Artin(W)
def inv(w): return [-g for g in reversed(w)]
P3,P2,P1=[1,1],[1,2,2,-1],[1,2,3,3,-2,-1]
a=P2+P3; b=P1+P3
g=G.word([-3,-2]+inv(b)+a+[2,3])
for K in range(0,4): print('K',K,'(s2s3)^-1 b^-1 a (s2s3) in A_{s1s2}:',G.in_parabolic(g,0b0011,K))
# guess: it equals p3^-1 * p2 ... print positive form after padding
dX=G.simple(W.parabolic_w0(0b0011)); h=g
for _ in range(2): h=G.mul(dX,h)
print('Delta_{12}^2 * it =',h[0],[W.word[x] for x in h[1]])
for cand,name in [([-1,-1,-2,-2,1,1],'?')]: pass

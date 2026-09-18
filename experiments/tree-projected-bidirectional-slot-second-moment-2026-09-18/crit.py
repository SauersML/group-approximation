import sys, anal
from math import sqrt
def pstar(m,v=2):
    d=4*m+v; la=v+2*sqrt(3)*m
    return 2/(la+sqrt(la*la-4*(d-1)))
def crit(fn,m):
    ctx=anal.load(fn)
    lo,hi=0.15/m,0.45/m
    for _ in range(22):
        mid=(lo+hi)/2
        up,low,w=anal.rho(ctx,mid,it=200)
        if up<1: hi=mid
        else: lo=mid
    ps=pstar(m)
    up,low,w=anal.rho(ctx,ps,it=300)
    return hi, ps, up, low
if __name__=='__main__':
    fn=sys.argv[1]; m=int(sys.argv[2])
    hi,ps,up,low=crit(fn,m)
    print('%s m %d  m*p_crit %.5f  m*p* %.5f  at p*: rho_up %.5f rho_low %.5f  %s'%(fn,m,m*hi,m*ps,up,low,'PASS' if up<1 else 'fail'),flush=True)

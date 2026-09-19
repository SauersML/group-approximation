from prof import *
for q in [2,3,4,6,8]:
    n=240*q//q*1  # keep n fixed-ish multiple of q
    n=720; L=n//(2*q); be=L//3; ga=L-be; al=n-L; th=n//q
    p,a=profile(arcx(n,th,al,be,ga),80,80)
    print(q,n,'L',L,'rho>=%.2f'%p,a,flush=True)

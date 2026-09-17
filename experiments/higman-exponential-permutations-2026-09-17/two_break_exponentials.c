/* Enumerate two-breakpoint order-four exponential permutations of Z/pZ.
 *
 * If f in Sym(Z/pZ) has exactly two doubling breakpoints then (since 0 is fixed by x->2x,
 * the point mapped to 0 is its own run) the multiplication-by-2 map has at most two cycles
 * on Z/p, so p is prime with 2 a primitive root (or p=3), and
 *     f(s-1) = 0,  f(s+k) = g * 2^k  (k = 0..p-2),   s in Z/p, g in (Z/p)^*.
 * This program checks f^4 = id for all p(p-1) candidates, for primes p <= PMAX with 2 primitive.
 * Output: one line per prime: p, number of solutions, first solution (s,g).
 * Usage: two_break_exponentials PMAX
 */
#include <stdio.h>
#include <stdlib.h>

static int is_prime(int n){ if(n<2) return 0; for(int d=2; d*d<=n; d++) if(n%d==0) return 0; return 1; }
static int ord2(int p){ long x=2%p; int k=1; while(x!=1){ x=(x*2)%p; k++; if(k>p) return -1;} return k; }

int main(int argc, char **argv){
  int PMAX = argc>1 ? atoi(argv[1]) : 1000;
  int *f = malloc(sizeof(int)*(PMAX+1));
  long *pw = malloc(sizeof(long)*(PMAX+1));
  for(int p=3; p<=PMAX; p+=2){
    if(!is_prime(p) || ord2(p)!=p-1) continue;
    pw[0]=1; for(int k=1;k<p;k++) pw[k]=(pw[k-1]*2)%p;
    long count=0; int fs=-1, fg=-1;
    for(int s=0; s<p; s++){
      for(int g=1; g<p; g++){
        f[(s-1+p)%p]=0;
        for(int k=0;k<=p-2;k++) f[(s+k)%p]=(int)((g*pw[k])%p);
        int ok=1;
        for(int x=0;x<p && ok;x++){ int y=f[f[f[f[x]]]]; if(y!=x) ok=0; }
        if(ok){ count++; if(fs<0){fs=s;fg=g;} }
      }
    }
    printf("%d %ld %d %d\n", p, count, fs, fg); fflush(stdout);
  }
  return 0;
}

/* canon.c -- print the canonical representative (as stored by thzsearch.c) of each input pair. usage: canon RANK < pairs */
#define main thz_main_unused
#include "thzsearch.c"
#undef main
int main(int argc, char **argv) {
    RANK = atoi(argv[1]); init_perms();
    char s1[256], s2[256];
    while (scanf("%255s %255s", s1, s2) == 2) {
        Word p, q, a, b; parse(s1, &p); parse(s2, &q);
        Key k = canon_pair(&p, &q); unpack(k, &a, &b);
        char t1[256], t2[256]; wstr(&a, t1); wstr(&b, t2); printf("%s %s\n", t1, t2);
    }
    return 0;
}

"""Window-2 census over Z for the height-one survivors: long fences and crowns.
Reuses run() from search_z.py. Run: python3 search_z_height1.py"""
from search_z import run

H1 = {
    # fence a1<c1>m1<c2>m2<c3 : minima 0,2,4 ; tops 1,3,5
    'fence6': (6, [(0, 1), (2, 1), (2, 3), (4, 3), (4, 5)]),
    # fence7 a1<c1>m1<c2>m2<c3>a3
    'fence7': (7, [(0, 1), (2, 1), (2, 3), (4, 3), (4, 5), (6, 5)]),
    # crown C6: minima 0,1,2 ; tops 3,4,5 ; m_i < c_i, c_{i+1}
    'crown6': (6, [(0, 3), (0, 4), (1, 4), (1, 5), (2, 5), (2, 3)]),
}

if __name__ == '__main__':
    for name, (n, rel) in H1.items():
        run(name, n, rel)

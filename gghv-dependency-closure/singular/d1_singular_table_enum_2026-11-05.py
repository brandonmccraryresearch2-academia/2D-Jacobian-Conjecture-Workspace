"""(iv) S2 table arithmetic + (v) [GGV5] enumeration recompute — Python exact ints.
Primary tool for the table/enumeration checks (Singular is the wrong tool for
list arithmetic; the Singular-side record for (v) is the PLLC filter script).
Second tool: python-flint (fmpz) for the integer identities.
"""
import sys
from fractions import Fraction

ok = True
def check(name, got, want):
    global ok
    status = "PASS" if got == want else "FAIL"
    if got != want: ok = False
    print(f"[{status}] {name}: got {got!r}, want {want!r}")

# ---- (iv) S2 table, Part 1 / Part 28 / Part 31 / Part 32 ----
table = [  # (A0, (m,n), maxDeg)
    ((4,12),(3,4),64), ((4,12),(5,7),112), ((5,20),(2,3),75), ((5,20),(3,2),75),
    ((7,21),(2,3),84), ((8,24),(2,3),96), ((8,28),(3,2),108), ((8,32),(3,2),120),
    ((9,24),(2,3),99), ((9,27),(2,3),108),
]
def degree_pair(r):
    (a,b),(m,n),_ = r
    return (m*(a+b), n*(a+b))
def pair_max(r):
    p = degree_pair(r); return max(p)
check("table length", len(table), 10)
check("table max degrees (family formula)", [pair_max(r) for r in table],
      [64,112,75,75,84,96,108,120,99,108])
check("table stated maxDeg == computed", [r[2] for r in table],
      [pair_max(r) for r in table])
check("table degree pairs", [degree_pair(r) for r in table],
      [(48,64),(80,112),(50,75),(75,50),(56,84),(64,96),(108,72),(120,80),(66,99),(72,108)])
check("all maxDeg < 125", all(r[2] < 125 for r in table), True)
red = [0,1,2,3,5]
check("exactly 5 red rows", len(red), 5)
remaining = [r for i,r in enumerate(table) if i not in red and r[2] not in (84,120)]
check("S2 survivors after red + 84 + 120 discards (degree pairs)",
      [degree_pair(r) for r in remaining], [(108,72),(66,99),(72,108)])
check("remaining max degrees (non-red rows)", [r[2] for i,r in enumerate(table) if i not in red],
      [84,108,120,99,108])
check("row828 degree pair", degree_pair(table[6]), (108,72))
check("row828 swapped = (72,108)", degree_pair(table[6])[::-1], (72,108))
check("(72,108) arises from two rows: (9,27) direct", degree_pair(table[9]), (72,108))
check("(72,108) arises from two rows: (8,28) swapped", degree_pair(table[6])[::-1], (72,108))
check("(5,20) A0 in exactly two rows",
      [r for r in table if r[0]==(5,20)], [((5,20),(2,3),75), ((5,20),(3,2),75)])
check("source count 7 + 3 = 10", 7+3, len(table))
import math
check("gcd(72,108)", math.gcd(72,108), 36)
check("(72,108) reduced ratio", (72//36, 108//36), (2,3))

# ---- (v) PLLC filter / PFL loop / row degrees ----
from math import gcd
def pllc_filter(a,b):
    return (b < a) and (b <= (a-b-1)**2) and (b + gcd(a,b) != a)
def pllc_dir(a,b):
    if b == 0: return (0,-1)
    if a > 2*b: return (1,-2)
    return (1,-1)
check("pllcFilter(8,3)", pllc_filter(8,3), True)
check("pllcFilter(8,4)", pllc_filter(8,4), False)
check("pllcDir(8,3)", pllc_dir(8,3), (1,-2))
check("pllcDir(8,4)", pllc_dir(8,4), (1,-1))
cands9 = [(a,b) for a in range(10) for b in range(a+1) if pllc_filter(a,b)]
check("(8,3) in pllcCandidates(9)", (8,3) in cands9, True)
check("(8,4) not in pllcCandidates(9)", (8,4) in cands9, False)
print("pllcCandidates(9) =", cands9)
pfl9 = [((a,b), pllc_dir(a,b)) for (a,b) in cands9]
check("((8,3),(1,-2)) in pfl(9)", ((8,3),(1,-2)) in pfl9, True)
check("((7,4),(1,-1)) in pfl(9)", ((7,4),(1,-1)) in pfl9, True)
def earlier(pfl, a, b):
    return [x for x in pfl if x[0][0] < a and x[0][1] < b and (x[0][0]-x[0][1]) < (a-b)]
check("(3,1) in earlierPairs(pfl9,7,4)", ((3,1),(1,-2)) in earlier(pfl9,7,4), True)
check("(8,3) not in earlierPairs(pfl9,7,4)", ((8,3),(1,-2)) in earlier(pfl9,7,4), False)
check("rowMaxDeg == table max in all 10 rows",
      all(max(r[1][0],r[1][1])*(r[0][0]+r[0][1]) == r[2] for r in table), True)

# ---- second tool: python-flint fmpz identities ----
from flint import fmpz
f = lambda n: fmpz(n)
check("flint: gcd(72,108)", int(f(72).gcd(f(108))), 36)
check("flint: gcd(8,4)", int(f(8).gcd(f(4))), 4)
check("flint: 4+gcd(8,4)", int(f(4)+f(8).gcd(f(4))), 8)
check("flint: 6*4==3*8", int(f(6)*f(4)-f(3)*f(8)), 0)
check("flint: 21*4==3*28", int(f(21)*f(4)-f(3)*f(28)), 0)
check("flint: 7*(2*2)==28", int(f(7)*(f(2)*f(2))), 28)
check("flint: I_M rational 7*(4/7)==4", Fraction(7)*(Fraction(4,7)), Fraction(4,1))
check("flint: I_m rational 1-((-3+1)+7*(-9/7+1))==5",
      Fraction(1)-((Fraction(-3)+1)+7*(Fraction(-9,7)+1)), Fraction(5,1))

print("OVERALL:", "ALL PASS" if ok else "FAILURES PRESENT")
sys.exit(0 if ok else 1)

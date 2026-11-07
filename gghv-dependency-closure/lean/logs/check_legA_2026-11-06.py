#!/usr/bin/env python3
"""Leg A second-tool check (I1, not kernel): recompute every arithmetic claim
of gghv_full_s2s3_2026-11-06.lean independently in Python (fractions).
Run on lean-build-3. Exit 0 iff ALL PASS."""
from fractions import Fraction as Q
import math, sys

fails = []
def check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond:
        fails.append(name)

# E2 table: degree pairs, max degrees, bound <125
table = [((4,12),(3,4),64), ((4,12),(5,7),112), ((5,20),(2,3),75),
         ((5,20),(3,2),75), ((7,21),(2,3),84), ((8,24),(2,3),96),
         ((8,28),(3,2),108), ((8,32),(3,2),120), ((9,24),(2,3),99),
         ((9,27),(2,3),108)]
pairs = [(m*(a+b), n*(a+b)) for (a,b),(m,n),_ in table]
check("table_degree_pairs", pairs == [(48,64),(80,112),(50,75),(75,50),(56,84),
      (64,96),(108,72),(120,80),(66,99),(72,108)])
check("table_max_degrees", [max(p) for p in pairs] == [64,112,75,75,84,96,108,120,99,108])
check("table_below_125", all(mx < 125 for _,_,mx in table))
check("pairMax_eq_maxDeg", all(max(p) == mx for p,(_,_,mx) in zip(pairs, table)))
red = table[:4] + [table[5]]
check("redRows_length_5", len(red) == 5)
surv = [p for row,p in zip(table,pairs) if row not in red and row[2] not in (84,120)]
check("survivors_pairs", surv == [(108,72),(66,99),(72,108)])
check("gcd_72_108", math.gcd(72,108) == 36)
check("ratio_72_108", (72//36, 108//36) == (2,3))
check("pair_108_72_unique", [r for r,p in zip(table,pairs) if p==(108,72)] == [table[6]])
check("pair_72_108_unique", [r for r,p in zip(table,pairs) if p==(72,108)] == [table[9]])
check("rowsA0_520_twice", sum(1 for (a,b),_,_ in table if (a,b)==(5,20)) == 2)

# E3 120: direction, en uniqueness, d0, corner, prop329
check("v_120_direction", Q(4)*8 + Q(-1)*28 == Q(4)*Q(11,4) + Q(-1)*7 == 4)
mu = Q(3,4)
check("v_120_en_unique", Q(4)*(mu*8) + Q(-1)*(mu*28) == 3 and mu == Q(3,4))
check("discard_120_data", 6*4 == 3*8 and 21*4 == 3*28)
check("gcd_2_7", math.gcd(2,7) == 1)
check("d0_bound", all(d == 4 for d in range(1,9) if d*2 == 8 and d*7 == 28))
check("d0_forced_4", all(d0 == 4 for d0 in range(1,5) if d0 % 4 == 0))
check("corner_120_exponents", all(2*(4*m) == 8*m and 1*(4*m) == 4*m for m in range(0,10)))
check("prop329_exclusion", 4 + math.gcd(8,4) == 8)

# E4 84: IM general + j0, Im, factor count
check("im_84_general", all(7*(2*(j+2))*Q(1,7) == 2*(j+2) for j in range(0,10)))
check("im_84_at_j0", 7*(2*2)*Q(1,7) == 4)
check("minor_delta_step", Q(-9,7) + 1 == Q(-2,7))
check("im_minor_84_rat", Q(1) - (-3+1) - 7*(Q(-9,7)+1) == 5)
check("factor_count_84", 7+7 == 14 and (2+1)*7 == 21)
check("discard_84_numeric", 4 < 5)

# E10/E18 endgames
check("thm5_bounds", 12+9*7 == 75 and 22+8+42+4 == 76)
check("thm5_g_degree", 66+3*4 == 78)
check("thm6_degrees_at_k2", 15+6*2 == 27 and 9+9*2 == 27)

print("OVERALL " + ("ALL PASS" if not fails else f"FAILURES: {fails}"))
sys.exit(0 if not fails else 1)

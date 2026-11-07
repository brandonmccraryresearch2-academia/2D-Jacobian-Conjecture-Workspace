#!/usr/bin/env python3
"""depth6_enum.py -- Enumerate depth-6 trees with >=2 dicritical candidates
with m >= 3 (kappa >= 7, kappa odd).

EPISTEMIC STATUS (2026-10-01): finite combinatorial enumeration using
kappa = 3*nu - c (from jet_engine.py). Not a geometric realizability proof.
"""
print("=" * 70)
print("Depth-6 enumeration: >=2 dicritical candidates with m>=3 (kappa>=7)")
print("=" * 70)


class State:
    def __init__(self):
        self.divs = {'L': {'nu': 1, 'c': 0, 'selfint': 1}}
        self.edges = set()
        self.next_id = 0

    def copy(self):
        s = State.__new__(State)
        s.divs = {k: dict(v) for k, v in self.divs.items()}
        s.edges = set(self.edges)
        s.next_id = self.next_id
        return s

    def kappa(self, i):
        d = self.divs[i]
        return 3 * d['nu'] - d['c']

    def blowup_smooth(self, i):
        s = self.copy()
        j = f"E{s.next_id}"
        s.next_id += 1
        di = s.divs[i]
        s.divs[j] = {'nu': di['nu'], 'c': 1 + di['c'], 'selfint': -1}
        di['selfint'] -= 1
        s.edges.add(frozenset({i, j}))
        return s

    def blowup_crossing(self, i, k):
        s = self.copy()
        j = f"E{s.next_id}"
        s.next_id += 1
        di, dk = s.divs[i], s.divs[k]
        s.divs[j] = {'nu': di['nu'] + dk['nu'],
                     'c': 1 + di['c'] + dk['c'], 'selfint': -1}
        di['selfint'] -= 1
        dk['selfint'] -= 1
        s.edges.discard(frozenset({i, k}))
        s.edges.add(frozenset({i, j}))
        s.edges.add(frozenset({j, k}))
        return s

    def children(self):
        out = [self.blowup_smooth(i) for i in self.divs]
        for e in self.edges:
            i, k = tuple(e)
            out.append(self.blowup_crossing(i, k))
        return out

    def cands_m3(self):
        return [i for i in self.divs if i != 'L'
                and self.kappa(i) % 2 == 1 and self.kappa(i) >= 7]


states = [State()]
for depth in range(0, 7):
    hits = [s for s in states if len(s.cands_m3()) >= 2]
    ktypes = sorted(set(
        tuple(sorted((s.kappa(i), (s.kappa(i) - 1) // 2)
                     for i in s.cands_m3()))
        for s in hits))
    print(f"depth {depth}: {len(states)} trees, "
          f"{len(hits)} with >=2 m>=3 candidates")
    for kt in ktypes[:15]:
        print(f"    (kappa,m) of m>=3 cands: {kt}")
    if ktypes and len(ktypes) > 15:
        print(f"    ... and {len(ktypes) - 15} more kappa-types")
    if depth < 6:
        states = [c for s in states for c in s.children()]

print()
print("Minimal (kappa,m) pair-types with two m>=3 candidates identified above.")

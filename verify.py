#!/usr/bin/env python3
"""Standard-library verifier for the two-pendant 49a certificate (sunflower3 v1, see FORMAT.md).

    python3 verify.py CERT.txt[.xz] [--pure] [--extra]

--pure: the certificate also contains the 20 sets inside the H1 pendant (PURE_H1 below).
--extra: it also contains the sets in EXTRA below (core edges plus H2 points, empty H1 part).

What it checks:
 1. The certificate parses (strict FORMAT v1, one block). It prints the sha256 of the uncompressed text.
 2. F and H (Cla2026) are rebuilt from their definitions and checked by brute force (Sperner, 3-sunflower-free).
    H has the pendant property: the sets D \\ {0} (D in H) are nonempty and pairwise intersecting.
 3. The 15 + 15 added edge sets satisfy the core-level conditions of Lemma A (PROOF.md) for F at the edges (0,3) and
    (0,4).
 4. The block is rebuilt from the construction (and the pure sets, with --pure). It must equal the certificate's
    block as a set, with the same member count.
 5. --pure / --extra: every pair and triple involving one of the 20 pure sets or an EXTRA set is checked
    exhaustively against the whole block.
 6. Port counts, T, and the Perron root as a surd. Integer proofs of rate > PR #237 and > Cla2026, and a
    10-digit interval for the rate.
 7. Negative controls: every check above must reject a planted defect.

With DEGKM Lemma 4.4 and Lemma A (PROOF.md), checks 2-5 prove the block Sperner and 3-sunflower-free. check.c checks
the same block exhaustively without using the lemmas.
"""
import hashlib
import lzma
import re
import sys
from itertools import combinations, permutations
from math import isqrt

# ---------------------------------------------------------------- the construction

EDGES = list(combinations(range(5), 2))                      # edge (u,v) of K5 <-> index in this list
E03, E04 = EDGES.index((0, 3)), EDGES.index((0, 4))
# block points: 0..7 = the K5 edges other than (0,3),(0,4) in order; 8..17 = H1 points 1..10; 18..27 = H2 points 1..10
CORE = [i for i in range(10) if i not in (E03, E04)]
CORE_BIT = {e: k for k, e in enumerate(CORE)}
PORT_P, PORT_Q, NPTS = CORE_BIT[EDGES.index((0, 1))], CORE_BIT[EDGES.index((0, 2))], 28

A1 = ["01 02 04 12 13 14 23", "01 04 13 23 24", "01 02 12 13 14 23 24", "02 04 12 13 14 23 24", "02 04 12 13 34",
      "01 02 14 23 34", "01 04 12 13 14 23 34", "01 02 04 13 14 24 34", "01 02 12 13 14 24 34",
      "01 04 12 13 14 24 34", "01 02 04 12 23 24 34", "01 02 12 13 23 24 34", "01 04 12 14 23 24 34",
      "02 04 12 14 23 24 34", "02 04 13 14 23 24 34"]       # empty H1 part; edge sets avoiding (0,3)
A2 = ["02 03 13 14 24", "01 02 03 12 14 23 24", "01 02 12 13 14 23 24", "01 03 12 13 14 23 24",
      "01 02 03 12 13 14 34", "01 02 14 23 34", "01 03 12 13 14 23 34", "02 03 12 13 14 23 34", "01 03 12 24 34",
      "01 02 12 13 14 24 34", "01 02 03 13 23 24 34", "01 02 12 13 23 24 34", "02 03 12 13 23 24 34",
      "02 03 12 14 23 24 34", "01 03 13 14 23 24 34"]       # empty H2 part; edge sets avoiding (0,4)
PURE_H1 = ["1 2 3 5 6 8", "2 3 4 6 7 9", "1 2 3 4 5 7 8 9", "1 2 4 5 6 7 8 9", "1 3 4 5 6 7 8 9",
           "1 2 3 4 5 6 7 10", "3 4 5 7 8 10", "1 2 3 4 6 7 8 10", "1 2 4 5 6 7 8 10", "1 2 3 4 5 6 9 10",
           "1 2 3 4 5 7 9 10", "1 5 6 7 9 10", "1 2 4 8 9 10", "1 3 4 5 6 8 9 10", "2 3 4 5 6 8 9 10",
           "1 2 3 5 7 8 9 10", "1 2 3 6 7 8 9 10", "1 3 4 6 7 8 9 10", "2 3 5 6 7 8 9 10",
           "2 4 5 6 7 8 9 10"]                                # subsets of H1's points 1..10 (no core, no H2 part)
EXTRA = [("12 14 23", "1 2 3 4 5 6 7 8 9 10")]               # (K5 edges, H2 points); empty H1 part


def emask(pairs):
    return sum(1 << EDGES.index((min(u, v), max(u, v))) for u, v in pairs)


def edge_set(s):
    return emask([(int(t[0]), int(t[1])) for t in s.split()])


def family_F():
    """75 sets on the edges of K5: 5 stars, 10 K_{2,3}, 60 complements of chairs."""
    fam = set()
    for v in range(5):
        fam.add(emask([e for e in EDGES if v in e]))
    for a, b in combinations(range(5), 2):
        rest = [x for x in range(5) if x not in (a, b)]
        fam.add(emask([(x, y) for x in (a, b) for y in rest]))
    for c, l1, l2, l3, ext in permutations(range(5)):      # chair: centre c, legs l1,l2,l3, l1 extended to ext
        fam.add(1023 ^ emask([(c, l1), (c, l2), (c, l3), (l1, ext)]))
    return sorted(fam)


def family_H():
    """121 sets on Z11: images of three base sets under x -> ax+b, a a nonzero square."""
    sq = {a * a % 11 for a in range(1, 11)}
    return sorted({sum(1 << ((a * x + b) % 11) for x in base)
                   for base in ([0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 6, 7], [0, 1, 2, 6, 9])
                   for a in sq for b in range(11)})


def is_valid_brute(fam):
    """Distinct, Sperner and 3-sunflower-free, by brute force over all pairs and triples."""
    if len(set(fam)) != len(fam):
        return False
    for a, b in combinations(fam, 2):
        if a & b in (a, b):
            return False
    for a, b, c in combinations(fam, 3):
        if a & b == a & c == b & c:
            return False
    return True


def core_bits(C):
    """K5 edge set (10-bit) minus (0,3),(0,4) -> block bits 0..7."""
    return sum(1 << CORE_BIT[e] for e in CORE if C >> e & 1)


def pendant_parts(H, glue_edge_in):
    """The possible parts of a member in a pendant copy of H (as 10-bit masks on points 1..10)."""
    if glue_edge_in:
        return [D >> 1 for D in H if not D & 1]                # D in H, 0 not in D
    return [D >> 1 for D in H if D & 1]                        # D \ {0}, 0 in D


def build(F, H, A1m, A2m, pure, extra=()):
    """The block on 28 points (a list, product sets first)."""
    out = []
    for C in F:                                                # product sets (DEGKM twice)
        c = core_bits(C)
        for q1 in pendant_parts(H, C >> E03 & 1):
            for q2 in pendant_parts(H, C >> E04 & 1):
                out.append(c | q1 << 8 | q2 << 18)
    for T in A1m:                                              # empty H1 part, H2 part as for a member of F
        out += [core_bits(T) | q2 << 18 for q2 in pendant_parts(H, T >> E04 & 1)]
    for T in A2m:
        out += [core_bits(T) | q1 << 8 for q1 in pendant_parts(H, T >> E03 & 1)]
    out += [S << 8 for S in pure]
    out += list(extra)
    return out


def lemma_a_core_conditions(F, x, A):
    """Lemma A, single pendant, at point x of the core F: A lies on the core minus x and is distinct, Sperner and
    sunflower-free; no T in A lies inside a member of F'; and no C' in F' and T1 != T2 in A have
    C' & T1 == C' & T2 == T1 & T2. Here F' = {C - x : x in C} u {C : x not in C}."""
    if any(T >> x & 1 for T in A) or not is_valid_brute(A):
        return False
    Fp = [C & ~(1 << x) for C in F]
    for T in A:
        if any(T & ~Cp == 0 for Cp in Fp):
            return False
    for Cp in Fp:
        for T1, T2 in combinations(A, 2):
            if Cp & T1 == Cp & T2 == T1 & T2:
                return False
    return True


H1_BITS, H2_BITS = ((1 << 10) - 1) << 8, ((1 << 10) - 1) << 18


def pure_exhaustive(block, pure_masks, far=H2_BITS):
    """Every pair and triple of the block that involves one of the new sets pure_masks, which must all avoid the
    pendant region `far` (H2 for the pure H1 sets, H1 for EXTRA): None if there is no containment and no 3-sunflower,
    else the reason."""
    assert far in (H1_BITS, H2_BITS) and not any(S & far for S in pure_masks)
    pset = set(pure_masks)
    rest = [B for B in block if B not in pset]
    for S in pure_masks:
        if any(S & ~B == 0 or B & ~S == 0 for B in block if B != S):
            return "containment"
    # {S, A, B} with A, B from the rest. S avoids the region `far`, so A and B need disjoint parts there (possibly
    # empty). Most nonempty parts there pairwise intersect (pendant parts D \ {0}, pendant_property), but not all:
    # e.g. a pure H1 set can miss a pendant part. So for every pair of disjoint nonempty part values, take the members
    # carrying the rarer of the two. In any such triple, one of A, B, say X, then has an empty part in `far` or lies
    # in that list. Bucket the rest by B & S and, for each such X, look for a partner in X's bucket whose part outside
    # S is disjoint from X's. This covers every such triple exactly.
    count = {}
    for B in rest:
        count[B & far] = count.get(B & far, 0) + 1
    vals = [v for v in count if v]
    rare = {u if count[u] <= count[v] else v for u, v in combinations(vals, 2) if not u & v}
    no_h2 = [B for B in rest if not B & far or B & far in rare]
    for S in pure_masks:
        buckets = {}
        for B in rest:
            buckets.setdefault(B & S, []).append(B & ~S)
        for X in no_h2:
            ox = X & ~S
            if sum(1 for o in buckets.get(X & S, ()) if o & ox == 0) > (1 if ox == 0 else 0):
                return "sunflower with two block members"
    for S1, S2 in combinations(pure_masks, 2):               # {S, S', A}: A & (S | S') == S & S'
        U, K = S1 | S2, S1 & S2
        if any(A & U == K for A in rest):
            return "sunflower with another pure set"
    for a, b, c in combinations(pure_masks, 3):
        if a & b == a & c == b & c:
            return "sunflower of pure sets"
    return None


def pendant_property(H):
    """D \\ {0} (D in H) nonempty and pairwise intersecting. It forces the H2 parts of members with nonempty H2 part
    to pairwise intersect. pure_exhaustive relies on this and checks the instance directly too."""
    parts = [D & ~1 for D in H]
    return all(parts) and all(a & b for a, b in combinations(parts, 2))


# ---------------------------------------------------------------- certificate

INT = re.compile(r"0|[1-9][0-9]*")


def parse(text):
    if "\r" in text:
        raise ValueError("CR")
    lines = [l for l in text.split("\n") if not l.startswith("#")]
    while lines and lines[-1] == "":
        lines.pop()
    if not lines or lines[0] != "sunflower3 v1":
        raise ValueError("header")
    blocks, i = [], 1
    while i < len(lines):
        t = lines[i].split(" ")
        if len(t) != 5 or t[0] != "block" or not all(INT.fullmatch(x) for x in t[1:]):
            raise ValueError(f"bad block line {i}")
        n, p, q, m = map(int, t[1:])
        if not (3 <= n <= 64 and 0 <= p < n and 0 <= q < n and p != q and m >= 1) or i + 1 + m > len(lines):
            raise ValueError("bad block header")
        fam = []
        for line in lines[i + 1:i + 1 + m]:
            if line == "-":
                fam.append(0)
                continue
            pts = line.split(" ")
            if not all(INT.fullmatch(x) for x in pts):
                raise ValueError("bad token")
            v = list(map(int, pts))
            if any(b <= a for a, b in zip(v, v[1:])) or v[-1] >= n:
                raise ValueError("points not increasing / out of range")
            fam.append(sum(1 << x for x in v))
        blocks.append((n, p, q, fam))
        i += 1 + m
    if not blocks:
        raise ValueError("no block")
    return blocks


# ---------------------------------------------------------------- exact arithmetic

def ports(fam, p, q):
    N = [[0, 0], [0, 0]]
    for D in fam:
        N[D >> p & 1][D >> q & 1] += 1
    return N


def rho_enclosure(tr, disc, scale):
    """Integers lo, hi with lo/scale <= (tr + sqrt(disc))/2 <= hi/scale (disc >= 0)."""
    r = isqrt(disc * scale * scale)
    return (tr * scale + r) // 2, (tr * scale + r + 1) // 2 + 1


def iroot(x, k):
    """floor(x^(1/k)) for integers x >= 0, k >= 1."""
    if x < 2:
        return x
    y = 1 << ((x.bit_length() + k - 1) // k)
    while True:
        z = ((k - 1) * y + x // y ** (k - 1)) // k
        if z >= y:
            break
        y = z
    while y ** k > x:
        y -= 1
    while (y + 1) ** k <= x:
        y += 1
    return y


def beats(A, L, B, Lb, scale=10 ** 8):
    """Proves (tr_A + sqrt(disc_A))/2 ^(1/L) > (... B ...)^(1/Lb), i.e. rho_A^Lb > rho_B^L, from integer enclosures."""
    loA, _ = rho_enclosure(*A, scale)
    _, hiB = rho_enclosure(*B, scale)
    return loA ** Lb * scale ** L > hiB ** L * scale ** Lb


def rate_interval(tr, disc, L, digits=10, scale=10 ** 12):
    """Integers a, a+1 with a/10^digits <= rho^(1/L) < (a+1)/10^digits."""
    lo, hi = rho_enclosure(tr, disc, scale)
    a = iroot(lo * 10 ** (digits * L) // scale, L)              # a^L <= lo/scale * 10^(dL)
    b = iroot(hi * 10 ** (digits * L) // scale, L) + 1           # b^L > hi/scale * 10^(dL)
    return a, b


# ---------------------------------------------------------------- main

def extra_masks():
    return [core_bits(edge_set(e)) | sum(1 << (17 + int(x)) for x in h2.split()) for e, h2 in EXTRA]


def main(path, pure, extra=False):
    raw = open(path, "rb").read()
    if path.endswith(".xz"):
        raw = lzma.decompress(raw)
    print("certificate sha256 (uncompressed):", hashlib.sha256(raw).hexdigest())
    blocks = parse(raw.decode("ascii"))
    assert len(blocks) == 1, "expected one block"
    n, p, q, fam = blocks[0]
    assert (n, p, q) == (NPTS, PORT_P, PORT_Q), (n, p, q)
    print(f"parsed: n={n} p={p} q={q} m={len(fam)}")

    F, H = family_F(), family_H()
    assert len(F) == 75 and len(H) == 121
    assert is_valid_brute(F) and is_valid_brute(H), "F or H invalid"
    assert pendant_property(H), "H lacks the pendant property"
    print("F (75) and H (121): Sperner, 3-sunflower-free; H \\ 0 parts nonempty, pairwise intersecting")

    A1m, A2m = [edge_set(s) for s in A1], [edge_set(s) for s in A2]
    assert lemma_a_core_conditions(F, E03, A1m) and lemma_a_core_conditions(F, E04, A2m)
    print("A1 at (0,3), A2 at (0,4): Lemma A core-level conditions hold")

    pure_sets = [sum(1 << (int(x) - 1) for x in s.split()) for s in PURE_H1] if pure else []
    ext = extra_masks() if extra else []
    built = build(F, H, A1m, A2m, pure_sets, ext)
    assert len(set(built)) == len(built) == len(fam) and set(built) == set(fam), "certificate != construction"
    print(f"certificate block == construction ({len(fam)} sets: 250659 product, {len(fam) - 250659} added)")

    if pure:
        why = pure_exhaustive(fam, [S << 8 for S in pure_sets])
        assert why is None, "pure sets: " + why
        print("20 pure H1 sets: all pairs and triples through them checked exhaustively")
    if extra:
        why = pure_exhaustive(fam, ext, far=H1_BITS)
        assert why is None, "extra sets: " + why
        print(f"{len(ext)} EXTRA set(s): all pairs and triples through them checked exhaustively")

    N = ports(fam, p, q)
    T = [[N[1][0], N[1][1]], [N[0][0], N[0][1]]]
    tr, disc = T[0][0] + T[1][1], (T[0][0] - T[1][1]) ** 2 + 4 * T[0][1] * T[1][0]
    L = n - 2
    print(f"N00={N[0][0]} N01={N[0][1]} N10={N[1][0]} N11={N[1][1]};  T rows {T[0]}, {T[1]};  L={L}")
    print(f"rho = ({tr} + sqrt({disc}))/2" + (f" = {tr // 2} + sqrt({disc // 4})" if tr % 2 == 0 and disc % 4 == 0 else ""))
    PR237 = (2254, 4 * 925536)                                  # 1127 + sqrt(925536), 17 points
    CLA = (2084, 4 * 1044828)                                   # 1042 + 2 sqrt(261207), 17 points
    assert beats((tr, disc), L, PR237, 17), "does not beat PR #237"
    assert beats((tr, disc), L, CLA, 17), "does not beat Cla2026"
    a, b = rate_interval(tr, disc, L)
    print(f"proved: {a / 1e10:.10f} <= rho^(1/{L}) < {b / 1e10:.10f}   (integers {a}, {b})")
    print("proved: rate > PR #237 (1127+sqrt(925536))^(1/17) and > Cla2026 (1042+2sqrt(261207))^(1/17)")

    # negative controls
    bad_T = next(C & ~(1 << E03) for C in F if C >> E03 & 1)    # a member of F' itself: violates "T inside no C'"
    assert not lemma_a_core_conditions(F, E03, A1m + [bad_T]), "control: core condition"
    assert not lemma_a_core_conditions(F, E03, A1m + [A1m[0] | 1 << E03]), "control: T must avoid x"
    mutated = list(fam)
    mutated[0] ^= 1 << 27
    assert set(built) != set(mutated), "control: rebuild comparison"
    assert not pendant_property(H + [0b11]), "control: pendant property"
    # pure_exhaustive must catch a planted defect in each of its branches; the witnesses are built by hand
    P = [sum(1 << (int(x) - 1) for x in t.split()) << 8 for t in PURE_H1]
    base = fam if pure else fam + P
    S1, S2 = P[0], P[1]
    B = next(B for B in fam if B & 0xFF != 0xFF and B & S1)  # a member that meets S1 and misses a core point
    X = (B & S1) | (0xFF & ~B)                                  # X & S1 = B & S1, X - S1 disjoint from B: {S1, B, X}
    for planted, want in (((S1 | 1 << 17) if not S1 >> 17 & 1 else (S1 & ~(1 << 17)), "containment"),
                          (X, "sunflower with two block members"),
                          ((S1 & S2) | 1 | H2_BITS, "sunflower with another pure set")):
        why = pure_exhaustive(base + [planted], P)
        assert why == want, f"control {want}: got {why}"
    if extra:                                                  # the far=H1 branch, with a hand-built witness
        X0 = ext[0]
        B = next(B for B in fam if B & X0 and 0xFF & ~X0 & ~B and B != X0)
        Y = (B & X0) | (0xFF & ~X0 & ~B)                         # empty H1 part; {X0, B, Y} is a sunflower
        why = pure_exhaustive(fam + [Y], ext, far=H1_BITS)
        assert why == "sunflower with two block members", f"control extra: got {why}"
    # a sunflower whose partners have disjoint *nonempty* parts in `far` (no member with an empty part there): the
    # rare-value list must catch it (review r-d06baf3d)
    syn = [1 << 8, 1 << 9 | 1]
    assert pure_exhaustive(syn + [1 << 1], [1 << 1], far=H1_BITS) == "sunflower with two block members", "control: rare"
    print("negative controls rejected as expected (core conditions, rebuild, pendant property, 3 planted defects)")
    assert not beats(PR237, 17, (tr, disc), L), "control: comparison is not symmetric"
    print("ALL CHECKS PASS")


if __name__ == "__main__":
    if sys.flags.optimize:                                     # every check below is an assert; -O would skip them all
        sys.exit("verify.py: refusing to run under python -O / PYTHONOPTIMIZE (its checks are asserts)")
    main(sys.argv[1], "--pure" in sys.argv[2:], "--extra" in sys.argv[2:])

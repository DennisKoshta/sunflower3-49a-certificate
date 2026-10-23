#!/usr/bin/env python3
"""Independent exact-combinatorial, algebraic-surd, and interval verifier for the
Erdos-Szemeredi 3-sunflower-free capacity constant (mu_3 / 49a).

References:
  - Tao et al., optimizationproblems constant 49a (constants/49a.md):
      C_49 = mu_3^S = lim_{n -> inf} f(n)^{1/n},
    where f(n) is the maximum size of a 3-sunflower-free family F subseteq 2^{[n]};
  - Erdos, Szemeredi (1978), Combinatorial properties of systems of sets,
    J. Combin. Theory Ser. A 24, 308-313;
  - Deuber, Erdos, Gunderson, Kostochka, Meyer (1997) [DEGKM1997], Intersection
    statements for systems of sets, J. Combin. Theory Ser. A 79, 118-132
    (Lemma 3.1: direct product of Sperner 3-free families; Lemma 4.4: gluing lemma);
  - Naslund, Sawin (2017), Upper bounds for sunflower-free sets, Forum Math. Sigma 5, e15;
  - IRSI (2026), teorth/optimizationproblems PR #200 (2x2 transfer-matrix chain count);
  - Claude (2026), teorth/optimizationproblems PR #220 (75-set K_5 family F and 121-set Z_11 family H);
  - Sylla (2026), teorth/optimizationproblems PR #237 (4364-set augmented glued family B').

Independent mathematical derivation from [DEGKM1997]:
  1. Gluing lemma ([DEGKM1997], Lemma 4.4):
     Let A and B be Sperner, 3-sunflower-free families of distinct subsets on disjoint
     ground sets X and Y, with ports a in X and b in Y. Partition A = A_1 sqcup A_0 by
     whether a in C, and B = B_1 sqcup B_0 by whether b in D. Define on (X cup Y) \\ {a, b}:
       G_1 = { (C \\ {a}) cup D : C in A_1, D in B_0 },
       G_2 = { C cup (D \\ {b}) : C in A_0, D in B_1 },
       G(A, a, B, b) = G_1 cup G_2.
     - Distinctness & size: Since X and Y are disjoint, M cap X and M cap Y uniquely
       recover (C, D) within G_1 and within G_2. If M_1 in G_1 and M_2 in G_2 satisfied
       M_1 subseteq M_2, intersecting with Y \\ {b} would give D_1 subseteq D_2 \\ {b}
       subsetneq D_2 (as b in D_2 \\ D_1), contradicting that B is Sperner; symmetrically
       M_2 subseteq M_1 contradicts that A is Sperner. Hence G_1 cap G_2 = empty,
       |G| = |A_1||B_0| + |A_0||B_1|, and G is Sperner.
     - 3-sunflower-freeness: Suppose distinct M_1, M_2, M_3 in G satisfy
       M_1 cap M_2 = M_1 cap M_3 = M_2 cap M_3. Their restrictions to X \\ {a} and
       Y \\ {b} also have equal pairwise intersections.
       * If all three lie in G_1 (or all three in G_2), their Y-parts D_1, D_2, D_3 in B_0
         satisfy D_1 cap D_2 = D_1 cap D_3 = D_2 cap D_3. Because B is Sperner and
         3-sunflower-free, D_1 = D_2 = D_3; restoring {a} to the X-parts similarly forces
         C_1 = C_2 = C_3 by the Sperner and 3-sunflower-free properties of A, so
         M_1 = M_2 = M_3, contradiction.
       * If two lie in G_1 and one in G_2 (say M_1, M_2 in G_1, M_3 in G_2), their Y-parts
         are D_1, D_2 in B_0 and D_3 \\ {b} with D_3 in B_1. Since b not in D_1, D_2,
         D_i cap (D_3 \\ {b}) = D_i cap D_3 for i = 1, 2, so D_1 cap D_2 = D_1 cap D_3 =
         D_2 cap D_3 in B. Since b in D_3 \\ (D_1 cup D_2), D_3 != D_1, D_2. If D_1 = D_2
         then D_1 = D_1 cap D_3 subsetneq D_3 (violating Sperner in B); if D_1 != D_2 then
         {D_1, D_2, D_3} is a 3-sunflower in B, contradiction. The case of one in G_1 and
         two in G_2 is symmetric on A.

  2. Periodic transfer-matrix chain (PRs #200, #220, #237):
     Let blocks B^{(1)}, ..., B^{(k)} be Sperner 3-sunflower-free families on ground sets
     of sizes n_1, ..., n_k >= 3 with distinct ports p_i != q_i in {0, ..., n_i - 1}.
     For block i, let
       N^{(i)}_{ab} = #{ D in B^{(i)} : [p_i in D] = a, [q_i in D] = b }  (a, b in {0, 1}),
       T_i = [[N^{(i)}_{10}, N^{(i)}_{11}],
              [N^{(i)}_{00}, N^{(i)}_{01}]].
     Take fresh disjoint copies B_1, B_2, ... cycling periodically through (1, ..., k).
     Set R_1 = B_1, and for j >= 1 glue the active out-port q^{(j)} of R_j to the in-port
     p^{(j+1)} of B_{j+1}:
       R_{j+1} = G(R_j, q^{(j)}, B_{j+1}, p^{(j+1)}).
     Since p^{(j+1)} != q^{(j+1)}, the new out-port q^{(j+1)} survives in R_{j+1}.
     Let u_j and w_j count the members of R_j avoiding and containing q^{(j)}.
     In R_{j+1}, members avoiding q^{(j)} (count u_j) pair with D in B_{j+1} containing
     p^{(j+1)} (counts N_{10}, N_{11} for q^{(j+1)} not in D, q^{(j+1)} in D), while
     members containing q^{(j)} (count w_j) pair with D avoiding p^{(j+1)} (counts
     N_{00}, N_{01}). Hence
       (u_{j+1}, w_{j+1}) = (u_j, w_j) T_{j+1},   with (u_1, w_1) = (1, 1) T_1.
     After t full periods of k blocks (j = t*k), let P = T_1 T_2 ... T_k (product in file
     order) and L = sum_{i=1}^k (n_i - 2). Then R_{tk} lives on L*t + 2 points and has
       |R_{tk}| = u_{tk} + w_{tk} = (1, 1) P^t (1, 1)^T.
     By Perron-Frobenius, any non-negative 2x2 matrix P has a non-negative right
     eigenvector v = (v_0, v_1)^T >= 0 for its spectral radius
       rho(P) = (tr(P) + sqrt((P_{00} - P_{11})^2 + 4 P_{01} P_{10})) / 2,
     normalized so v_0 + v_1 = 1. Since (1, 1)^T >= v entrywise and P^t >= 0,
       |R_{tk}| = (1, 1) P^t (1, 1)^T >= (1, 1) P^t v = rho(P)^t (v_0 + v_1) = rho(P)^t
     for every t >= 1 (with constant c = 1). Taking (L*t + 2)-th roots and sending
     t -> inf (or taking tensor powers via [DEGKM1997] Lemma 3.1) yields
       mu_3 >= rho(P)^{1/L}.
     Note: FORMAT.md requires all four N_{ab} >= 1 in every block to guarantee T_i > 0;
     mathematically Lemma 4.4 and |R_{tk}| >= rho(P)^t hold for any non-negative P with
     rho(P) > 0, and this verifier enforces N_{ab} >= 1 as specified by sunflower3 v1.
"""

import argparse
from collections import defaultdict
import decimal
from fractions import Fraction
import math
import re
import sys
from typing import Any

try:
    import numpy as np

    HAS_NUMPY = True
except ImportError:  # pragma: no cover
    np = None  # type: ignore[assignment]
    HAS_NUMPY = False

try:
    from mpmath import iv as mp_iv

    HAS_MPMATH = True
except ImportError:  # pragma: no cover
    mp_iv = None  # type: ignore[assignment]
    HAS_MPMATH = False

try:
    import numba

    HAS_NUMBA = True
except ImportError:  # pragma: no cover
    numba = None  # type: ignore[assignment]
    HAS_NUMBA = False

MAX_N = 64
MAX_BLOCKS = 1000
MAX_M = 1_000_000
MAX_M_NUMPY = 100_000
MAX_M_PURE_PYTHON = 10_000
NUMBA_AUTO_MIN_M = 20_000
NUMBA_MAX_N = 32
NUMBA_CROSSCHECK_MAX_M = 5_000
DEFAULT_THREADS = 6
PURE_PYTHON_CROSSCHECK_MAX_M = 200
BRUTE_FORCE_CROSSCHECK_MAX_M = 150
INTERVAL_DPS = 100
OUTPUT_DIGITS = 25
MAX_STR_DIGITS = 2000

_UNSIGNED_INT_RE = re.compile(r"\A(?:0|[1-9][0-9]*)\Z")
_BEAT_RE = re.compile(r"\A(?:0|[1-9][0-9]*)(?:\.[0-9]+|/[1-9][0-9]*)?\Z")


class _VerifierArgumentParser(argparse.ArgumentParser):
    def error(self, message: str):
        print(f"INVALID: {message}")
        raise SystemExit(1)


def _mpf_tuple_to_fraction(t: tuple[int, int, int, int]) -> Fraction:
    """Convert an internal mpmath (sign, man, exp, bc) tuple to an exact Fraction."""
    sign, man, exp, _bc = t
    if man == 0:
        return Fraction(0, 1)
    signed_man = -int(man) if sign else int(man)
    if exp >= 0:
        return Fraction(signed_man << int(exp), 1)
    return Fraction(signed_man, 1 << (-int(exp)))


def multiply_2x2(
    a: tuple[tuple[int, int], tuple[int, int]],
    b: tuple[tuple[int, int], tuple[int, int]],
) -> tuple[tuple[int, int], tuple[int, int]]:
    """Multiply two 2x2 matrices of exact Python integers."""
    (a00, a01), (a10, a11) = a
    (b00, b01), (b10, b11) = b
    return (
        (a00 * b00 + a01 * b10, a00 * b01 + a01 * b11),
        (a10 * b00 + a11 * b10, a10 * b01 + a11 * b11),
    )


def _format_surd_canonical(tr: int, disc: int) -> dict[str, Any]:
    """Build exact quadratic surd representations for rho = (tr + sqrt(disc)) / 2."""
    if tr < 0 or disc < 0:
        raise ValueError(f"Expected non-negative tr and disc, got tr={tr}, disc={disc}")

    root_disc = math.isqrt(disc)
    is_square = root_disc * root_disc == disc

    if tr % 2 == 0:
        # Since disc == tr^2 (mod 4), disc is divisible by 4 whenever tr is even.
        half_tr = tr // 2
        quarter_disc = disc // 4
        if is_square:
            exact_val = half_tr + (root_disc // 2)
            surd_str = str(exact_val)
        else:
            surd_str = f"{half_tr}+sqrt({quarter_disc})"
    else:
        half_tr = None
        quarter_disc = None
        if is_square:
            num = tr + root_disc
            if num % 2 == 0:
                surd_str = str(num // 2)
            else:
                surd_str = f"{num}/2"
        else:
            surd_str = f"({tr}+sqrt({disc}))/2"

    return {
        "tr": tr,
        "disc": disc,
        "denom": 2,
        "half_tr": half_tr,
        "quarter_disc": quarter_disc,
        "is_rational": is_square,
        "str": surd_str,
    }


def _binom_expand_surd_power(tr: int, disc: int, exp: int) -> tuple[int, int]:
    """Compute (tr + sqrt(disc))^exp = A + B * sqrt(disc) in exact integers via binary exponentiation."""
    if exp < 0:
        raise ValueError(f"Expected non-negative exponent, got {exp}")
    res_a, res_b = 1, 0
    base_a, base_b = int(tr), 1
    e = int(exp)
    while e > 0:
        if e & 1:
            res_a, res_b = (
                res_a * base_a + disc * res_b * base_b,
                res_a * base_b + res_b * base_a,
            )
        e >>= 1
        if e > 0:
            base_a, base_b = (
                base_a * base_a + disc * base_b * base_b,
                2 * base_a * base_b,
            )
    return res_a, res_b


def _compare_int_plus_sqrt(a1: int, c1: int, a2: int, c2: int) -> int:
    """Compare A1 + sqrt(C1) vs A2 + sqrt(C2) for integers A1, A2 and C1, C2 >= 0.

    Returns -1 if A1 + sqrt(C1) < A2 + sqrt(C2), 0 if equal, +1 if greater.
    Uses pure exact integer arithmetic (squaring twice).
    """
    if c1 < 0 or c2 < 0:
        raise ValueError("Radicands c1, c2 must be non-negative")
    d = a1 - a2
    if d < 0:
        return -_compare_int_plus_sqrt(a2, c2, a1, c1)

    # Now d = a1 - a2 >= 0, comparing d + sqrt(c1) >= 0 against sqrt(c2) >= 0.
    # Square once: (d + sqrt(c1))^2 - c2 = 2*d*sqrt(c1) - (c2 - d^2 - c1).
    r = c2 - d * d - c1
    if r < 0:
        return 1
    # Both 2*d*sqrt(c1) >= 0 and r >= 0; square again:
    lhs = 4 * d * d * c1
    rhs = r * r
    if lhs > rhs:
        return 1
    if lhs < rhs:
        return -1
    return 0


def compare_surd_rates(
    tr1: int, disc1: int, l1: int, tr2: int, disc2: int, l2: int
) -> int:
    """Compare rho_1^{1/l1} vs rho_2^{1/l2} in exact integer arithmetic, where
    rho_i = (tr_i + sqrt(disc_i)) / 2.

    Returns -1 if rho_1^{1/l1} < rho_2^{1/l2}, 0 if equal, +1 if greater.
    """
    if l1 < 1 or l2 < 1:
        raise ValueError(f"Expected positive period lengths, got l1={l1}, l2={l2}")
    g = math.gcd(l1, l2)
    e2 = l2 // g
    e1 = l1 // g

    # Compare 2^{e1} * rho_1^{e2} = 2^{e1 - e2} (tr1 + sqrt(disc1))^{e2}
    # against 2^{e1} * rho_2^{e1} = (tr2 + sqrt(disc2))^{e1}.
    a1, b1 = _binom_expand_surd_power(tr1, disc1, e2)
    a2, b2 = _binom_expand_surd_power(tr2, disc2, e1)
    if e1 > e2:
        shift = e1 - e2
        a1 <<= shift
        b1 <<= shift
    elif e2 > e1:
        shift = e2 - e1
        a2 <<= shift
        b2 <<= shift

    c1 = b1 * b1 * disc1
    c2 = b2 * b2 * disc2
    return _compare_int_plus_sqrt(a1, c1, a2, c2)


def _compare_rho_with_fraction(tr: int, disc: int, frac: Fraction) -> int:
    """Compare rho = (tr + sqrt(disc)) / 2 against a non-negative Fraction p/q in Z.

    Returns -1 if rho < p/q, 0 if rho == p/q, +1 if rho > p/q.
    """
    p = frac.numerator
    q = frac.denominator
    if p <= 0:
        return 1 if (tr > 0 or disc > 0) else 0
    # Compare q * (tr + sqrt(disc)) vs 2 * p  <=>  q * sqrt(disc) vs 2*p - q*tr.
    rhs = 2 * p - q * tr
    if rhs < 0:
        return 1
    lhs_sq = q * q * disc
    rhs_sq = rhs * rhs
    if lhs_sq > rhs_sq:
        return 1
    if lhs_sq < rhs_sq:
        return -1
    return 0


def _compare_rate_with_fraction(
    tr: int, disc: int, total_l: int, frac: Fraction
) -> int:
    """Compare rho^{1/total_l} against a non-negative Fraction p/q in exact integers.

    Returns -1 if rho^{1/total_l} < p/q, 0 if equal, +1 if greater.
    """
    if frac <= 0:
        return 1 if (tr > 0 or disc > 0) else 0
    p_l = frac.numerator**total_l
    q_l = frac.denominator**total_l
    rhs = 2 * p_l - q_l * tr
    if rhs < 0:
        return 1
    lhs_sq = q_l * q_l * disc
    rhs_sq = rhs * rhs
    if lhs_sq > rhs_sq:
        return 1
    if lhs_sq < rhs_sq:
        return -1
    return 0


def _enclose_rho_and_rate_mpmath_iv(
    tr: int, disc: int, total_l: int, dps: int = INTERVAL_DPS
) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    """Enclose rho and rho^{1/L} using mpmath.iv at >=100 digits in two formulations."""
    old_dps = mp_iv.dps
    try:
        mp_iv.dps = max(int(dps), 100)
        mp_tr = mp_iv.mpf(tr)
        mp_disc = mp_iv.mpf(disc)
        mp_two = mp_iv.mpf(2)
        mp_l = mp_iv.mpf(total_l)

        # Formulation 1: (tr + sqrt(disc)) / 2 and interval power rho ** (1 / L).
        rho_iv_1 = (mp_tr + mp_iv.sqrt(mp_disc)) / mp_two
        if total_l == 1:
            rate_iv_1 = rho_iv_1
        else:
            rate_iv_1 = rho_iv_1 ** (mp_iv.mpf(1) / mp_l)

        # Formulation 2: separate half-terms and exp(log(rho) / L).
        if tr % 2 == 0:
            rho_iv_2 = mp_iv.mpf(tr // 2) + mp_iv.sqrt(mp_iv.mpf(disc // 4))
        else:
            rho_iv_2 = (mp_tr / mp_two) + (mp_iv.sqrt(mp_disc) / mp_two)
        if total_l == 1:
            rate_iv_2 = rho_iv_2
        else:
            rate_iv_2 = mp_iv.exp(mp_iv.log(rho_iv_2) / mp_l)

        rho1_lo = _mpf_tuple_to_fraction(rho_iv_1._mpi_[0])
        rho1_hi = _mpf_tuple_to_fraction(rho_iv_1._mpi_[1])
        rho2_lo = _mpf_tuple_to_fraction(rho_iv_2._mpi_[0])
        rho2_hi = _mpf_tuple_to_fraction(rho_iv_2._mpi_[1])

        rho_lo = max(rho1_lo, rho2_lo)
        rho_hi = min(rho1_hi, rho2_hi)
        if rho_lo > rho_hi:
            raise AssertionError("mpmath.iv spectral radius enclosures failed to overlap")

        r1_lo = _mpf_tuple_to_fraction(rate_iv_1._mpi_[0])
        r1_hi = _mpf_tuple_to_fraction(rate_iv_1._mpi_[1])
        r2_lo = _mpf_tuple_to_fraction(rate_iv_2._mpi_[0])
        r2_hi = _mpf_tuple_to_fraction(rate_iv_2._mpi_[1])

        rate_lo = max(r1_lo, r2_lo)
        rate_hi = min(r1_hi, r2_hi)
        if rate_lo > rate_hi:
            raise AssertionError("mpmath.iv bound enclosures failed to overlap")

        return (rho_lo, rho_hi), (rate_lo, rate_hi)
    finally:
        mp_iv.dps = old_dps


def _enclose_rho_and_rate_decimal_iv(
    tr: int, disc: int, total_l: int, dps: int = INTERVAL_DPS
) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    """Enclose rho via exact integer isqrt and rho^{1/L} via stdlib Decimal intervals."""
    prec = max(int(dps), 100) + 20
    scale = 10**prec
    scaled_radicand = disc * (scale * scale)
    sqrt_lo_int = math.isqrt(scaled_radicand)
    sqrt_hi_int = (
        sqrt_lo_int
        if sqrt_lo_int * sqrt_lo_int == scaled_radicand
        else sqrt_lo_int + 1
    )

    two_scale = 2 * scale
    rho_lo = Fraction(tr * scale + sqrt_lo_int, two_scale)
    rho_hi = Fraction(tr * scale + sqrt_hi_int, two_scale)

    if total_l == 1:
        return (rho_lo, rho_hi), (rho_lo, rho_hi)

    ctx_near = decimal.Context(prec=prec, rounding=decimal.ROUND_HALF_EVEN)
    ctx_lo = decimal.Context(prec=prec, rounding=decimal.ROUND_FLOOR)
    ctx_hi = decimal.Context(prec=prec, rounding=decimal.ROUND_CEILING)

    rho_dec_lo = ctx_lo.divide(
        decimal.Decimal(tr * scale + sqrt_lo_int), decimal.Decimal(two_scale)
    )
    rho_dec_hi = ctx_hi.divide(
        decimal.Decimal(tr * scale + sqrt_hi_int), decimal.Decimal(two_scale)
    )

    ln_lo_near = ctx_near.ln(rho_dec_lo)
    ulp_ln_lo = ln_lo_near.next_plus(context=ctx_near) - ln_lo_near
    ln_lo = ctx_lo.subtract(ln_lo_near, ctx_hi.multiply(ulp_ln_lo, decimal.Decimal(4)))

    ln_hi_near = ctx_near.ln(rho_dec_hi)
    ulp_ln_hi = ln_hi_near.next_plus(context=ctx_near) - ln_hi_near
    ln_hi = ctx_hi.add(ln_hi_near, ctx_hi.multiply(ulp_ln_hi, decimal.Decimal(4)))

    l_dec = decimal.Decimal(total_l)
    div_lo = ctx_lo.divide(ln_lo, l_dec)
    div_hi = ctx_hi.divide(ln_hi, l_dec)

    exp_lo_near = ctx_near.exp(div_lo)
    ulp_exp_lo = exp_lo_near.next_plus(context=ctx_near) - exp_lo_near
    rate_dec_lo = ctx_lo.subtract(
        exp_lo_near, ctx_hi.multiply(ulp_exp_lo, decimal.Decimal(4))
    )

    exp_hi_near = ctx_near.exp(div_hi)
    ulp_exp_hi = exp_hi_near.next_plus(context=ctx_near) - exp_hi_near
    rate_dec_hi = ctx_hi.add(
        exp_hi_near, ctx_hi.multiply(ulp_exp_hi, decimal.Decimal(4))
    )

    rate_lo = Fraction(rate_dec_lo)
    rate_hi = Fraction(rate_dec_hi)
    return (rho_lo, rho_hi), (rate_lo, rate_hi)


def enclose_rho_and_rate(
    tr: int, disc: int, total_l: int, dps: int = INTERVAL_DPS
) -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    """Compute rigorous rational enclosures ((rho_lo, rho_hi), (rate_lo, rate_hi))."""
    dec_rho, dec_rate = _enclose_rho_and_rate_decimal_iv(
        tr, disc, total_l, dps=dps
    )
    if not HAS_MPMATH:
        rho_lo, rho_hi = dec_rho
        rate_lo, rate_hi = dec_rate
    else:
        mp_rho, mp_rate = _enclose_rho_and_rate_mpmath_iv(
            tr, disc, total_l, dps=dps
        )
        if max(mp_rho[0], dec_rho[0]) > min(mp_rho[1], dec_rho[1]):
            raise AssertionError("mpmath.iv and Decimal rho enclosures disagree")
        if max(mp_rate[0], dec_rate[0]) > min(mp_rate[1], dec_rate[1]):
            raise AssertionError("mpmath.iv and Decimal bound enclosures disagree")
        rho_lo = max(mp_rho[0], dec_rho[0])
        rho_hi = min(mp_rho[1], dec_rho[1])
        rate_lo = max(mp_rate[0], dec_rate[0])
        rate_hi = min(mp_rate[1], dec_rate[1])

    # Certify the rho enclosure algebraically in Z.
    if _compare_rho_with_fraction(tr, disc, rho_lo) < 0:
        raise AssertionError("rho_lo exceeds exact algebraic rho")
    if _compare_rho_with_fraction(tr, disc, rho_hi) > 0:
        raise AssertionError("rho_hi is below exact algebraic rho")

    # Certify the rate enclosure algebraically in Z when bit size is tractable.
    if total_l <= 500:
        if _compare_rate_with_fraction(tr, disc, total_l, rate_lo) < 0:
            raise AssertionError("rate_lo exceeds exact algebraic rho^{1/L}")
        if _compare_rate_with_fraction(tr, disc, total_l, rate_hi) > 0:
            raise AssertionError("rate_hi is below exact algebraic rho^{1/L}")

    return (rho_lo, rho_hi), (rate_lo, rate_hi)


def format_interval_outward(
    lo: Fraction, hi: Fraction, digits: int = OUTPUT_DIGITS
) -> tuple[str, str, Fraction, Fraction]:
    """Format rational interval [lo, hi] (>= 0) with outward rounding to `digits` decimal places."""
    if lo < 0 or hi < lo:
        raise ValueError(f"Expected 0 <= lo <= hi, got [{lo}, {hi}]")
    scale = 10**digits
    scaled_lo = (lo.numerator * scale) // lo.denominator
    scaled_hi = (hi.numerator * scale + hi.denominator - 1) // hi.denominator

    lo_int, lo_frac_part = divmod(scaled_lo, scale)
    hi_int, hi_frac_part = divmod(scaled_hi, scale)
    lo_str = f"{lo_int}.{lo_frac_part:0{digits}d}"
    hi_str = f"{hi_int}.{hi_frac_part:0{digits}d}"
    lo_dec_frac = Fraction(scaled_lo, scale)
    hi_dec_frac = Fraction(scaled_hi, scale)
    return lo_str, hi_str, lo_dec_frac, hi_dec_frac


def _parse_beat_threshold(beat: str | Fraction) -> tuple[Fraction, str]:
    """Parse a --beat or --claim threshold into an exact Fraction and canonical string."""
    if isinstance(beat, Fraction):
        if beat < 0:
            raise ValueError("threshold must be non-negative")
        return beat, str(beat)
    if not isinstance(beat, str):
        raise ValueError("threshold must be a string or Fraction")
    if not beat or beat != beat.strip() or any(c.isspace() for c in beat):
        raise ValueError("whitespace junk in threshold value")
    if len(beat) > MAX_STR_DIGITS:
        raise ValueError("threshold value exceeds digit limit")
    if not _BEAT_RE.match(beat):
        raise ValueError(
            "expected canonical unsigned decimal or rational 'p/q'"
        )
    return Fraction(beat), beat


def check_sperner_bitset(masks: list[int], n: int) -> tuple[int, int] | None:
    """Check whether any member is a subset of another using m-bit Python integer bitsets.

    Assumes all members in `masks` are distinct subsets of {0, ..., n-1}.
    Returns (i, j) with masks[i] subsetneq masks[j] if a containment exists, else None.
    """
    m = len(masks)
    if m <= 1:
        return None
    all_ones = (1 << m) - 1
    elem_bits = [0] * n
    for idx, mk in enumerate(masks):
        bit = 1 << idx
        x = mk
        while x:
            lsb = x & -x
            elem_bits[lsb.bit_length() - 1] |= bit
            x ^= lsb

    for idx, mk in enumerate(masks):
        sup = all_ones
        x = mk
        while x:
            lsb = x & -x
            sup &= elem_bits[lsb.bit_length() - 1]
            x ^= lsb
        other = sup ^ (1 << idx)
        if other:
            j = (other & -other).bit_length() - 1
            return (idx, j)
    return None


def check_sperner_brute_force(masks: list[int]) -> tuple[int, int] | None:
    """Direct O(m^2) pairwise Sperner check. Returns (i, j) with masks[i] subsetneq masks[j], or None."""
    m = len(masks)
    for i in range(m):
        mi = masks[i]
        for j in range(i + 1, m):
            mj = masks[j]
            inter = mi & mj
            if inter == mi:
                return (i, j)
            if inter == mj:
                return (j, i)
    return None


def check_sunflower3_numpy(masks: list[int]) -> tuple[int, int, int] | None:
    """Check 3-sunflower-freeness via numpy sorted intersection buckets.

    For each member S_i (ordered by descending popcount), computes inter = S_j & S_i
    for all j > i and sorts by `inter`. Equal intersections form contiguous runs in
    the sorted array `s_inter`, so two members at sorted offset d >= 1 belong to the
    same intersection bucket iff `s_inter[:-d] == s_inter[d:]`, and form a 3-sunflower
    with S_i iff their outside parts `s_rem = S_j ^ inter` are disjoint.
    Returns original indices (i, j, k) (sorted) of a 3-sunflower if one exists, else None.
    """
    if not HAS_NUMPY:
        raise RuntimeError("numpy is not available")
    m = len(masks)
    if m < 3:
        return None

    indexed = sorted(enumerate(masks), key=lambda pair: (-pair[1].bit_count(), pair[0]))
    orig_indices = np.array([idx for idx, _ in indexed], dtype=np.int64)
    arr = np.array([mk for _, mk in indexed], dtype=np.uint64)

    for i in range(m - 2):
        si = arr[i]
        sub = arr[i + 1 :]
        inter = sub & si
        order = np.argsort(inter, kind="quicksort")
        s_inter = inter[order]
        s_rem = sub[order] ^ s_inter
        n_sub = len(s_inter)
        d = 1
        while d < n_sub:
            same = s_inter[:-d] == s_inter[d:]
            if not np.any(same):
                break
            hit = same & ((s_rem[:-d] & s_rem[d:]) == 0)
            if np.any(hit):
                p = int(np.flatnonzero(hit)[0])
                u = int(orig_indices[i])
                v = int(orig_indices[i + 1 + int(order[p])])
                w = int(orig_indices[i + 1 + int(order[p + d])])
                a, b, c = sorted((u, v, w))
                return (a, b, c)
            d += 1
    return None


if HAS_NUMBA:

    @numba.njit(parallel=True, cache=False)
    def _sunflower3_numba_kernel(arr, nchunks):  # pragma: no cover - compiled
        """Per-chunk first 3-sunflower (i, B, C) found, or -1 rows.

        Chunk c handles i = c, c + nchunks, ... For S = arr[i] each later member B is
        packed as key = ((B & S) << 32) | (B & ~S) (requires n <= 32). After sorting,
        equal high halves form the buckets {B : B & S = K}, and two members B, C of a
        bucket form a 3-sunflower with S iff their low halves (parts outside S) are
        disjoint. Every triple is found when its smallest index is processed.
        """
        m = arr.shape[0]
        out = np.full((nchunks, 3), -1, dtype=np.int64)
        stop = np.zeros(1, dtype=np.int64)
        sh = np.uint64(32)
        lo_mask = np.uint64(0xFFFFFFFF)
        zero = np.uint64(0)
        for c in numba.prange(nchunks):
            keys = np.empty(m, dtype=np.uint64)
            rems = np.empty(m, dtype=np.uint64)
            n_steps = (m - 2 - c + nchunks - 1) // nchunks if c < m - 2 else 0
            for step in range(n_steps):
                i = c + step * nchunks
                if stop[0] != 0:
                    break
                s_i = arr[i]
                not_s = ~s_i
                cnt = 0
                for t in range(i + 1, m):
                    b = arr[t]
                    keys[cnt] = ((b & s_i) << sh) | (b & not_s)
                    cnt += 1
                ks = keys[:cnt]
                ks.sort()
                for t in range(cnt):
                    rems[t] = ks[t] & lo_mask
                g0 = 0
                found = False
                while g0 < cnt and not found:
                    hi = ks[g0] >> sh
                    g1 = g0 + 1
                    while g1 < cnt and (ks[g1] >> sh) == hi:
                        g1 += 1
                    for a in range(g0, g1 - 1):
                        ra = rems[a]
                        for b2 in range(a + 1, g1):
                            if (ra & rems[b2]) == zero:
                                out[c, 0] = i
                                out[c, 1] = np.int64(hi | rems[a])
                                out[c, 2] = np.int64(hi | rems[b2])
                                found = True
                                break
                        if found:
                            break
                    g0 = g1
                if found:
                    stop[0] = 1
                    break
        return out


def check_sunflower3_numba(
    masks: list[int], n: int, threads: int = DEFAULT_THREADS
) -> tuple[int, int, int] | None:
    """Exact parallel 3-sunflower check (numba) for n <= 32 and large m.

    Returns original indices (i, j, k) (sorted) of a 3-sunflower if one exists, else None.
    """
    if not HAS_NUMBA or not HAS_NUMPY:
        raise RuntimeError("numba/numpy is not available")
    if n > NUMBA_MAX_N:
        raise ValueError(f"numba backend requires n <= {NUMBA_MAX_N}, got n={n}")
    m = len(masks)
    if m < 3:
        return None
    numba.set_num_threads(max(1, min(int(threads), numba.config.NUMBA_NUM_THREADS)))
    arr = np.array(masks, dtype=np.uint64)
    nchunks = max(1, min(m, 256 * numba.get_num_threads()))
    out = _sunflower3_numba_kernel(arr, nchunks)
    hits = [tuple(int(x) for x in row) for row in out if int(row[0]) >= 0]
    if not hits:
        return None
    index_of = {mk: idx for idx, mk in enumerate(masks)}
    i, b_mask, c_mask = min(hits)
    j, k = index_of[b_mask], index_of[c_mask]
    a, b, c = sorted((i, j, k))
    return (a, b, c)


def check_sunflower3_pure_python(masks: list[int]) -> tuple[int, int, int] | None:
    """Check 3-sunflower-freeness in pure Python by grouping pairs (S_i, S_j) by S_i & S_j.

    Returns original indices (i, j, k) (sorted) of a 3-sunflower if one exists, else None.
    """
    m = len(masks)
    if m < 3:
        return None

    indexed = sorted(enumerate(masks), key=lambda pair: (-pair[1].bit_count(), pair[0]))
    ordered_masks = [mk for _, mk in indexed]
    orig_indices = [idx for idx, _ in indexed]

    for i in range(m - 2):
        si = ordered_masks[i]
        buckets: dict[int, list[tuple[int, int]]] = {}
        for j in range(i + 1, m):
            sj = ordered_masks[j]
            inter = si & sj
            rem = sj ^ inter
            b = buckets.get(inter)
            if b is None:
                buckets[inter] = [(rem, j)]
            else:
                for prev_rem, prev_j in b:
                    if not (prev_rem & rem):
                        u = orig_indices[i]
                        v = orig_indices[prev_j]
                        w = orig_indices[j]
                        a, b_idx, c = sorted((u, v, w))
                        return (a, b_idx, c)
                b.append((rem, j))
    return None


def check_sunflower3_brute_force(masks: list[int]) -> tuple[int, int, int] | None:
    """Direct textbook O(m^3) check over all triples (i, j, k) with 0 <= i < j < k < m."""
    m = len(masks)
    for i in range(m - 2):
        mi = masks[i]
        for j in range(i + 1, m - 1):
            mj = masks[j]
            ij = mi & mj
            for k in range(j + 1, m):
                mk = masks[k]
                if (mi & mk) == ij and (mj & mk) == ij:
                    return (i, j, k)
    return None


def compute_port_counts(
    masks: list[int], p: int, q: int
) -> dict[tuple[int, int], int]:
    """Compute exact port counts N_ab = #{D in B : [p in D] = a, [q in D] = b}."""
    counts = {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 0}
    for mk in masks:
        a = (mk >> p) & 1
        b = (mk >> q) & 1
        counts[(a, b)] += 1
    return counts


def _format_member_set(mask: int, n: int) -> str:
    if mask == 0:
        return "-"
    return "{" + ",".join(str(i) for i in range(n) if (mask >> i) & 1) + "}"


def rate_beats_threshold(
    tr: int, disc: int, total_l: int, rate_lo: Fraction, lo_dec: Fraction, beat_frac: Fraction
) -> bool:
    """True iff the certified rate exceeds beat_frac: exact surd comparison and both lower ends."""
    exact_beats = _compare_rate_with_fraction(tr, disc, total_l, beat_frac) > 0
    return (lo_dec > beat_frac) and (rate_lo > beat_frac) and exact_beats


def verify_sunflower3_lines(
    lines: list[str],
    beat: str | Fraction | None = None,
    claimed_lower_bound: str | Fraction | None = None,
    max_n: int = MAX_N,
    use_numpy: bool | None = None,
    dps: int = INTERVAL_DPS,
    use_numba: bool | None = None,
    threads: int = DEFAULT_THREADS,
) -> tuple[bool, dict[str, Any] | None, str]:
    """Parse and verify a sunflower3 v1 certificate from lines, returning (ok, details, msg)."""
    if not lines:
        return False, None, "INVALID: empty certificate"

    if use_numpy is None:
        use_numpy_flag = HAS_NUMPY
    else:
        use_numpy_flag = bool(use_numpy)
        if use_numpy_flag and not HAS_NUMPY:
            return False, None, "INVALID: numpy requested but not available"
    if use_numba and not (HAS_NUMBA and HAS_NUMPY):
        return False, None, "INVALID: numba requested but not available"

    # Filter out '#' comment lines while preserving 1-based line numbers.
    non_comment: list[tuple[int, str]] = []
    for line_no, line in enumerate(lines, start=1):
        if "\ufeff" in line:
            return False, None, f"INVALID: line {line_no}: UTF-8 BOM is not allowed"
        if "\r" in line:
            return (
                False,
                None,
                f"INVALID: line {line_no}: carriage return whitespace junk in line",
            )
        if not line.isascii():
            return (
                False,
                None,
                f"INVALID: line {line_no}: non-ASCII character in certificate",
            )
        if "\x00" in line:
            return (
                False,
                None,
                f"INVALID: line {line_no}: NUL byte in certificate",
            )
        if line.startswith("#"):
            continue
        if not line:
            return (
                False,
                None,
                f"INVALID: line {line_no}: blank line is not allowed",
            )
        if (
            line != line.strip()
            or any(c.isspace() and c != " " for c in line)
            or "  " in line
        ):
            return (
                False,
                None,
                f"INVALID: line {line_no}: whitespace junk in line {line!r}",
            )
        non_comment.append((line_no, line))

    if not non_comment:
        return False, None, "INVALID: no non-comment lines in certificate"

    hdr_line_no, hdr_line = non_comment[0]
    if hdr_line != "sunflower3 v1":
        return (
            False,
            None,
            f"INVALID: line {hdr_line_no}: expected header 'sunflower3 v1', got {hdr_line!r}",
        )

    idx = 1
    total_non_comment = len(non_comment)
    blocks_raw: list[tuple[int, int, int, int, int, list[tuple[int, int]]]] = []
    file_claim_str: str | None = None

    while idx < total_non_comment:
        line_no, line = non_comment[idx]
        tokens = line.split(" ")

        # Support optional top-level `claim <value>` line for claimed lower bound checks.
        if tokens[0] == "claim":
            if len(tokens) != 2:
                return (
                    False,
                    None,
                    f"INVALID: line {line_no}: expected 'claim <bound>', got {line!r}",
                )
            if file_claim_str is not None:
                return (
                    False,
                    None,
                    f"INVALID: line {line_no}: duplicate 'claim' directive",
                )
            file_claim_str = tokens[1]
            idx += 1
            continue

        if tokens[0] != "block":
            return (
                False,
                None,
                f"INVALID: line {line_no}: expected 'block <n> <p> <q> <m>', got {line!r}",
            )
        if len(tokens) != 5:
            return (
                False,
                None,
                f"INVALID: line {line_no}: expected 5 tokens in 'block <n> <p> <q> <m>', got {len(tokens)}",
            )

        for tok_name, tok_val in zip(("n", "p", "q", "m"), tokens[1:]):
            if not _UNSIGNED_INT_RE.match(tok_val) or len(tok_val) > 10:
                return (
                    False,
                    None,
                    f"INVALID: line {line_no}: invalid canonical integer for {tok_name}: {tok_val!r}",
                )

        n = int(tokens[1])
        p = int(tokens[2])
        q = int(tokens[3])
        m = int(tokens[4])

        if n < 3 or n > 64:
            return (
                False,
                None,
                f"INVALID: line {line_no}: require 3 <= n <= 64, got n={n}",
            )
        if n > max_n:
            return (
                False,
                None,
                f"INVALID: line {line_no}: n = {n} exceeds limit ({max_n}); too large for this verifier",
            )
        if p < 0 or p >= n:
            return (
                False,
                None,
                f"INVALID: line {line_no}: in-port p={p} out of range [0, {n - 1}]",
            )
        if q < 0 or q >= n:
            return (
                False,
                None,
                f"INVALID: line {line_no}: out-port q={q} out of range [0, {n - 1}]",
            )
        if p == q:
            return (
                False,
                None,
                f"INVALID: line {line_no}: ports must be distinct, got p=q={p}",
            )
        if m < 1:
            return (
                False,
                None,
                f"INVALID: line {line_no}: require m >= 1, got m={m}",
            )
        if m > MAX_M:
            return (
                False,
                None,
                f"INVALID: line {line_no}: m = {m} exceeds limit ({MAX_M})",
            )
        numba_ok = HAS_NUMBA and HAS_NUMPY and n <= NUMBA_MAX_N and use_numba is not False
        if m > MAX_M_NUMPY and not numba_ok:
            return (
                False,
                None,
                f"INVALID: line {line_no}: m = {m} exceeds limit ({MAX_M_NUMPY}) "
                f"without the numba backend (needs numba and n <= {NUMBA_MAX_N})",
            )
        if use_numba and n > NUMBA_MAX_N:
            return (
                False,
                None,
                f"INVALID: line {line_no}: numba backend requires n <= {NUMBA_MAX_N}, got n={n}",
            )
        if not use_numpy_flag and not use_numba and m > MAX_M_PURE_PYTHON:
            return (
                False,
                None,
                f"INVALID: line {line_no}: m = {m} exceeds pure-Python limit ({MAX_M_PURE_PYTHON})",
            )

        idx += 1
        if idx + m > total_non_comment:
            avail = total_non_comment - idx
            return (
                False,
                None,
                f"INVALID: line {line_no}: block claims m={m} members, but only {avail} lines remain",
            )

        member_entries: list[tuple[int, int]] = []
        for _ in range(m):
            m_line_no, m_line = non_comment[idx]
            idx += 1
            if m_line == "-":
                member_entries.append((m_line_no, 0))
                continue
            m_tokens = m_line.split(" ")
            mask = 0
            prev_pt = -1
            for pt_tok in m_tokens:
                if not _UNSIGNED_INT_RE.match(pt_tok) or len(pt_tok) > 10:
                    return (
                        False,
                        None,
                        f"INVALID: line {m_line_no}: expected canonical point integer, got {pt_tok!r}",
                    )
                pt = int(pt_tok)
                if pt < 0 or pt >= n:
                    return (
                        False,
                        None,
                        f"INVALID: line {m_line_no}: point {pt} out of range [0, {n - 1}]",
                    )
                if pt == prev_pt:
                    return (
                        False,
                        None,
                        f"INVALID: line {m_line_no}: duplicate point {pt} in member line",
                    )
                if pt < prev_pt:
                    return (
                        False,
                        None,
                        f"INVALID: line {m_line_no}: points not in strictly increasing order in {m_line!r}",
                    )
                prev_pt = pt
                mask |= 1 << pt
            member_entries.append((m_line_no, mask))

        blocks_raw.append((line_no, n, p, q, m, member_entries))
        if len(blocks_raw) > MAX_BLOCKS:
            return (
                False,
                None,
                f"INVALID: number of blocks exceeds limit ({MAX_BLOCKS})",
            )

    if not blocks_raw:
        return False, None, "INVALID: certificate must contain at least one block"

    # Parse optional claimed_lower_bound and beat thresholds.
    claimed_frac: Fraction | None = None
    claimed_str: str | None = None
    effective_claim = (
        claimed_lower_bound if claimed_lower_bound is not None else file_claim_str
    )
    if effective_claim is not None:
        try:
            claimed_frac, claimed_str = _parse_beat_threshold(effective_claim)
        except (ValueError, ZeroDivisionError) as exc:
            return (
                False,
                None,
                f"INVALID: invalid claimed bound {effective_claim!r}: {exc}",
            )
        if file_claim_str is not None and claimed_lower_bound is not None:
            try:
                file_c_frac, _ = _parse_beat_threshold(file_claim_str)
            except (ValueError, ZeroDivisionError) as exc:
                return (
                    False,
                    None,
                    f"INVALID: invalid file claim {file_claim_str!r}: {exc}",
                )
            if file_c_frac > claimed_frac:
                claimed_frac = file_c_frac
                claimed_str = file_claim_str

    beat_frac: Fraction | None = None
    beat_str: str | None = None
    if beat is not None:
        try:
            beat_frac, beat_str = _parse_beat_threshold(beat)
        except (ValueError, ZeroDivisionError) as exc:
            return False, None, f"INVALID: invalid --beat threshold {beat!r}: {exc}"

    # Verify each block exhaustively.
    block_details: list[dict[str, Any]] = []
    prod_mat: tuple[tuple[int, int], tuple[int, int]] = ((1, 0), (0, 1))
    total_l = 0

    for blk_idx, (blk_line_no, n, p, q, m, member_entries) in enumerate(
        blocks_raw, start=1
    ):
        # 1. Distinct members check.
        seen_masks: dict[int, tuple[int, int]] = {}
        masks: list[int] = []
        for mem_idx, (mem_line_no, mask) in enumerate(member_entries):
            if mask in seen_masks:
                prev_idx, prev_line = seen_masks[mask]
                return (
                    False,
                    None,
                    f"INVALID: block {blk_idx} (line {blk_line_no}): duplicate member "
                    f"{_format_member_set(mask, n)} at member {mem_idx} (line {mem_line_no}), "
                    f"already seen at member {prev_idx} (line {prev_line})",
                )
            seen_masks[mask] = (mem_idx, mem_line_no)
            masks.append(mask)

        # 2. Port counts N_ab >= 1 check.
        port_counts = compute_port_counts(masks, p, q)
        n00 = port_counts[(0, 0)]
        n01 = port_counts[(0, 1)]
        n10 = port_counts[(1, 0)]
        n11 = port_counts[(1, 1)]
        if n00 + n01 + n10 + n11 != m:
            raise AssertionError("Port counts do not sum to m")
        for (a_bit, b_bit), cnt in (
            ((0, 0), n00),
            ((0, 1), n01),
            ((1, 0), n10),
            ((1, 1), n11),
        ):
            if cnt < 1:
                return (
                    False,
                    None,
                    f"INVALID: block {blk_idx} (line {blk_line_no}): port count "
                    f"N_{a_bit}{b_bit} = {cnt} < 1 for ports p={p}, q={q} "
                    "(all four N_ab must be >= 1)",
                )

        # 3. Sperner check (bitset + brute-force cross-check on small m).
        sperner_viol = check_sperner_bitset(masks, n)
        if m <= PURE_PYTHON_CROSSCHECK_MAX_M:
            bf_sperner = check_sperner_brute_force(masks)
            if (sperner_viol is None) != (bf_sperner is None):
                raise AssertionError(
                    "Bitset and brute-force Sperner checks disagreed"
                )
        if sperner_viol is not None:
            sub_i, sup_j = sperner_viol
            if sub_i == sup_j or (masks[sub_i] & masks[sup_j]) != masks[sub_i]:
                raise AssertionError("Invalid Sperner witness indices")
            return (
                False,
                None,
                f"INVALID: block {blk_idx} (line {blk_line_no}): family is not Sperner "
                f"(member {sub_i} {_format_member_set(masks[sub_i], n)} is a proper subset "
                f"of member {sup_j} {_format_member_set(masks[sup_j], n)})",
            )

        # 4. 3-sunflower-free check (fast exact + brute-force cross-check on small m).
        block_numba = bool(use_numba) or (
            use_numba is None
            and m >= NUMBA_AUTO_MIN_M
            and HAS_NUMBA
            and HAS_NUMPY
            and n <= NUMBA_MAX_N
        )
        if block_numba:
            sf_viol = check_sunflower3_numba(masks, n, threads=threads)
            if m <= NUMBA_CROSSCHECK_MAX_M:
                sf_np = check_sunflower3_numpy(masks)
                if (sf_viol is None) != (sf_np is None):
                    raise AssertionError(
                        "numba and numpy 3-sunflower checks disagreed"
                    )
        elif use_numpy_flag:
            sf_viol = check_sunflower3_numpy(masks)
            if m <= PURE_PYTHON_CROSSCHECK_MAX_M:
                sf_py = check_sunflower3_pure_python(masks)
                if (sf_viol is None) != (sf_py is None):
                    raise AssertionError(
                        "numpy and pure-Python 3-sunflower checks disagreed"
                    )
        else:
            sf_viol = check_sunflower3_pure_python(masks)

        if m <= BRUTE_FORCE_CROSSCHECK_MAX_M:
            sf_bf = check_sunflower3_brute_force(masks)
            if (sf_viol is None) != (sf_bf is None):
                raise AssertionError(
                    "Fast and brute-force 3-sunflower checks disagreed"
                )

        if sf_viol is not None:
            i_sf, j_sf, k_sf = sf_viol
            mi, mj, mk = masks[i_sf], masks[j_sf], masks[k_sf]
            if (
                len({i_sf, j_sf, k_sf}) != 3
                or (mi & mj) != (mi & mk)
                or (mi & mj) != (mj & mk)
            ):
                raise AssertionError("Invalid 3-sunflower witness triple")
            core = mi & mj
            return (
                False,
                None,
                f"INVALID: block {blk_idx} (line {blk_line_no}): 3-sunflower found at "
                f"members ({i_sf}, {j_sf}, {k_sf}) with core {_format_member_set(core, n)}",
            )

        t_mat: tuple[tuple[int, int], tuple[int, int]] = (
            (n10, n11),
            (n00, n01),
        )
        prod_mat = multiply_2x2(prod_mat, t_mat)
        total_l += n - 2
        block_details.append(
            {
                "n": n,
                "p": p,
                "q": q,
                "m": m,
                "N_00": n00,
                "N_01": n01,
                "N_10": n10,
                "N_11": n11,
                "T": t_mat,
            }
        )

    (p00, p01), (p10, p11) = prod_mat
    tr = p00 + p11
    det = p00 * p11 - p01 * p10
    disc = (p00 - p11) * (p00 - p11) + 4 * p01 * p10
    surd_info = _format_surd_canonical(tr, disc)

    eff_dps = max(
        int(dps),
        (len(claimed_str) + 50) if claimed_str is not None else 0,
        (len(beat_str) + 50) if beat_str is not None else 0,
        100,
    )
    (rho_lo, rho_hi), (rate_lo, rate_hi) = enclose_rho_and_rate(
        tr, disc, total_l, dps=eff_dps
    )
    lo_str, hi_str, lo_dec_frac, hi_dec_frac = format_interval_outward(
        rate_lo, rate_hi, digits=OUTPUT_DIGITS
    )
    rho_lo_str, rho_hi_str, rho_lo_dec, rho_hi_dec = format_interval_outward(
        rho_lo, rho_hi, digits=OUTPUT_DIGITS
    )

    # Algebraically verify outward-rounded decimal bounds in Z when L <= 500.
    if total_l <= 500:
        if _compare_rate_with_fraction(tr, disc, total_l, lo_dec_frac) < 0:
            raise AssertionError("Outward-rounded lo_str exceeds exact rho^{1/L}")
        if _compare_rate_with_fraction(tr, disc, total_l, hi_dec_frac) > 0:
            raise AssertionError("Outward-rounded hi_str is below exact rho^{1/L}")

    if claimed_frac is not None:
        exact_claim_ok = _compare_rate_with_fraction(
            tr, disc, total_l, claimed_frac
        ) >= 0
        if rate_lo < claimed_frac or not exact_claim_ok:
            return (
                False,
                None,
                f"INVALID: certified lower bound {lo_str} is below claimed bound {claimed_str}",
            )

    beats = False
    if beat_frac is not None:
        beats = rate_beats_threshold(tr, disc, total_l, rate_lo, lo_dec_frac, beat_frac)

    surd_str = surd_info["str"]
    msg = (
        f"VALID [{lo_str}, {hi_str}] blocks={len(block_details)} L={total_l} "
        f"P=[[{p00},{p01}],[{p10},{p11}]] rho={surd_str} "
        f"rho_iv=[{rho_lo_str}, {rho_hi_str}]"
    )
    if beat_frac is not None and beats:
        msg += f" BEATS {beat_str}"

    details: dict[str, Any] = {
        "blocks": block_details,
        "num_blocks": len(block_details),
        "L": total_l,
        "P": prod_mat,
        "tr": tr,
        "det": det,
        "disc": disc,
        "surd": surd_info,
        "rho_lo": rho_lo,
        "rho_hi": rho_hi,
        "rho_lo_str": rho_lo_str,
        "rho_hi_str": rho_hi_str,
        "rho_lo_dec": rho_lo_dec,
        "rho_hi_dec": rho_hi_dec,
        "rate_lo": rate_lo,
        "rate_hi": rate_hi,
        "ratio_lo": rate_lo,
        "ratio_hi": rate_hi,
        "lo_str": lo_str,
        "hi_str": hi_str,
        "lo_dec": lo_dec_frac,
        "hi_dec": hi_dec_frac,
        "claimed_lower_bound": claimed_frac,
        "beats": beats,
        "beat_str": beat_str,
    }
    return True, details, msg


def verify_sunflower3_text(
    raw: str,
    beat: str | Fraction | None = None,
    claimed_lower_bound: str | Fraction | None = None,
    max_n: int = MAX_N,
    use_numpy: bool | None = None,
    dps: int = INTERVAL_DPS,
    use_numba: bool | None = None,
    threads: int = DEFAULT_THREADS,
) -> tuple[bool, dict[str, Any] | None, str]:
    """Parse a raw sunflower3 v1 certificate text string and verify it."""
    if not isinstance(raw, str) or not raw:
        return False, None, "INVALID: empty file"
    if "\ufeff" in raw:
        return False, None, "INVALID: UTF-8 BOM is not allowed"
    if "\r" in raw:
        return False, None, "INVALID: carriage return whitespace junk in file"
    if not raw.isascii():
        return False, None, "INVALID: non-ASCII character in file"

    # Allow at most one trailing newline at EOF; reject trailing blank lines.
    body = raw[:-1] if raw.endswith("\n") else raw
    if not body:
        return False, None, "INVALID: empty file"
    lines = body.split("\n")
    return verify_sunflower3_lines(
        lines,
        beat=beat,
        claimed_lower_bound=claimed_lower_bound,
        max_n=max_n,
        use_numpy=use_numpy,
        dps=dps,
        use_numba=use_numba,
        threads=threads,
    )


def verify_sunflower3_file(
    filepath: str,
    beat: str | Fraction | None = None,
    claimed_lower_bound: str | Fraction | None = None,
    max_n: int = MAX_N,
    use_numpy: bool | None = None,
    dps: int = INTERVAL_DPS,
    use_numba: bool | None = None,
    threads: int = DEFAULT_THREADS,
) -> tuple[bool, dict[str, Any] | None, str]:
    """Read a sunflower3 v1 certificate file and verify it."""
    try:
        with open(filepath, "r", encoding="utf-8", newline="") as f:
            raw = f.read()
    except (OSError, UnicodeDecodeError) as exc:
        return False, None, f"INVALID: cannot read file: {exc}"

    return verify_sunflower3_text(
        raw,
        beat=beat,
        claimed_lower_bound=claimed_lower_bound,
        max_n=max_n,
        use_numpy=use_numpy,
        dps=dps,
        use_numba=use_numba,
        threads=threads,
    )


def main(argv: list[str] | None = None) -> int:
    parser = _VerifierArgumentParser(
        description="Verify a 3-sunflower-free capacity (constant 49a) sunflower3 v1 certificate."
    )
    parser.add_argument("file", help="Path to the sunflower3 v1 certificate file")
    parser.add_argument(
        "--beat",
        type=str,
        action="append",
        default=None,
        help=(
            "Optional threshold V (e.g. 1.5666969); prints BEATS V only if lo > V exactly. "
            "May be repeated."
        ),
    )
    parser.add_argument(
        "--claim",
        type=str,
        default=None,
        help="Optional claimed lower bound C; rejects with INVALID if certified lo < C",
    )
    parser.add_argument(
        "--threads",
        type=int,
        default=DEFAULT_THREADS,
        help=f"Threads for the numba 3-sunflower backend (default {DEFAULT_THREADS})",
    )
    parser.add_argument(
        "--backend",
        choices=("auto", "numba", "numpy"),
        default="auto",
        help=(
            "3-sunflower backend: numba (parallel, n <= 32), numpy, or auto "
            f"(numba for blocks with m >= {NUMBA_AUTO_MIN_M})"
        ),
    )
    args = parser.parse_args(argv)
    if args.threads < 1:
        parser.error("--threads must be >= 1")

    beats_args = args.beat or []
    extra_beats = []
    for extra in beats_args[1:]:
        try:
            extra_beats.append(_parse_beat_threshold(extra))
        except ValueError as exc:
            parser.error(f"invalid --beat threshold {extra!r}: {exc}")

    ok, details, message = verify_sunflower3_file(
        args.file,
        beat=beats_args[0] if beats_args else None,
        claimed_lower_bound=args.claim,
        use_numba={"auto": None, "numba": True, "numpy": False}[args.backend],
        threads=args.threads,
    )
    if ok and details is not None:
        for beat_frac, beat_str in extra_beats:
            if rate_beats_threshold(
                details["tr"],
                details["disc"],
                details["L"],
                details["rate_lo"],
                details["lo_dec"],
                beat_frac,
            ):
                message += f" BEATS {beat_str}"
    print(message)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

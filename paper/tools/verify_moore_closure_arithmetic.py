"""Verify the arithmetic used by the exact Moore closure for n >= 48."""

from fractions import Fraction
from typing import TypeVar


Number = TypeVar("Number", int, Fraction)
Polynomial = list[Number]


def poly_add(left: Polynomial, right: Polynomial) -> Polynomial:
    size = max(len(left), len(right))
    return [
        (left[i] if i < len(left) else 0)
        + (right[i] if i < len(right) else 0)
        for i in range(size)
    ]


def poly_scale(poly: Polynomial, scalar: Number) -> Polynomial:
    return [scalar * coefficient for coefficient in poly]


def poly_mul(left: Polynomial, right: Polynomial) -> Polynomial:
    product = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            product[i + j] += a * b
    return product


def poly_pow(poly: Polynomial, exponent: int) -> Polynomial:
    result: Polynomial = [1]
    for _ in range(exponent):
        result = poly_mul(result, poly)
    return result


def verify_displayed_polynomials() -> None:
    ell: Polynomial = [8, 1]
    c_ell: Polynomial = [1]
    for offset in range(4):
        c_ell = poly_mul(c_ell, [8 - offset, 1])

    corner_43 = poly_add(
        poly_scale(c_ell, 2 * 43**3),
        poly_scale(poly_pow(poly_add(poly_scale(ell, 10), [17]), 4), -3),
    )
    assert corner_43 == [
        1_555_677,
        59_988_164,
        22_976_314,
        2_970_364,
        129_014,
    ]

    corner_44 = poly_add(
        poly_scale(c_ell, 1_250 * 44**3),
        poly_scale(poly_pow(poly_add(poly_scale(ell, 50), [91]), 4), -3),
    )
    assert corner_44 == [
        4_526_254_317,
        42_485_217_400,
        15_877_835_000,
        2_031_980_000,
        87_730_000,
    ]

    ratio_difference = poly_add(
        poly_pow([Fraction(1), Fraction(1)], 3),
        poly_scale(
            poly_pow([Fraction(1), Fraction(3, 5)], 4),
            Fraction(-1),
        ),
    )
    assert ratio_difference == [
        Fraction(0),
        Fraction(375, 625),
        Fraction(525, 625),
        Fraction(85, 625),
        Fraction(-81, 625),
    ]


def phi(ell: int, t: int, x: int) -> int:
    return (
        30 * ell * t * x**2
        + 150 * ell * (ell - 1) * t**2 * x
        + 500 * ell * (ell - 1) * (ell - 2) * t**3
        - 3 * (t - 10) * x**3
    )


def verify_small_exponents() -> int:
    checked = 0

    for t in range(43, 80):
        u = t - 43
        a_bound = 159 + 3 * t
        expanded = (
            u**3 * (773_272 - 81 * u**2 - 5_297 * u)
            + 83_801_688 * u**2
            + 2_621_645_152 * u
            + 31_854_951_952
        )
        assert (a_bound + 10 * t) ** 4 - (t - 9) * a_bound**4 == expanded
        assert expanded >= 0

    for ell in range(5, 8):
        a = ell - 5
        for t in range(43, 108):
            b = t - 43
            upper = 50 * ell + 3 * t - 41
            if 5 * t > upper:
                continue

            left_endpoint = 125 * t**3 * (
                4 * a**3 + 54 * a**2 + 248 * a + 54 + 3 * (79 - b)
            )
            assert phi(ell, t, 5 * t) == left_endpoint
            assert left_endpoint >= 0

            q3 = 500 * b**3 + 72_000 * b**2 + 3_118_500 * b + 44_471_000
            q2 = (
                6_450 * b**3
                + 872_400 * b**2
                + 36_222_750 * b
                + 504_355_800
            )
            q1 = (
                23_770 * b**3
                + 3_057_300 * b**2
                + 121_507_590 * b
                + 1_658_324_560
            )
            upper_endpoint = (
                a**3 * q3
                + a**2 * q2
                + a * q1
                + b**3 * (10_299 - 81 * b)
                + 2_032_188 * b**2
                + 82_837_380 * b
                + 1_174_137_072
            )
            assert phi(ell, t, upper) == upper_endpoint
            assert upper_endpoint >= 0
            second_derivative_bound = 60 * ell * t - 18 * (t - 10) * (5 * t)
            assert second_derivative_bound <= t * (1_320 - 90 * t) < 0

            for v in range(t, 108):
                if 5 * v > upper:
                    continue
                checked += 1
                assert 3 * (t - 10) * v**3 <= (
                    6 * ell * t * v**2
                    + 6 * ell * (ell - 1) * t**2 * v
                    + 4 * ell * (ell - 1) * (ell - 2) * t**3
                )
                assert (t - 9) * v**ell <= (v + 2 * t) ** ell

    return checked


def verify_fourth_term_region() -> int:
    checked = 0
    for ell in range(8, 201):
        c_ell = ell * (ell - 1) * (ell - 2) * (ell - 3)
        for t in range(43, (50 * ell - 41) // 2 + 1):
            upper_v = (50 * ell + 3 * t - 41) // 5
            if upper_v < t:
                continue
            checked += 1
            assert 3 * upper_v**4 <= 2 * c_ell * t**3
            assert (t + 1) * upper_v**ell <= (upper_v + 2 * t) ** ell
    return checked


def verify_census_region() -> tuple[int, int, int]:
    checked = 0
    small = 0
    large = 0

    # This finite sweep is a regression check.  The unbounded step is the
    # polynomial and ratio argument checked separately above and proved in Lean.
    # It intentionally assumes only the master census inequality.
    for n in range(48, 257):
        for excess in range((4 * n - 186) // 10 + 1):
            for heavy in range(excess + 1):
                if 10 * excess + 7 * heavy + 186 > 4 * n:
                    continue

                checked += 1
                t = n - 4 - excess - 3 * heavy
                v = n - heavy
                length = (2 * n - excess) // 12
                ell = length // 2
                remainder = 2 * n - excess - 24 * ell

                assert ell == (2 * n - excess) // 24
                assert 0 <= remainder <= 23
                assert 43 <= t <= v
                assert ell >= 4
                assert length >= 8
                assert 5 * v + 41 <= 50 * ell + 3 * t
                assert 12 * length + excess <= 2 * n

                if ell <= 7:
                    small += 1
                    assert n <= 107
                    assert v <= 107
                    assert (t - 9) * v**ell <= (v + 2 * t) ** ell
                else:
                    large += 1
                    c_ell = ell * (ell - 1) * (ell - 2) * (ell - 3)
                    assert 3 * v**4 <= 2 * c_ell * t**3

                assert (
                    t * (v - 1) * v**ell
                    < (v + t) * ((v + 2 * t) ** ell - v**ell)
                )

    assert small > 0 and large > 0
    return checked, small, large


def main() -> None:
    verify_displayed_polynomials()
    small_profiles = verify_small_exponents()
    fourth_profiles = verify_fourth_term_region()
    census_profiles, small_census, large_census = verify_census_region()

    print("displayed_polynomials=verified")
    print(f"small_exponent_profiles={small_profiles}")
    print(f"fourth_term_profiles={fourth_profiles}")
    print(
        "census_profiles="
        f"{census_profiles} (small={small_census}, large={large_census})"
    )


if __name__ == "__main__":
    main()

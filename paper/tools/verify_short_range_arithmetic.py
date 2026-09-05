"""Verify the endpoint profiles and owner-slot arithmetic below order 50."""


def endpoint_profiles(n: int) -> list[tuple[int, ...]]:
    profiles: list[tuple[int, ...]] = []
    for moat in range(7):
        bulk = n - 3 - moat
        if bulk < 1 or 2 * n > 5 * moat:
            continue
        for moat_excess in range(n - 8):
            bulk_excess = n - 9 - moat_excess
            if bulk_excess < 0:
                continue
            if moat_excess < max(2, moat - 2):
                continue
            for bulk_pairs in range(0, 2 * bulk_excess + 1, 2):
                boundary = 3 * bulk + bulk_excess - bulk_pairs
                moat_pairs = 3 * moat + moat_excess - 6 - boundary
                if boundary > 2 * bulk and moat_pairs >= 0 and moat_pairs % 2 == 0:
                    profiles.append(
                        (
                            moat,
                            bulk,
                            moat_excess,
                            bulk_excess,
                            bulk_pairs,
                            boundary,
                            moat_pairs,
                        )
                    )
    return sorted(profiles)


def verify_endpoint_profiles() -> None:
    expected = {
        10: [],
        11: [],
        12: [(5, 4, 3, 0, 0, 12, 0)],
        13: [(6, 4, 4, 0, 0, 12, 4)],
        14: [
            (6, 5, 4, 1, 0, 16, 0),
            (6, 5, 4, 1, 2, 14, 2),
            (6, 5, 5, 0, 0, 15, 2),
        ],
        15: [
            (6, 6, 4, 2, 4, 16, 0),
            (6, 6, 5, 1, 2, 17, 0),
            (6, 6, 6, 0, 0, 18, 0),
        ],
    }
    for n, profiles in expected.items():
        assert endpoint_profiles(n) == profiles


def verify_owner_slot() -> int:
    checked = 0
    for n in range(32, 50):
        for excess in range(n + 1):
            for heavy in range(excess + 1):
                for giant in range(n + 1):
                    if 3 * excess + 32 > n + 3 * giant:
                        continue
                    if giant * (n - 20) > 9 * excess:
                        continue

                    checked += 1
                    owner_min = max(0, 24 + 2 * excess - heavy - 3 * giant)
                    owner_max = (4 * n - 3 * excess - 32) // 7
                    assert owner_min > owner_max
    return checked


def main() -> None:
    verify_endpoint_profiles()
    owner_cells = verify_owner_slot()
    print("endpoint_profiles=verified")
    print(f"owner_parameter_cells={owner_cells}")
    print("owner_survivors=0")


if __name__ == "__main__":
    main()

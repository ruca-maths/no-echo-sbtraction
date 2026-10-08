#!/usr/bin/env python3
"""Exact strategy calculator for the bounded no-echo take-away game.

Rules
-----
There is one heap of ``n`` stones. A move takes 1 through ``m`` stones,
without exceeding the heap, and may not repeat the previous player's take.
The player with no legal move loses. Pass ``j=0`` for the opening position;
otherwise ``j`` is the number taken on the immediately preceding turn.

Examples
--------
    python no_echo_strategy.py 7 3
    python no_echo_strategy.py 20 5 2

The recurrence is exact. For a fixed ``m``, the compressed sequence of rows
has finitely many states, so a repeated window can be used to skip arbitrarily
large ``n``. The number of states can grow exponentially with ``m``; large
inputs are mathematically supported but may require substantial time or memory.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from typing import Optional, Tuple


@dataclass(frozen=True)
class Analysis:
    """Outcome and winning moves for the player whose turn it is."""

    n: int
    m: int
    previous_take: int
    winning_moves: Tuple[int, ...]

    @property
    def can_force_win(self) -> bool:
        return bool(self.winning_moves)

    @property
    def position_type(self) -> str:
        return "N" if self.can_force_win else "P"

    @property
    def best_move(self) -> Optional[int]:
        """Return the smallest winning take, or None if no winning move exists."""
        return self.winning_moves[0] if self.winning_moves else None


def _validate_integer(name: str, value: int) -> None:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError("{} must be an integer".format(name))


def _validate_heap_and_cap(n: int, m: int) -> None:
    _validate_integer("n", n)
    _validate_integer("m", m)
    if n < 0:
        raise ValueError("n must be nonnegative")
    if m < 1:
        raise ValueError("m must be at least 1")


def _moves_to_losing_row(index: int, row_codes: list[int], m: int) -> Tuple[int, ...]:
    """Compute T_index from the already-computed compressed rows."""
    upper = min(index, m)
    moves = []
    for take in range(1, upper + 1):
        previous_code = row_codes[index - take]
        if previous_code == 0 or previous_code == take:
            moves.append(take)
    return tuple(moves)


def _encode_row(moves: Tuple[int, ...], m: int) -> int:
    """Encode T_n: 0=empty, i={i}, and m+1=two or more elements."""
    if not moves:
        return 0
    if len(moves) == 1:
        return moves[0]
    return m + 1


def moves_to_losing_position(n: int, m: int) -> Tuple[int, ...]:
    """Return all take sizes that leave the opponent in a losing position.

    This is the set T_n from the exact recurrence

        T_0 = empty,
        T_n = {i: 1 <= i <= min(m,n), T_(n-i) is empty or {i}}.

    The returned moves are sorted in increasing order. The function detects a
    repeated window of ``m`` compressed rows and maps large ``n`` back into
    that exact cycle. It imposes no artificial input limit.
    """
    _validate_heap_and_cap(n, m)

    # c_n is 0 for T_n=empty, i for T_n={i}, and m+1 for |T_n|>=2.
    row_codes = [0]  # T_0 is empty.
    if n == 0:
        return ()

    # Maps a length-m state window to the first row index that followed it.
    first_seen = {}
    next_index = 1

    while next_index <= n:
        if next_index >= m:
            window = tuple(row_codes[next_index - m : next_index])
            first_index = first_seen.get(window)
            if first_index is not None:
                period = next_index - first_index
                phase_index = first_index + (n - first_index) % period
                return _moves_to_losing_row(phase_index, row_codes, m)
            first_seen[window] = next_index

        # No need to append c_n when n itself is the requested row.
        if next_index == n:
            return _moves_to_losing_row(n, row_codes, m)

        moves = _moves_to_losing_row(next_index, row_codes, m)
        row_codes.append(_encode_row(moves, m))
        next_index += 1

    # The loop returns at n or at a repeated state.
    raise AssertionError("unreachable")


def analyze(n: int, m: int, j: int = 0) -> Analysis:
    """Analyze state (n,j); j=0 means no previous take (the opening turn).

    A take in T_n wins exactly when it is not forbidden by ``j``. The
    recommendation is the smallest such take, for deterministic output.
    """
    _validate_heap_and_cap(n, m)
    _validate_integer("j", j)
    if not 0 <= j <= m:
        raise ValueError("j must be between 0 and m (inclusive)")

    moves = moves_to_losing_position(n, m)
    winning_moves = tuple(take for take in moves if take != j)
    return Analysis(n=n, m=m, previous_take=j, winning_moves=winning_moves)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="石取りゲーム（直前の取得数を禁止）の勝敗と必勝手を計算します。"
    )
    parser.add_argument("n", type=int, help="山に残っている石の数（0以上）")
    parser.add_argument("m", type=int, help="一度に取れる上限（1以上）")
    parser.add_argument(
        "j",
        type=int,
        nargs="?",
        default=0,
        help="直前に取られた数。初手は0（省略時も0）",
    )
    args = parser.parse_args()

    try:
        result = analyze(args.n, args.m, args.j)
    except (TypeError, ValueError) as exc:
        parser.error(str(exc))

    print("局面: n={}, m={}, j={}".format(result.n, result.m, result.previous_take))
    if result.can_force_win:
        print("判定: 勝ち (N局面)")
        print("おすすめ: {} 個取る".format(result.best_move))
        print("勝ち手候補: {}".format(", ".join(map(str, result.winning_moves))))
    else:
        print("判定: 負け (P局面)")
        print("必勝手はありません")


if __name__ == "__main__":
    main()

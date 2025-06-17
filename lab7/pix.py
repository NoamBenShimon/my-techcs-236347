from __future__ import annotations
import typing

from z3 import Int, Xor, BoolVal, Solver, sat, Ast, ModelRef
from functools import reduce

# fmt: off
                                            #      |   | 1 |   | 1 |   |
rows = [[Int('r00'), 1, Int('r01'), 1],     #      | 1 | 1 | 1 | 1 | 1 |
        [],                                 # -----+---+---+---+---+---+
        [Int('r20'), 1, Int('r21'), 1],     #  1 1 |   |   |   |   |   |
        [Int('r30'), 3]]                    # -----+---+---+---+---+---+
cols = [[Int('c00'), 1],                    #      |   |   |   |   |   |
        [Int('c10'), 1, Int('c11'), 1],     # -----+---+---+---+---+---+
        [Int('c20'), 1],                    #  1 1 |   |   |   |   |   |
        [Int('c30'), 1, Int('c31'), 1],     # -----+---+---+---+---+---+
        [Int('c40'), 1],                    #    3 |   |   |   |   |   |
        ]                                   # -----+---+---+---+---+---+

# fmt: on

nrows = len(rows)
ncols = len(cols)


Formula: typing.TypeAlias = Ast | bool
T = typing.TypeVar("T")


def prefix_sum(fs: list[T]) -> list[T]:
    """Auxiliary function for computing the sums of all prefixes of a list fs"""
    return [sum(fs[: i + 1]) for i in range(len(fs))]


def xor_all(fs: list[BoolVal]) -> BoolVal:
    """Auxiliary function for computing the xor of the elements of a list fs"""
    if not fs:
        return BoolVal(False)
    return reduce(Xor, fs)


def solve(*formulas: Formula) -> typing.Optional[ModelRef]:
    """
    Solves a set of formulas using SMT; prints the outcome.
    Return model if SAT, None if not.
    """
    s = Solver()
    s.add(*formulas)
    status = s.check()
    print(status)
    if status == sat:
        m = s.model()
        print(m)
        return m
    return None


def draw(sol: list[list[bool]]) -> None:
    print("-" * 40)
    for row in sol:
        print(" ".join(("■" if b else " ") for b in row))


def pix_color(j: int, r: list[int | Int]) -> Formula:
    """This function receives an index j (int) and the run-lengths r (list of ints and int unknowns),
    and returns a Boolean expression describing the color of pixel j.
    A false value represents a white pixel, a true value represents a black pixel."""
    if r is None:
        return BoolVal(False)

    s = prefix_sum(r)

    conds = [i <= j for i in s]

    return xor_all(conds)

# from z3 import *
# m = z3.Model()
# print(m.eval(pix_color(9, [1, 3, 2, 6])))
# print(m.eval(pix_color(5, [1, 3, 2, 6])))
# print([m.eval(pix_color(i, [1, 3, 2, 6])) for i in range(15)])

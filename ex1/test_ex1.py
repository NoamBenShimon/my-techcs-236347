import pytest

from syntax.lambda_typed import parse, parse_type, TypedExpr

from solution import infer_types, InsufficientAnnotationsError, TypeMismatchError


def check_legal(expr: str, expected: str) -> None:
    type_expr = infer_types(parse(expr))
    assert isinstance(type_expr, TypedExpr)
    assert str(type_expr) == f"({expected})"


def test_gift_0() -> None:
    check_legal(
        r"1",
        r"1 : int",
    )


def test_gift_1() -> None:
    check_legal(
        r"\x: int . x",
        r"\(x : int) : int. (x : int) : int -> int",
    )


def test_gift_2() -> None:
    check_legal(
        r"let f = \x. x in f 3",
        r"let f : int -> int = \(x : int) : int. (x : int) : int -> int in ((f : int -> int) (3 : int) : int) : int",
    )


def test_gift_3() -> None:
    check_legal(
        r"\(x : int). \(x : bool). (\(x : int). x)",
        r"\(x : int) : bool -> int -> int. (\(x : bool) : int -> int. (\(x : int) : int. (x : int) : int -> int) : bool -> int -> int) : int -> bool -> int -> int",
    )


def test_insufficient_0() -> None:
    expr = parse(r"x")
    with pytest.raises(InsufficientAnnotationsError):
        infer_types(expr)


def test_type_mismatch_0() -> None:
    expr = parse(r"let x: bool = 1 in x")
    with pytest.raises(TypeMismatchError):
        infer_types(expr)

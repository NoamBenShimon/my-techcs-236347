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

def test_my_test_1() -> None:
    check_legal(
        r"let x: int = 1 in let x: bool = True in x",
        r"let x : int = 1 : int in (let x : bool = True : bool in (x : bool) : bool) : bool",
    )

def test_my_test_2() -> None:
    check_legal(
        r"\x: int. \y: bool. x",
        r"\(x : int) : bool -> int. (\(y : bool) : int. (x : int) : bool -> int) : int -> bool -> int",
    )

def test_my_test_3() -> None:
    check_legal(
        r"(\x: int -> int. x 1) (\y: int. y)",
        r"(\(x : int -> int) : int. ((x : int -> int) (1 : int) : int) : int -> int -> int) (\(y : int) : int. (y : int) : int -> int) : int",
    )

def test_my_test_4() -> None:
    check_legal(
        r"let id = \x. x in let y = id 2 in id y",
        r"let id : int -> int = \(x : int) : int. (x : int) : int -> int in (let y : int = (id : int -> int) (2 : int) : int in ((id : int -> int) (y : int) : int) : int) : int",
    )

def test_my_test_5() -> None:
    check_legal(
        r"let id = \x. x in let y = id 2 in id y",
        r"let id : int -> int = \(x : int) : int. (x : int) : int -> int in (let y : int = (id : int -> int) (2 : int) : int in ((id : int -> int) (y : int) : int) : int) : int",
    )

def test_my_test_6() -> None:
    check_legal(
        r"\x: int. \y: int. x",
        r"\(x : int) : int -> int. (\(y : int) : int. (x : int) : int -> int) : int -> int -> int",
    )


def test_my_test_7() -> None:
    check_legal(
        r"let id = \x. x in let y = id 42 in id y",
        r"let id : int -> int = \(x : int) : int. (x : int) : int -> int in (let y : int = (id : int -> int) (42 : int) : int in ((id : int -> int) (y : int) : int) : int) : int",
    )


def test_my_test_8() -> None:
    check_legal(
        r"(\x: int. \y: bool. x) 3 True",
        r"((\(x : int) : bool -> int. (\(y : bool) : int. (x : int) : bool -> int) : int -> bool -> int) (3 : int) : bool -> int) (True : bool) : int",
    )


def test_my_test_9() -> None:
    check_legal(
        r"let f = \x: int. x in let g = \y: int. f y in g 10",
        r"let f : int -> int = \(x : int) : int. (x : int) : int -> int in (let g : int -> int = \(y : int) : int. ((f : int -> int) (y : int) : int) : int -> int in ((g : int -> int) (10 : int) : int) : int) : int",
    )


def test_my_test_10() -> None:
    check_legal(
        r"\x: int. let y = x in y",
        r"\(x : int) : int. (let y : int = x : int in (y : int) : int) : int -> int",
    )


def test_my_test_11() -> None:
    check_legal(
        r"(\f: int -> int. f 2) (\x: int. x)",
        r"(\(f : int -> int) : int. ((f : int -> int) (2 : int) : int) : int -> int -> int) (\(x : int) : int. (x : int) : int -> int) : int",
    )


def test_my_test_12() -> None:
    check_legal(
        r"let x: int = 1 in let y: int = 2 in x",
        r"let x : int = 1 : int in (let y : int = 2 : int in (x : int) : int) : int",
    )

def test_my_test_13() -> None:
    check_legal(
        r"let double = \x: int. x in double 4",
        r"let double : int -> int = \(x : int) : int. (x : int) : int -> int in ((double : int -> int) (4 : int) : int) : int",
    )

def test_my_test_14() -> None:
    check_legal(
        r"\f: int -> int. \x: int. f (f x)",
        r"\(f : int -> int) : int -> int. (\(x : int) : int. ((f : int -> int) ((f : int -> int) (x : int) : int) : int) : int -> int) : int -> int -> int -> int",
    )

def test_my_test_15() -> None:
    check_legal(
        r"let apply = \f: int -> int. \x: int. f x in apply (\y: int. y) 5",
        r"let apply : int -> int -> int -> int = \(f : int -> int) : int -> int. (\(x : int) : int. ((f : int -> int) (x : int) : int) : int -> int) : int -> int -> int -> int in (((apply : int -> int -> int -> int) (\(y : int) : int. (y : int) : int -> int) : int -> int) (5 : int) : int) : int",
    )

def test_my_test_16() -> None:
    check_legal(
        r"(\x: int. \y: int. y) 2 3",
        r"((\(x : int) : int -> int. (\(y : int) : int. (y : int) : int -> int) : int -> int -> int) (2 : int) : int -> int) (3 : int) : int"
    )

def test_my_test_17() -> None:
    check_legal(
        r"let const = \x: int. \y: bool. x in const 7 False",
        r"let const : int -> bool -> int = \(x : int) : bool -> int. (\(y : bool) : int. (x : int) : bool -> int) : int -> bool -> int in (((const : int -> bool -> int) (7 : int) : bool -> int) (False : bool) : int) : int",
    )

def test_my_test_18() -> None:
    check_legal(
        r"let const = \x: int. \y: bool. x in const 10 False",
        r"let const : int -> bool -> int = \(x : int) : bool -> int. (\(y : bool) : int. (x : int) : bool -> int) : int -> bool -> int in (((const : int -> bool -> int) (10 : int) : bool -> int) (False : bool) : int) : int",
    )

def test_my_test_19() -> None:
    check_legal(
        r"\x: int. \y: bool. y",
        r"\(x : int) : bool -> bool. (\(y : bool) : bool. (y : bool) : bool -> bool) : int -> bool -> bool",
    )


def test_my_test_20() -> None:
    check_legal(
        r"let f = \x: int. \y: int. x in f 1 2",
        r"let f : int -> int -> int = \(x : int) : int -> int. (\(y : int) : int. (x : int) : int -> int) : int -> int -> int in (((f : int -> int -> int) (1 : int) : int -> int) (2 : int) : int) : int",
    )


def test_my_test_21() -> None:
    check_legal(
        r"(\x.\y.\z.1) True True True",
        r"(((\(x : bool) : bool -> bool -> int. (\(y : bool) : bool -> int. (\(z : bool) : int. (1 : int) : bool -> int) : bool -> bool -> int) : bool -> bool -> bool -> int) (True : bool) : bool -> bool -> int) (True : bool) : bool -> int) (True : bool) : int",
    )


def test_my_test_22() -> None:
    check_legal(
        r"\f: int -> bool. f 5",
        r"\(f : int -> bool) : bool. ((f : int -> bool) (5 : int) : bool) : int -> bool -> bool",
    )

def test_my_test_error_1() -> None:
    expr = parse(r"let f: int -> int = \x: bool. x in f 1")
    with pytest.raises(TypeMismatchError):
        infer_types(expr)

def test_my_test_error_2() -> None:
    expr = parse(r"\x. x")
    with pytest.raises(InsufficientAnnotationsError):
        infer_types(expr)

def test_my_test_error_3() -> None:
    expr = parse(r"(\x: int. x) True")
    with pytest.raises(TypeMismatchError):
        infer_types(expr)

def test_my_error_test_4() -> None:
    expr = parse(r"let f: int -> bool = \x: int. x in f 1")
    with pytest.raises(TypeMismatchError):
        infer_types(expr)


def test_my_error_test_5() -> None:
    expr = parse(r"(\x: int. x) False")
    with pytest.raises(TypeMismatchError):
        infer_types(expr)


def test_my_error_test_6() -> None:
    expr = parse(r"\x. let y = x in y")
    with pytest.raises(InsufficientAnnotationsError):
        infer_types(expr)

def test_my_error_test_7() -> None:
    expr = parse(r"let x: int = True in x")
    with pytest.raises(TypeMismatchError):
        infer_types(expr)

def test_my_error_test_8() -> None:
    expr = parse(r"let f = \x. x in f")
    with pytest.raises(InsufficientAnnotationsError):
        infer_types(expr)

def test_my_error_test_9() -> None:
    expr = parse(r"(\x: int. x) False")
    with pytest.raises(TypeMismatchError):
        infer_types(expr)


def test_my_error_test_10() -> None:
    expr = parse(r"let f: bool -> int = \x: int. x in f 3")
    with pytest.raises(TypeMismatchError):
        infer_types(expr)


def test_my_error_test_11() -> None:
    expr = parse(r"\x. \y: int. True False")
    with pytest.raises(TypeMismatchError):
        infer_types(expr)


def test_my_error_test_12() -> None:
    expr = parse(r"let f = \x.\y.1  in f")
    with pytest.raises(InsufficientAnnotationsError):
        infer_types(expr)



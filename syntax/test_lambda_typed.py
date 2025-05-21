import pytest
from syntax.lambda_typed import (
    parse,
    Id,
    Int,
    Bool,
    App,
    Lambda,
    Let,
    VarDecl,
    Arrow,
    TypeName,
    TypedExpr,
    LambdaType,
    _instantiate_placeholders,
    Primitive,
)
from syntax.utils import ParseError


def tid(name: str) -> TypeName:
    return TypeName(name)


def arrow(a: LambdaType, b: LambdaType) -> Arrow:
    return Arrow(a, b)


def decl(name: str, type: LambdaType = None) -> VarDecl:
    return VarDecl(Id(name), type)


def id_(name: str) -> TypedExpr:
    return TypedExpr(Id(name), type=None)  # type: ignore[param]


def num(n: int) -> TypedExpr:
    return TypedExpr(Int(n), type=None)  # type: ignore[param]


def boolean(b: bool) -> TypedExpr:
    return TypedExpr(Bool(b), type=None)  # type: ignore[param]


def var(name: str, type: LambdaType = None) -> VarDecl:
    return VarDecl(Id(name), type)


def lam(decl: VarDecl, body: TypedExpr) -> TypedExpr:
    return TypedExpr(Lambda(decl, body, ret=None), type=None)  # type: ignore[param]


def app(f: TypedExpr, x: TypedExpr) -> TypedExpr:
    return TypedExpr(App(f, x), type=None)  # type: ignore[param]


def let(decl: VarDecl, defn: TypedExpr, body: TypedExpr) -> TypedExpr:
    return TypedExpr(Let(decl, defn, body), type=None)  # type: ignore[param]


@pytest.mark.parametrize(
    "program, expected",
    [
        # Identifiers
        ("x", id_("x")),
        ("foo", id_("foo")),
        # Numbers
        ("0", num(0)),
        ("42", num(42)),
        # Booleans
        ("True", boolean(True)),
        ("False", boolean(False)),
        # Lambda without type
        (r"\x. x", lam(decl("x"), id_("x"))),
        (r"\x y. x", lam(decl("x"), lam(decl("y"), id_("x")))),
        (r"\x. 5", lam(decl("x"), num(5))),
        # Lambda with type
        (r"\(x : int). x", lam(decl("x", Primitive.INT), id_("x"))),
        (
            r"\(x : int). \y : Bool. x",
            lam(decl("x", Primitive.INT), lam(decl("y", tid("Bool")), id_("x"))),
        ),
        (
            r"\(x : int) (y : Bool). x",
            lam(decl("x", Primitive.INT), lam(decl("y", tid("Bool")), id_("x"))),
        ),
        # Application
        ("5 y", app(num(5), id_("y"))),
        ("z 4", app(id_("z"), num(4))),
        ("True y", app(boolean(True), id_("y"))),
        ("z False", app(id_("z"), boolean(False))),
        ("x y", app(id_("x"), id_("y"))),
        ("(x y) z", app(app(id_("x"), id_("y")), id_("z"))),
        ("x y z", app(app(id_("x"), id_("y")), id_("z"))),
        ("x (y z)", app(id_("x"), app(id_("y"), id_("z")))),
        # Let without type
        ("let x = y in z", let(decl("x"), id_("y"), id_("z"))),
        ("let x = 5 in x", let(decl("x"), num(5), id_("x"))),
        # Let with type
        ("let x : int = 5 in x", let(decl("x", Primitive.INT), num(5), id_("x"))),
        # Let with lambda
        (
            r"let x : (int -> int) = (\y : int. y) in x",
            let(
                decl("x", arrow(Primitive.INT, Primitive.INT)),
                lam(decl("y", Primitive.INT), id_("y")),
                id_("x"),
            ),
        ),
        # Complex nesting
        (
            r"let id : (int -> int) = (\x : int. x) in id 3",
            let(
                decl("id", arrow(Primitive.INT, Primitive.INT)),
                lam(decl("x", Primitive.INT), id_("x")),
                app(id_("id"), num(3)),
            ),
        ),
    ],
)
def test_parse_valid(program, expected):
    assert parse(program) == _instantiate_placeholders(expected)


@pytest.mark.parametrize(
    "program",
    [
        "let",  # incomplete
        "\\",  # missing body
        "let x = in y",  # missing definition
    ],
)
def test_parse_invalid(program):
    with pytest.raises(ParseError):
        parse(program)

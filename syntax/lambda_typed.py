import enum
from dataclasses import dataclass
from functools import lru_cache
import itertools

from lark import Transformer, v_args, UnexpectedInput

from syntax.utils import _install_str_hook, ParseError, _read_grammar

type LambdaType = Arrow | Primitive | TypeName | TypeVar


@dataclass(frozen=True, slots=True)
class Arrow:
    arg: LambdaType
    ret: LambdaType


class Primitive(enum.Enum):
    BOOL = "bool"
    INT = "int"


@dataclass(frozen=True, slots=True)
class TypeName:
    """Represents a named type, e.g., int, bool, etc."""

    name: str


@dataclass(frozen=True, slots=True)
class TypeVar:
    """Represents a placeholder for a yet-unknown type.
    This is used when parsing an expression without an explicit type, and for type inference.
    In the former case, it will not be pretty-printed."""

    id: int  # if negative, it is an internal type variable, created during parsing and not pretty-printed

    def is_internal(self) -> bool:
        """Check if this is an internal type variable."""
        return self.id < 0


_next_typevar_id = itertools.count()


def fresh_typevar() -> TypeVar:
    """Returns a brand new TypeVar, ensuring uniqueness. The typevar is not internal."""
    return TypeVar(next(_next_typevar_id))


@lru_cache(maxsize=None)
def is_grounded_type(t: LambdaType, require_fully_annotated: bool) -> bool:
    match t:
        case None:
            # We probably forgot to freshen the type variable after parsing
            assert (
                False
            ), f"Type variable is None for {t}. Did you forget to call _instantiate_placeholders()?"
        case TypeName() | Primitive():
            return True
        case Arrow(a, b):
            return is_grounded_type(a, require_fully_annotated) and is_grounded_type(
                b, require_fully_annotated
            )
        case TypeVar():
            if require_fully_annotated:
                return False
            return t.is_internal()
        case _:
            raise ValueError(f"Unknown type: {type(t)}")


type Expr = Id | Int | Bool | Let | Lambda | App


@dataclass(frozen=True, slots=True)
class TypedExpr:
    expr: Expr
    type: LambdaType


@dataclass(frozen=True, slots=True)
class Id:
    name: str


@dataclass(frozen=True, slots=True)
class VarDecl:
    var: Id
    type: LambdaType


@dataclass(frozen=True, slots=True)
class Int:
    n: int


@dataclass(frozen=True, slots=True)
class Bool:
    b: bool


@dataclass(frozen=True, slots=True)
class Let:
    decl: VarDecl
    defn: TypedExpr
    body: TypedExpr


@dataclass(frozen=True, slots=True)
class Lambda:
    decl: VarDecl
    body: TypedExpr
    ret: LambdaType


@dataclass(frozen=True, slots=True)
class App:
    func: TypedExpr
    arg: TypedExpr


@lru_cache(maxsize=None)
def is_grounded_expr(e: TypedExpr, require_fully_annotated: bool) -> bool:
    if not is_grounded_type(e.type, require_fully_annotated):
        return False
    match e.expr:
        case Id() | Int() | Bool():
            return True
        case Let(decl, defn, body):
            return (
                is_grounded_expr(defn, require_fully_annotated)
                and is_grounded_expr(body, require_fully_annotated)
                and is_grounded_type(decl.type, require_fully_annotated)
            )
        case Lambda(decl, body):
            return is_grounded_expr(body, require_fully_annotated) and is_grounded_type(
                decl.type, require_fully_annotated
            )
        case App(func, arg):
            return is_grounded_expr(func, require_fully_annotated) and is_grounded_expr(
                arg, require_fully_annotated
            )
        case _:
            raise ValueError(f"Unknown expression: {e.expr!r}")


def _instantiate_placeholders(expr: TypedExpr) -> TypedExpr:
    """Replaces all internal type variables (None) with fresh ones.
    Used only for parsing/testing, to ensure that internal type variables are all unique.
    """
    internal_counter = itertools.count(start=-1, step=-1)

    def fresh_typevars_type(t: LambdaType) -> LambdaType:
        match t:
            case None:
                return TypeVar(next(internal_counter))
            case Arrow(arg, ret):
                return Arrow(fresh_typevars_type(arg), fresh_typevars_type(ret))
            case Primitive() | TypeName():
                return t
            case _:
                raise TypeError(f"Unexpected type node: {t}")

    def fresh_typevars_expr(e: TypedExpr) -> TypedExpr:
        match e.expr:
            case Id(name):
                return TypedExpr(Id(name), fresh_typevars_type(e.type))
            case Int(n):
                return TypedExpr(Int(n), fresh_typevars_type(e.type))
            case Bool() as b:
                return TypedExpr(b, fresh_typevars_type(e.type))
            case Let(decl, defn, body):
                return TypedExpr(
                    Let(
                        VarDecl(decl.var, fresh_typevars_type(decl.type)),
                        fresh_typevars_expr(defn),
                        fresh_typevars_expr(body),
                    ),
                    fresh_typevars_type(e.type),
                )
            case Lambda(decl, body, ret):
                return TypedExpr(
                    Lambda(
                        VarDecl(decl.var, fresh_typevars_type(decl.type)),
                        fresh_typevars_expr(body),
                        fresh_typevars_type(ret),
                    ),
                    fresh_typevars_type(e.type),
                )
            case App(func, arg):
                return TypedExpr(
                    App(
                        fresh_typevars_expr(func),
                        fresh_typevars_expr(arg),
                    ),
                    fresh_typevars_type(e.type),
                )
            case _:
                raise TypeError(f"Unexpected expression node: {e.expr!r}")

    return fresh_typevars_expr(expr)


@v_args(inline=True)
class NodeFactory(Transformer):
    def typename(self, token):
        match token.value:
            case "int":
                return Primitive.INT
            case "bool":
                return Primitive.BOOL
            case _:
                return TypeName(token.value)

    def arrow(self, arg, ret):
        return Arrow(arg, ret)

    def decl(self, id, typ=None):
        return VarDecl(Id(id.value), typ)  # typ may be None

    def var(self, token):
        if token.value == "True":
            return TypedExpr(Bool(True), None)  # type: ignore[param]
        if token.value == "False":
            return TypedExpr(Bool(False), None)  # type: ignore[param]
        return TypedExpr(Id(token.value), None)  # type: ignore[param]

    def num(self, token):
        return TypedExpr(Int(int(token.value)), None)  # type: ignore[param]

    def abs(self, *args):
        *decls, body = args
        for decl in reversed(decls):
            body = TypedExpr(Lambda(decl, body, ret=None), type=None)  # type: ignore[param]
        return body

    def abs_typed(self, decl, ret_type, body):
        return TypedExpr(Lambda(decl, body, ret=ret_type), type=None)  # type: ignore[param]

    def app(self, func, arg):
        return TypedExpr(App(func, arg), type=None)  # type: ignore[param]

    def let(self, decl, defn, body):
        return TypedExpr(Let(decl, defn, body), type=None)  # type: ignore[param]


_factory = NodeFactory()


def parse(program_text: str) -> TypedExpr:
    """Parses a typed lambda calculus program and returns the corresponding expression.
    All types are either ground types or fresh type variables for which .is_internal() is True.
    """
    grammar = _read_grammar("lambda_typed.lark", _factory)
    try:
        return _instantiate_placeholders(grammar.parse(program_text))
    except UnexpectedInput as e:
        raise ParseError(program_text) from e


def parse_type(program_text: str) -> TypedExpr:
    """Parses string representing a type and returns the corresponding type."""
    grammar = _read_grammar("lambda_typed.lark", _factory, start="type")
    try:
        return grammar.parse(program_text)
    except UnexpectedInput as e:
        raise ParseError(program_text) from e


@_install_str_hook(Arrow, TypeName, TypeVar, Primitive)
def pretty_type(expr: LambdaType) -> str:
    match expr:
        case TypeVar(id):
            if id < 0:
                return ""
            return f"${id}"
        case Primitive() as prim:
            return prim.value
        case TypeName(name):
            return name
        case Arrow(arg, ret):
            return f"{pretty_type(arg)} -> {pretty_type(ret)}"
        case _:
            raise ValueError(f"Unknown type: {type(expr)}")


@_install_str_hook(VarDecl)
def pretty_decl(decl: VarDecl, omit_parens=False) -> str:
    """Formats a variable declaration for pretty printing."""
    type_str = pretty_type(decl.type)
    if not type_str:
        return decl.var.name
    type_str = f"{decl.var.name} : {type_str}"
    if omit_parens:
        return type_str
    return f"({type_str})"


@_install_str_hook(Id, Int, Bool, Let, Lambda, App)
def pretty(expr: Expr) -> str:
    """Formats an expression for pretty printing."""
    match expr:
        case Id(name):
            return name
        case Int(n):
            return str(n)
        case Bool(b):
            return "True" if b else "False"
        case Let() as let:
            return f"let {pretty_decl(let.decl, omit_parens=True)} = {pretty_typed(let.defn, omit_parens=True)} in {pretty_typed(let.body)}"
        case Lambda(decl, body, ret):
            if isinstance(ret, TypeVar) and ret.is_internal():
                return rf"\{pretty_decl(decl)}. {pretty_typed(body)}"
            return rf"\{pretty_decl(decl)} : {pretty_type(ret)}. {pretty_typed(body)}"
        case App(func, arg):
            return f"{pretty_typed(func)} {pretty_typed(arg)}"
        case _:
            raise ValueError(f"Unknown expression type: {expr!r}")


@_install_str_hook(TypedExpr)
def pretty_typed(expr: TypedExpr, omit_parens=False) -> str:
    """Formats a typed expression for pretty printing."""
    if isinstance(expr.type, TypeVar) and expr.type.is_internal():
        return pretty(expr.expr)
    res = f"{pretty(expr.expr)} : {pretty_type(expr.type)}"
    if omit_parens:
        return res
    return f"({res})"

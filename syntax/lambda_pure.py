from dataclasses import dataclass

from lark import Transformer, v_args, UnexpectedInput

from syntax.utils import make_node, ParseError, _read_grammar, _install_str_hook


type LambdaExpr = Id | Int | Let | Lambda | App


@dataclass(frozen=True, slots=True)
class Id:
    name: str

    def __eq__(self, other):
        if isinstance(other, Id):
            return self.name == other.name
        if isinstance(other, str):  # allow comparison with string directly
            return self.name == other
        return NotImplemented

    # Less than: compare based on the 'value' field
    def __lt__(self, other):
        if isinstance(other, Id):
            return self.name < other.name
        if isinstance(other, str):  # allow comparison with string directly
            return self.name < other
        return NotImplemented

    # Optional: you can define other operators, if necessary
    def __le__(self, other):
        if isinstance(other, Id):
            return self.name <= other.name
        if isinstance(other, str):  # allow comparison with string directly
            return self.name <= other
        return NotImplemented

    def __hash__(self):
        return hash(self.name)

    def __str__(self):
        return pretty(self)

    def __repr__(self):
        return self.__str__()


@dataclass(frozen=True, slots=True)
class Int:
    n: int

    def __str__(self):
        return pretty(self)

    def __repr__(self):
        return self.__str__()


@dataclass(frozen=True, slots=True)
class Let:
    decl: Id
    defn: LambdaExpr
    body: LambdaExpr

    def __str__(self):
        return pretty(self)

    def __repr__(self):
        return self.__str__()


@dataclass(frozen=True, slots=True)
class Lambda:
    var: Id
    body: LambdaExpr

    def __str__(self):
        return pretty(self)

    def __repr__(self):
        return self.__str__()


@dataclass(frozen=True, slots=True)
class App:
    func: LambdaExpr
    arg: LambdaExpr

    def __str__(self):
        return pretty(self)

    def __repr__(self):
        return self.__str__()


@v_args(inline=True)
class NodeFactory(Transformer):
    def var(self, name):
        return make_node(Id, name.value)

    def decl(self, name):
        return make_node(Id, name.value)

    def num(self, value):
        return make_node(Int, int(value.value))

    def let(self, decl, defn, body):
        return make_node(Let, decl, defn, body)

    def abs(self, *args):
        *params, body = args
        for param in reversed(params):
            body = make_node(Lambda, param, body)
        return body

    def app(self, func, arg):
        return make_node(App, func, arg)


_factory = NodeFactory()


def parse(program_text: str) -> LambdaExpr:
    """Parses a lambda calculus program and returns the corresponding expression."""
    parser = _read_grammar("lambda_pure.lark", _factory)
    try:
        return parser.parse(program_text)
    except UnexpectedInput as e:
        raise ParseError() from e


@_install_str_hook(Id, Int, Let, Lambda, App)
def pretty(expr: LambdaExpr) -> str:
    """Formats an expression for pretty printing."""
    match expr:
        case Id(n):
            return n
        case Int(num):
            return str(num)
        case Let(var, defn, body):
            return f"let {var.name} = {pretty(defn)} in {pretty(body)}"
        case Lambda(var, body):
            return f"\\{var.name}. {pretty(body)}"
        case App(func, arg):
            if isinstance(func, (Lambda, Let)):
                return f"(({pretty(func)}) {pretty(arg)})"
            return f"({pretty(func)} {pretty(arg)})"
        case _:
            raise ValueError(f"Unknown expression type: {type(expr)}")

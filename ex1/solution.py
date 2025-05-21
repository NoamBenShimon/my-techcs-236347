"""
Homework 1

Your task:
Implement type checking and type inference for simply-typed lambda calculus.
"""

from syntax.lambda_typed import parse, TypedExpr, is_grounded_expr, Id, Expr, LambdaType, VarDecl, App, Lambda, Let


class TypeMismatchError(TypeError):
    pass


class InsufficientAnnotationsError(TypeError):
    pass


def infer_types(expr: TypedExpr) -> TypedExpr:
    """
    Input: an expression with ungrounded types (containing TypeVar types).
    Output: An ast with all the types explicitly inferred.
     * If encountered a unification error, raise TypeMismatchError
     * If some types cannot be inferred, raise InsufficientAnnotationsError
    """
    assert is_grounded_expr(expr, require_fully_annotated=False)

    # General sketch of the implementation:
    # Input: AST Expression
    #
    # 1. Go on and label vars with general types, collecting them in the process into the environment
    # 2.
    #

    match expr:
        case VarDecl(var, varType):
            """were given a var and its type, should be added to env. """

            # Type[var]     =   Type[varType]
            pass # TODO: Implement VarDecl case

        case Let(decl, defn, body):
            # Type[decl]    =   Type[defn]
            # Type[expr]    =   Type[body] // TODO: Recheck
            pass # TODO: Implement Let case

        case Lambda(decl, body, ret):
            # Type[body]    =   { Type[ret] } v { Type[??? --> Type[ret] }
            # Type[expr]    =   Type[decl] --> Type[ret]
            pass # TODO: Implement Lambda case

        case App(func, arg):
            # Type[func] = Type[arg] --> ???
            pass # TODO: Implement App case

        # case TypedExpr(te, tt):
        #     pass # TODO: Implement different matches for `te`

        # TODO: List other matches

        case _:
            raise TypeError(f"Unknown expression type (unrelated to grounded types): {expr}")

    result: TypedExpr = ...
    raise NotImplementedError

    assert is_grounded_expr(result, require_fully_annotated=True)
    return result


def main() -> None:
    expr = parse(r"""\x: int. x""")
    print(f"{expr!r}")
    print(f"{expr}")
    print(infer_types(expr))


if __name__ == "__main__":
    main()


def build_type_tree_with_type_dicts():
    """
    Builds a type tree with type dictionaries.
    The type tree is a dictionary of dictionaries, where the outer dictionary maps variable names to types,
    and the inner dictionary maps type names to types."""


def solve_constraints():
    #def apply upwards

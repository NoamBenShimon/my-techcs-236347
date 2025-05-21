"""
Homework 1

Your task:
Implement type checking and type inference for simply-typed lambda calculus.
"""

from syntax.lambda_typed import parse, TypedExpr, is_grounded_expr, Id, Expr, LambdaType, VarDecl, App, Lambda, Let, \
    Arrow


class TypeMismatchError(TypeError):
    pass


class InsufficientAnnotationsError(TypeError):
    pass


def solve_constraints(expr: TypedExpr, env: dict[Id, LambdaType]) -> TypedExpr:


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
            # Type[var]     =   Type[varType]
            return expr
            pass # TODO: Implement VarDecl case

        case Let(decl, defn, body):
            # Type[decl]    =   Type[defn]
            # Type[expr]    =   Type[body] // TODO: Recheck
            assert(isinstance(decl, VarDecl))
            assert(isinstance(defn, TypedExpr))
            assert(isinstance(body, TypedExpr))
            # let x=y in z
            # App(\\ x. z)(y)

            unsuger_expr: App = (
                App(TypedExpr(
                        Lambda( decl,
                                body,
                                body.type),
                        Arrow(decl.type, body.type)),
                    defn))

            return infer_types(
                        TypedExpr(
                            unsuger_expr, body.type
                        )
                    )

        case Lambda(decl, body, ret):
            # Type[body]    =   Type[ret]
            # Type[expr]    =   Type[decl] --> Type[ret]

            assert (isinstance(decl, VarDecl))
            assert (isinstance(body, TypedExpr))
            assert (isinstance(ret, LambdaType))





            pass # TODO: Implement Lambda case

        case App(func, arg):
            # Type[expr]    =   Type[func] --> Type[arg]
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

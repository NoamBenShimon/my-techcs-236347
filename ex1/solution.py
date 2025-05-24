"""
Homework 1

Your task:
Implement type checking and type inference for simply-typed lambda calculus.
"""
from dataclasses import field, dataclass

from syntax.lambda_typed import parse, TypedExpr, is_grounded_expr, Id, LambdaType, VarDecl, App, Lambda, Let, \
    Arrow, TypeVar, Primitive, Int, Bool, TypeName


class TypeMismatchError(TypeError):
    pass


class InsufficientAnnotationsError(TypeError):
    pass

@dataclass
class Environment:
    bindings: dict[str, LambdaType] = field(default_factory=dict)

    def extend(self, name: str, var_type: LambdaType) -> 'Environment':
        new_env = Environment()
        new_env.bindings = self.bindings.copy()
        new_env.bindings[name] = var_type
        return new_env

    def __contains__(self, var_name: str) -> bool:
        return var_name in self.bindings

    def __getitem__(self, var_name: str) -> LambdaType:
        if var_name in self.bindings:
            return self.bindings[var_name]
        else:
            raise InsufficientAnnotationsError(f"Variable {var_name} not found in environment.")

    def __setitem__(self, var_name: str, var_type: LambdaType) -> None:
        self.bindings[var_name] = var_type

    def __repr__(self) -> str:
        return f"Environment({self.bindings})"

    def __str__(self) -> str:
        return f"Environment({self.bindings})"

@dataclass
class Substitution:
    mappings: dict[int, LambdaType] = field(default_factory=dict)

    def __init__(self, mappings: dict[int, LambdaType] = None):
        if mappings is None:
            self.mappings = {}
        else:
            self.mappings = mappings

    def __getitem__(self, var_id: int, ret: LambdaType = None) -> LambdaType:
        return self.mappings.get(var_id, ret)

    def __setitem__(self, var_id: int, var_type: LambdaType) -> None:
        self.mappings[var_id] = var_type

    def __contains__(self, var_id: int) -> bool:
        return var_id in self.mappings

    def __add__(self, other: 'Substitution') -> 'Substitution':
        result = Substitution(self.mappings.copy())
        for var_id, var_type in other.mappings.items():
            if var_id not in result.mappings:
                result.mappings[var_id] = var_type
        return result


    def apply_to_type(self, t: LambdaType) -> LambdaType:
        match t:
            case TypeVar(t_id):
                return self.mappings.get(t_id, t)
            case Arrow(arg, ret):
                return Arrow(self.apply_to_type(arg), self.apply_to_type(ret))
            case Primitive() | LambdaType():
                return t
            case _:
                raise TypeError(f"Unexpected type: {t}")

    def apply_to_env(self, env: Environment) -> Environment:
        new_env = Environment()
        for var_name, var_type in env.bindings.items():
            new_env[var_name] = self.apply_to_type(var_type)
        return new_env

    def apply_to_expr(self, expr: TypedExpr) -> TypedExpr:
        new_type = self.apply_to_type(expr.type)

        match expr.expr:
            case Id(_) | Int(_) | Bool(_):
                return TypedExpr(expr.expr, new_type)

            case Let(decl, defn, body):
                new_decl_type = self.apply_to_type(decl.type)
                new_decl = VarDecl(decl.var, new_decl_type)
                new_defn = self.apply_to_expr(defn)
                new_body = self.apply_to_expr(body)
                return TypedExpr(Let(new_decl, new_defn, new_body), new_type)

            case Lambda(decl, body, ret):
                new_decl_type = self.apply_to_type(decl.type)
                new_decl = VarDecl(decl.var, new_decl_type)
                new_body = self.apply_to_expr(body)
                new_ret = self.apply_to_type(ret)
                return TypedExpr(Lambda(new_decl, new_body, new_ret), new_type)

            case App(func, arg):
                new_func = self.apply_to_expr(func)
                new_arg = self.apply_to_expr(arg)
                return TypedExpr(App(new_func, new_arg), new_type)

            case _:
                raise TypeError(f"Unexpected expression: {expr}")

    def __call__(self, expr: TypedExpr) -> TypedExpr:
        return self.apply_to_expr(expr)

    def __repr__(self) -> str:
        return f"Substitution({self.mappings})"

    def __str__(self) -> str:
        return f"Substitution({self.mappings})"

def check_instance(var_id: int, type: LambdaType) -> bool:
    match type:
        case TypeVar(id):
            return id == var_id
        case Arrow(arg, ret):
            return check_instance(var_id, arg) or check_instance(var_id, ret)
        case Primitive() | LambdaType() | TypeName(_):
            return False
        case _:
            raise TypeError(f"Unexpected type: {type}")

def unify(type1: LambdaType, type2: LambdaType) -> Substitution:
    match (type1, type2):
        case TypeVar(id1), TypeVar(id2) if id1 == id2:
            return Substitution()

        case TypeVar(id), _: # Circular dependency check
            if check_instance(id, type2):
                raise TypeMismatchError(f"Cannot unify {type1} with {type2}: circular dependency detected.")
            return Substitution({id: type2})

        case _, TypeVar(id):
            if check_instance(id, type1):
                raise TypeMismatchError(f"Cannot unify {type1} with {type2}: circular dependency detected.")
            return Substitution({id: type1})

        case Arrow(arg1, ret1), Arrow(arg2, ret2):
            sub1 = unify(arg1, arg2)
            sub2 = unify(sub1.apply_to_type(ret1), sub1.apply_to_type(ret2))
            return sub1 + sub2

        case Primitive(), Primitive():
            if type1 != type2:
                raise TypeMismatchError(f"Cannot unify {type1} with {type2}: type mismatch.")
            return Substitution()

        case LambdaType(), LambdaType():
            if type1 != type2:
                raise TypeMismatchError(f"Cannot unify {type1} with {type2}: type mismatch.")
            return Substitution()

        case _:
            raise TypeMismatchError(f"Cannot unify {type1} with {type2}: type mismatch.")

def infer_expr(expr: TypedExpr, env: Environment) -> tuple[Substitution, TypedExpr]:
    match expr.expr:
        case Id(name):
            var_type = env[name]
            if var_type is None:
                raise InsufficientAnnotationsError(f"Unbound variable {name}.")
            return Substitution(), TypedExpr(expr.expr, var_type)

        case Int(_):
            return Substitution(), TypedExpr(expr.expr, Primitive.INT)

        case Bool(_):
            return Substitution(), TypedExpr(expr.expr, Primitive.BOOL)

        case Let(decl, defn, body):
            # Type[decl]    =   Type[defn]
            # Type[expr]    =   Type[body]
            assert (isinstance(decl, VarDecl) and isinstance(defn, TypedExpr) and isinstance(body, TypedExpr))

            sub1, typed_defn = infer_expr(defn, env)
            decl_type = sub1.apply_to_type(decl.type)

            try:    # Type[decl]    =   Type[defn]
                sub2 = unify(typed_defn.type, decl_type)
            except TypeMismatchError as e:
                raise TypeMismatchError(f"Type mismatch in Let binding: {e}")

            sub3 = sub1 + sub2
            new_env = env.extend(decl.var.name, sub3.apply_to_type(decl_type))

            sub4, typed_body = infer_expr(sub3(body), new_env)

            sub5 = sub3 + sub4

            new_let = Let (
                VarDecl(decl.var, sub5.apply_to_type(decl_type)),
                sub5(typed_defn),
                typed_body # already recurses over body - so it should be fine
            )

            return sub5, TypedExpr(new_let, sub5.apply_to_type(typed_body.type))

        case Lambda(decl, body, ret):
            decl_type = decl.type
            new_env = env.extend(decl.var.name, decl_type)

            sub1, typed_body = infer_expr(body, new_env)

            inf_ret = sub1.apply_to_type(ret)

            try:    # Type[body]    =   Type[ret]
                sub2 = unify(typed_body.type, inf_ret)
            except TypeMismatchError as e:
                raise TypeMismatchError(f"Lambda body-return type mismatch: {e}")

            sub3 = sub1 + sub2
            final_decl_type = sub3.apply_to_type(decl_type)
            final_body_type = sub3.apply_to_type(typed_body.type)

            new_lambda = Lambda(
                VarDecl(decl.var, final_decl_type),
                sub3(typed_body),
                final_body_type
            )

            return sub3, TypedExpr(new_lambda, Arrow(final_decl_type, final_body_type))

        case App(func, arg):
            assert (isinstance(func, TypedExpr) and isinstance(arg, TypedExpr))

            sub1, typed_func = infer_expr(func, env)
            sub2, typed_arg = infer_expr(sub1(arg), sub1.apply_to_env(env))

            func_type = sub1.apply_to_type(typed_func.type)

            if not isinstance(func_type, Arrow):
                raise TypeMismatchError(f"Function type expected, but got {func_type}.")
            sub3 = unify(func_type.arg, typed_arg.type)

            sub4 = sub1 + sub2 + sub3

            new_app = App(
                sub4(typed_func),
                sub4(typed_arg),
            )

            return sub4, TypedExpr(new_app, sub4.apply_to_type(func_type.ret))

        case _:
            raise TypeError(f"Unknown expression: {expr.expr}")

def infer_types(expr: TypedExpr) -> TypedExpr:
    """
    Input: an expression with ungrounded types (containing TypeVar types).
    Output: An ast with all the types explicitly inferred.
     * If encountered a unification error, raise TypeMismatchError
     * If some types cannot be inferred, raise InsufficientAnnotationsError
    """
    assert is_grounded_expr(expr, require_fully_annotated=False)

    env = Environment()
    subst, typed_expr = infer_expr(expr, env)

    result: TypedExpr = subst.apply_to_expr(typed_expr)

    if not is_grounded_expr(result, require_fully_annotated=True):
        raise InsufficientAnnotationsError("Expression has insufficient type annotations")
    return result


def main() -> None:
    expr = parse(r"""\x: int. x""")
    print(f"{expr!r}")
    print(f"{expr}")
    print(infer_types(expr))


if __name__ == "__main__":
    main()

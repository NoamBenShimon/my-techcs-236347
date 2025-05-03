from unittest import case

from syntax.lambda_pure import *
from syntax.lambda_pure import Id

###########################################
#         CHURCH ENCODINGS                #
###########################################

# Boolean values and operations
TRUE = Lambda(Id('x'), Lambda(Id('y'), Id('x')))
"""The Church encoding for boolean TRUE: λx.λy.x"""

FALSE = Lambda(Id('x'), Lambda(Id('y'), Id('y')))
"""The Church encoding for boolean FALSE: λx.λy.y"""

IF = Lambda(Id('b'), Lambda(Id('x'), Lambda(Id('y'), App(App(Id('b'), Id('x')), Id('y')))))
"""Conditional expression: λb.λx.λy.((b x) y)"""

# Boolean operations
AND = Lambda(Id('p'), Lambda(Id('q'), App(App(Id('p'), Id('q')), Id('p'))))
"""Logical AND: λp.λq.((p q) p)"""

OR = Lambda(Id('p'), Lambda(Id('q'), App(App(Id('p'), Id('p')), Id('q'))))
"""Logical OR: λp.λq.((p p) q)"""

NOT = Lambda(Id('p'), App(App(Id('p'), FALSE), TRUE))
"""Logical NOT: λp.(p FALSE TRUE)"""

XOR = Lambda(Id('p'), Lambda(Id('q'), App(App(Id('p'), App(NOT, Id('q'))), Id('q'))))
"""Logical XOR: λp.λq.(p (NOT q) q)"""

NAND = Lambda(Id('p'), Lambda(Id('q'), App(NOT, App(App(Id('p'), Id('q')), Id('p')))))
"""Logical NAND: λp.λq.NOT ((p q) p)"""

# Numeric operations
ISZERO = Lambda(Id("n"), App(App(Id("n"), Lambda(Id("x"), FALSE)), TRUE))
"""Check if a Church numeral is zero: λn.(n (λx.FALSE) TRUE)"""

SUCC = Lambda(Id('n'), Lambda(Id('f'), Lambda(Id('x'),
                App(Id('f'), App(App(Id('n'), Id('f')), Id('x'))))))
"""Church numeral successor: λn.λf.λx.(f ((n f) x))"""

PRED = Lambda(Id("n"), Lambda(Id("f"), Lambda(Id("x"),
                App(App(App(Id("n"),
                    Lambda(Id("g"), Lambda(Id("h"), App(Id("h"), App(Id("g"), Id("f")))))),
                    Lambda(Id("u"), Id("x"))),
                    Lambda(Id("u"), Id("u"))))))
"""Church numeral predecessor: λn.λf.λx.(n (λg.λh.(h (g f))) (λu.x) (λu.u))"""

ADD = Lambda(Id('m'), Lambda(Id('n'), Lambda(Id('f'), Lambda(Id('x'),
                App(App(Id('m'), Id('f')), App(App(Id('n'), Id('f')), Id('x')))))))
"""Church numeral addition: λm.λn.λf.λx.((m f) ((n f) x))"""

SUB = Lambda(Id("m"), Lambda(Id("n"), App(App(Id("n"), PRED), Id("m"))))
"""Church numeral subtraction: λm.λn.((n PRED) m)"""

MULT = Lambda(Id('m'), Lambda(Id('n'), Lambda(Id('f'), App(Id('m'), App(Id('n'), Id('f'))))))
"""Church numeral multiplication: λm.λn.λf.(m (n f))"""

LEQ = Lambda(Id("m"), Lambda(Id("n"), App(ISZERO, App(App(SUB, Id("m")), Id("n")))))
"""Less than or equal comparison: λm.λn.ISZERO ((SUB m) n)"""

EQ = Lambda(Id("m"), Lambda(Id("n"),
         App(App(AND,
             App(App(LEQ, Id("m")), Id("n"))),
             App(App(LEQ, Id("n")), Id("m")))
))
"""Equality: λm.λn.((LEQ m n) AND (LEQ n m))"""

NEQ = Lambda(Id("m"), Lambda(Id("n"), App(NOT, App(App(EQ, Id("m")), Id("n")))))
"""Inequality: λm.λn.NOT (EQ m n)"""

# Recursion
Y = Lambda(Id('f'), App(Lambda(Id('x'), App(Id('f'), App(Id('x'), Id('x')))),
                         Lambda(Id('x'), App(Id('f'), App(Id('x'), Id('x'))))))
"""Y combinator (fixed-point combinator): λf.((λx.(f (x x))) (λx.(f (x x))))"""

GCD = App(Y, Lambda(Id('r'), Lambda(Id('a'), Lambda(Id('b'),
                    App(
                        App(
                            App(IF, App(App(NEQ, Id('a')), Id('b'))),
                            App(
                                App(
                                    App(IF, App(App(LEQ, Id('a')), Id('b'))),
                                    App(App(Id('r'), Id('a')), App(App(SUB, Id('b')), Id('a')))
                                ),
                                App(App(Id('r'), App(App(SUB, Id('a')), Id('b'))), Id('b'))
                            )
                        ), Id('a'))))))
"""
GCD:        Y ( λr. λa. λb.
                IF  (NEQ (a) (b))
                    (IF 
                    (LEQ (a) (b))   // Then
                        (r a (SUB (b) (a))) // GCD(a, b-a)
                        (r (SUB (a) (b)) b) // GCD(a-b, b)
                    a)              // Else
"""


###########################################
#         VARIABLE MANAGEMENT             #
###########################################

# Get bound & free variables
def get_bound(context: LambdaExpr) -> set[Id]:
    """
    Get all bound variables in a lambda expression.

    Args:
        context (LambdaExpr): Lambda expression to be analyzed.

    Returns:
        set[Id]: A set of bound variable Id objects.

    Raises:
        NotImplementedError: If the expression type is not supported.

    Notes:
        - If context is an Id, it would return an empty set. That is because if it bound, it would be picked off from the Lambda or Let expressions that hold it.

    """

    match context:
        case Id(_) | Int(_):
            return set()

        case Lambda(var, body):
            return {var} | get_bound(body)

        case App(func, arg):
            return get_bound(func) | get_bound(arg)

        case Let(decl, defn, body):
            return {decl} | get_bound(defn) | get_bound(body)

        case _:
            raise NotImplementedError(f"Unsupported expression type: {type(context)}")

def get_free(e: LambdaExpr) -> set[Id]:
    match e:
        case Id(_):
            return {e}

        case Int(_):
            return set()

        case Lambda(var, body):
            return get_free(body) - {var}

        case App(func, arg):
            return get_free(func) | get_free(arg)

        case Let(decl, defn, body):
            return get_free(defn) | (get_free(body) - {decl})

        case _:
            raise NotImplementedError(f"Unsupported expression type: {type(e)}")

def is_name_bound(name: Id, context: LambdaExpr) -> bool:
    """
    Check if a name is bound in a given context.

    Args:
        name    (Id):           The name to check.
        context (LambdaExpr):   The context in which to check for the name.

    Returns:
        bool: `True` if the name is bound in the context, `False` otherwise.

    Notes:
        - Could be implemented using get_bound_names. It would be less efficient, but more readable.

    """

    match context:
        case Id(_) | Int(_):
            return False

        case Lambda(var, body):
            return (var == name
                    or is_name_bound(name, body))

        case App(func, arg):
            return (is_name_bound(name, func)
                    or is_name_bound(name, arg))

        case Let(decl, defn, body):
            return (decl == name
                    or is_name_bound(name, defn)
                    or is_name_bound(name, body))

        case _:
            raise NotImplementedError(f"Unsupported expression type: {type(context)}")

def is_name_free(name: Id, context: LambdaExpr) -> bool:
    return name in get_free(context)

def get_free_name(*args: LambdaExpr, bound_names: set[Id] = None,
                  base_name: Id = Id("t"),
                  safety_limit: int = 1000) -> Id:
    """
    Get a free name that is not already bound in the given context.

    Args:
        *args           (LambdaExpr):   Lambda expressions to check for bound names.
        bound_names     (set[Id]):      A set of bound variable Id objects.
        base_name       (Id):           The base name to start with.
        safety_limit    (int):          The maximum number of iterations to prevent infinite loops.

    Returns:
        Id: A free name that is not already bound in the given context. Possibly the original base_name.

    Raises:
        RecursionError: If the maximum recursion depth is exceeded.

    """

    if bound_names is None:
        bound_names = set()

    counter: int = 0

    while counter < safety_limit:

        if counter == 0: # TODO: Do not need this, as we already check if the name is free in most cases - use only else
            new_name: Id = base_name
        else:
            new_name: Id = Id(f"{base_name.name}{counter}")

        is_free: bool = new_name not in bound_names
        if is_free:
            for expr in args:
                if expr is not None and is_name_bound(new_name, expr):
                    is_free = False
                    break

            if is_free:
                return new_name

        counter += 1

    raise RecursionError(f"Maximum recursion depth {safety_limit} exceeded")


###########################################
#         ALPHA CONVERSIONS               #
###########################################

def alpha_rename(e: LambdaExpr, old: Id, new: Id) -> LambdaExpr:

    match e:
        case Id(_):
            return new if e == old else e

        case Int(_):
            return e

        case Let(decl, defn, body):
            if decl == old:             # Allow hiding!
                return Let(decl,
                           alpha_rename(defn, old, new),
                           body)

            return Let(decl,
                       alpha_rename(defn, old, new),
                       alpha_rename(body, old, new))

        case Lambda(var, body):
            if var == old:              # Allow hiding!
                return e
            if var == new:              # Avoid renaming to the same name
                return e

            return Lambda(e.var,
                          alpha_rename(body, old, new))

        case App(func, arg):
            return App(alpha_rename(func, old, new),
                       alpha_rename(arg, old, new))

        case _:
            raise NotImplementedError(f"Unsupported expression type: {type(e)}")

def alpha_equivalent(e1: LambdaExpr, e2: LambdaExpr) -> bool:
    """Check if two lambda expressions differ only in the names of their bound variables."""
    # """Preforming a series of alpha-conversions (renaming)"""

    match (e1, e2):
        case (Id(_), Id(_)):
            return e1 == e2

        case (Int(_), Int(_)):
            return e1.n == e2.n

        case (Lambda(var1, body1), Lambda(var2, body2)):
            if var1 == var2:
                return alpha_equivalent(body1, body2)

            new_var: Id = get_free_name(e1, e2, base_name=var1)
            renamed_body1: Lambda = alpha_rename(body1, old=var1, new=new_var)
            renamed_body2: Lambda = alpha_rename(body2, old=var2, new=new_var)

            return alpha_equivalent(renamed_body1, renamed_body2)

        case (App(func1, arg1), App(func2, arg2)):
            return (alpha_equivalent(func1, func2) and
                    alpha_equivalent(arg1, arg2))

        case (Let(decl1, defn1, body1), Let(decl2, defn2, body2)):
            if decl1 == decl2:
                return (alpha_equivalent(defn1, defn2) and
                        alpha_equivalent(body1, body2))

            new_decl: Id = get_free_name(e1, e2, base_name=decl1)
            e1_renamed: Let = alpha_rename(e1, old=decl1, new=new_decl)
            e2_renamed: Let = alpha_rename(e2, old=decl2, new=new_decl)

            return (alpha_equivalent(e1_renamed.defn, e2_renamed.defn) and
                    alpha_equivalent(e1_renamed.body, e2_renamed.body))

        case (_, _):
            return False

    return False


###########################################
#         BETA REDUCTIONS                 #
###########################################

def beta_reduction(func: Lambda, arg: LambdaExpr)-> LambdaExpr:

    def replace(e: LambdaExpr, old: Id, new: LambdaExpr) -> LambdaExpr:
        """
        Replace all occurrences of old with new in the expression e.

        Args:
            e   (LambdaExpr):   The expression in which to replace.
            old (Id):           The old name to be replaced.
            new (LambdaExpr):   The new name to replace the old name.

        Returns:
            LambdaExpr: The expression after replacement.

        Raises:
            NotImplementedError: If the expression type is not supported.

        """

        match e:
            case Id(_):
                return new if e == old else e

            case Int(_):
                return e

            case Lambda(var, body):
                if var == old:
                    return e

                # We need to check if any free variables in 'new' would be captured by e.var
                # No need to rename if e.var doesn't occur in new (it can't capture anything)
                if var not in get_free(new):
                    return Lambda(var,
                                  replace(body, old, new))

                # Rename the bound variable to avoid variable capture
                new_var = get_free_name(body, new, bound_names={old}, base_name=var)
                new_body = alpha_rename(body, old=var, new=new_var)
                return Lambda(new_var,
                              replace(new_body, old, new))

            case App(func, arg):
                return App(replace(func, old, new),
                           replace(arg, old, new))

            case Let(decl, defn, body):
                if decl == old:
                    return Let(e.decl,
                               replace(defn, old, new),
                               body)

                if decl not in get_free(new):
                    return Let(decl,
                               replace(defn, old, new),
                               replace(body, old, new))

                new_decl = get_free_name(body, new, bound_names={decl}, base_name=decl)
                new_body = alpha_rename(body, old=decl, new=new_decl)
                return Let(new_decl,
                           replace(defn, old, new),
                           new_body)

            case _:
                raise NotImplementedError(f"Unsupported expression type: {type(e)}")

    return replace(func.body, old=func.var, new=arg)


###########################################
#         ETA REDUCTIONS                  #
###########################################

def is_eta_redex(e: LambdaExpr) -> bool:

    return (isinstance(e, Lambda)       and
            isinstance(e.body, App)     and
            isinstance(e.body.arg, Id)  and
            e.body.arg == e.var         and
            e.var not in get_free(e.body.func))

def eta_reduction(e: LambdaExpr) -> LambdaExpr:

    match e:
        case Id(_) | Int(_):
            return e

        case Lambda(var, body):
            eta_reduced_body = eta_reduction(body)

            if is_eta_redex(Lambda(var, eta_reduced_body)):
                return eta_reduced_body.func

            return Lambda(var, eta_reduced_body)

        case App(func, arg):
            return App(eta_reduction(func),
                       eta_reduction(arg))

        case Let(decl, defn, body):
            return Let(decl,
                       eta_reduction(defn),
                       eta_reduction(body))

        case _:
            raise NotImplementedError(f"Unsupported expression type: {type(e)}")


###########################################
#         EVALUATION                      #
###########################################

def normal_order_reduction(e: LambdaExpr) -> LambdaExpr:

    match e:
        case Id(_):
            return e

        case Int(_):
            return int_to_church(e.n)

        case Let(decl, defn, body):
            # Transform "let" statement to "(\lambda defl. body) defn"
            e_lambda: Lambda = Lambda(decl, body)
            return normal_order_reduction(App(e_lambda, defn))

        case Lambda(var, body):
            reduced_body = normal_order_reduction(body)
            if alpha_equivalent(reduced_body, body):
                return e
            return Lambda(var, reduced_body)

        case App(func, arg):
            if isinstance(func, Lambda):
                return beta_reduction(func, arg)

            func_reduced = normal_order_reduction(func)
            if not alpha_equivalent(func_reduced, func):
                return normal_order_reduction(App(func_reduced, arg))

            arg_reduced = normal_order_reduction(arg)
            if not alpha_equivalent(arg_reduced, arg):
                return App(func, arg_reduced)

            return e

        case _:
            raise NotImplementedError(f"Unsupported expression type: {type(e)}")

def interpret(e: LambdaExpr, fuel: int = 100_000) -> LambdaExpr:
    """Keep performing normal-order reduction steps until you reach normal form, detect divergence or run out of fuel."""

    result = e
    while fuel > 0:
        reduced = normal_order_reduction(result)
        if alpha_equivalent(reduced, result):
            return result
        result = reduced
        fuel -= 1

    print("Recursion depth exceeded; Current result: " + pretty(result))
    raise RecursionError("Maximum recursion depth exceeded")

def int_to_church(n: int) -> LambdaExpr:

    f: Id = Id('f')
    x: Id = Id('x')
    body = x

    while n > 0:
        n -= 1
        body = App(f, body) # Get the successor - (f body)

    return Lambda(f, Lambda(x, body))  # \\ f. \\ x. (body)

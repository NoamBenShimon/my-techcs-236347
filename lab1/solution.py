from unittest import case

from syntax.lambda_pure import *
from syntax.lambda_pure import Id

# Popular lambda-expressions
TRUE    = Lambda(Id('x'), Lambda(Id('y'), Id('x')))
"""
The `TRUE` lambda expression represents the boolean value `True` in lambda calculus.
It is defined as: `\\x y. x`
When applied to two arguments, it always returns the first argument.
"""

FALSE   = Lambda(Id('x'), Lambda(Id('y'), Id('y')))
"""
The `FALSE` lambda expression represents the boolean value `False` in lambda calculus.
It is defined as: `\\x y. y`
When applied to two arguments, it always returns the second argument.
"""

IF      = Lambda(Id('b'), Lambda(Id('x'), Lambda(Id('y'), App(App(Id('b'), Id('x')), Id('y')))))
"""
The `IF` lambda expression represents a conditional statement in lambda calculus.
It is defined as: `\\b x y. ((b x) y)`

It takes three arguments:
1. `b` - A boolean value (TRUE or FALSE).
2. `x` - The value to return if `b` is TRUE.
3. `y` - The value to return if `b` is FALSE.

The expression evaluates to `x` if `b` is TRUE, and `y` if `b` is FALSE.
"""

ISZERO  = Lambda(Id("n"),
                 App(
                     App(Id("n"),
                         Lambda(Id("x"), FALSE)
                         ),
                     TRUE
                 )
                 )
"""
The `ISZERO` lambda expression checks if a given Church numeral is zero.

It is defined as: `\\n. (n (\\x. FALSE) TRUE)`

Explanation:
- `n` is the Church numeral to check.
- The Church numeral `n` is applied to the function `\\x. FALSE`.
- If `n` is zero, it does not apply the function and directly returns `TRUE`.
- If `n` is greater than zero, it applies the function at least once, resulting in `FALSE`.

Returns:
- `TRUE` if the Church numeral is zero.
- `FALSE` otherwise.
"""

SUCC    = Lambda(Id('n'),
                 Lambda(Id('f'),
                        Lambda(Id('x'),
                               App(Id('f'), App(App(Id('n'), Id('f')), Id('x')))
                               )
                        )
                 )
"""
The `SUCC` lambda expression represents the successor function in lambda calculus.
It is defined as: `\\n f x. (f ((n f) x))`

It takes a Church numeral `n` and returns the Church numeral representing `n + 1`.
- `f` is the function to apply.
- `x` is the initial value.
"""

PRED    = Lambda(Id("n"),
                 Lambda(Id("f"),
                        Lambda(Id("x"),
                               App(
                                   App(
                                       App(Id("n"),
                                           Lambda(Id("g"),
                                                  Lambda(Id("h"),
                                                         App(Id("h"), App(Id("g"), Id("f")))
                                                         )
                                                  )
                                           ),
                                       Lambda(Id("u"), Id("x"))
                                   ),
                                   Lambda(Id("u"), Id("u"))
                               )
                               )
                        )
                 )
"""
The `PRED` lambda expression represents the predecessor function in lambda calculus.
It is defined as: `\\n f x. (n (\\g h. (h (g f))) (\\u. x) (\\u. u))`

Explanation:
- `n` is the Church numeral whose predecessor is to be computed.
- `f` is the function to apply.
- `x` is the initial value.
- The function works by constructing a pair of values and returning the first value, effectively decrementing the numeral.

Steps:
1. `n` is applied to the function `\\g h. (h (g f))`, which builds a pair of values.
2. The second argument `\\u. x` initializes the pair with `x`.
3. The third argument `\\u. u` ensures the correct structure for the pair.

Returns:
- The Church numeral representing `n - 1`.
- If `n` is 0, the result is the Church numeral for 0 (no negative numbers in Church numerals).
"""

ADD     = Lambda(Id('m'),
                 Lambda(Id('n'),
                        Lambda(Id('f'),
                               Lambda(Id('x'),
                                      App(App(Id('m'), Id('f')), App(App(Id('n'), Id('f')), Id('x')))
                                      )
                               )
                        )
                 )
"""
The `ADD` lambda expression represents addition of two Church numerals in lambda calculus.
It is defined as: `\\m n f x. ((m f) ((n f) x))`

It takes two Church numerals `m` and `n` and returns their sum as a Church numeral.
- `f` is the function to apply.
- `x` is the initial value.
"""

SUB     = Lambda(Id("m"),
                 Lambda(Id("n"),
                        App(App(Id("n"), PRED), Id("m"))
                        )
                 )
"""
The `SUB` lambda expression represents subtraction of two Church numerals in lambda calculus.
It is defined as: `\\m n. ((n PRED) m)`

Explanation:
- `m` is the minuend (the number from which another number is subtracted).
- `n` is the subtrahend (the number to subtract).
- `PRED` is the predecessor function, which decrements a Church numeral by 1.

The expression applies the predecessor function `n` times to `m`, effectively computing `m - n`.

Returns:
- The Church numeral representing the result of `m - n`.
- If `n > m`, the result is the Church numeral for 0 (no negative numbers in Church numerals).
"""

MULT    = Lambda(Id('m'),
                 Lambda(Id('n'),
                        Lambda(Id('f'),
                               App(Id('m'), App(Id('n'), Id('f')))
                               )
                        )
                 )
"""
The `MULT` lambda expression represents multiplication of two Church numerals in lambda calculus.
It is defined as: `\\m n f. (m (n f))`

It takes two Church numerals `m` and `n` and returns their product as a Church numeral.
- `f` is the function to apply.
"""

LEQ     = Lambda(Id("m"),
                 Lambda(Id("n"),
                        App(
                            ISZERO,
                            App(App(SUB, Id("m")), Id("n"))
                        )
                        )
                 )
"""
The `LEQ` lambda expression represents the "less than or equal to" comparison for Church numerals in lambda calculus.
It is defined as: `\\m n. ISZERO ((SUB m) n)`

Explanation:
- `m` and `n` are Church numerals to compare.
- `SUB` computes the subtraction `m - n`.
- `ISZERO` checks if the result of `m - n` is zero.

Returns:
- `TRUE` if `m` is less than or equal to `n`.
- `FALSE` otherwise.
"""

Y       = Lambda(Id('f'),
                 App(
                     Lambda(Id('x'),
                            App(Id('f'), App(Id('x'), Id('x')))
                            ),
                     Lambda(Id('x'),
                            App(Id('f'), App(Id('x'), Id('x')))
                            )
                 )
                 )
"""
The `Y` lambda expression represents the Y-combinator (fixed-point combinator) in lambda calculus.
It is defined as: `\\f. ((\\x. (f (x x))) (\\x. (f (x x))))`

The Y-combinator allows for the definition of recursive functions in lambda calculus.
- `f` is the function to which the fixed-point combinator is applied.
"""

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
        case Id(_):
            return set()

        case Int(_):
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
        case Id(_):
            return False

        case Int(_):
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
    """
    Check if a name is free var in a given context.
    Args:
        name    (Id):           The name to check.
        context (LambdaExpr):   The context in which to check for the name.

    Returns:
        bool: `True` if the name is free in the context, `False` otherwise.

    """
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

# Alpha reductions
def alpha_rename(e: LambdaExpr, old: Id, new: Id) -> LambdaExpr:
    """
    Perform alpha-renaming on a lambda expression.

    Args:
        e   (LambdaExpr):   The lambda expression to be renamed.
        old (Id):           The old name to be replaced.
        new (Id):           The new name to replace the old name.

    Returns:
        LambdaExpr: The lambda expression after alpha-renaming.

    Raises:
        NotImplementedError: If the expression type is not supported.

    """

    match e:
        case Id(_):
            if e == old:
                return new
            return e

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

def alpha_reduction(e1: LambdaExpr, e2: LambdaExpr) -> LambdaExpr:
    shared: set[Id] = get_bound(e1).intersection(get_bound(e2))

    for name in shared:
        new_name: Id = get_free_name(e1, e2, base_name=name)
        e2 = alpha_rename(e=e2, old=name, new=new_name)

    return e2

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
            e1_renamed: Lambda = alpha_rename(e1, old=var1, new=new_var)
            e2_renamed: Lambda = alpha_rename(e2, old=var2, new=new_var)

            return alpha_equivalent(e1_renamed.body, e2_renamed.body)

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

# Beta reductions
def beta_reduction(func: Lambda, arg: LambdaExpr)-> LambdaExpr:
    """
    Perform beta-reduction on a lambda expression.
    Args:
        func    (Lambda):       The lambda expression to be reduced.
        arg     (LambdaExpr):   The argument to be applied to the lambda expression.

    Returns:
        LambdaExpr: The lambda expression after beta-reduction.

    Raises:
        NotImplementedError: If the expression type is not supported.

    """
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
                if e == old:
                    return new
                return e

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
                           replace(new_body, old, new),
                           replace(body, decl, new))

            case _:
                raise NotImplementedError(f"Unsupported expression type: {type(e)}")

    return replace(func.body, old=func.var, new=arg)

# Eta reductions
def is_eta_redex(e: LambdaExpr) -> bool:

    return (isinstance(e, Lambda)       and
            isinstance(e.body, App)     and
            isinstance(e.body.arg, Id)  and
            not isinstance(e.body.func, Id) and
            e.body.arg == e.var         and
            e.var not in get_free(e.body.func))

def eta_reduction(e: LambdaExpr) -> LambdaExpr:

    match e:
        case Id(_):
            return e

        case Int(_):
            return e

        case Lambda(var, body):
            new_body = alpha_rename(body, old=var, new=var)

            if is_eta_redex(Lambda(var, new_body)):
                return new_body.func

            return Lambda(var, new_body)

        case App(func, arg):
            return App(eta_reduction(func),
                       eta_reduction(arg))

        case Let(decl, defn, body):
            return Let(decl,
                       eta_reduction(defn),
                       eta_reduction(body))

        case _:
            raise NotImplementedError(f"Unsupported expression type: {type(e)}")

# Other reductions
def normal_order_reduction(e: LambdaExpr) -> LambdaExpr:
    """
    Perform normal-order reduction on a lambda expression.

    Args:
        e (LambdaExpr):   The lambda expression to be reduced.

    Returns:
        LambdaExpr: The lambda expression after normal-order reduction.

    Raises:
        NotImplementedError: If the expression type is not supported.

    """

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
            # Check if the body is a redex
            # if isinstance(body, App):
            #     if isinstance(body.func, Lambda):
            #         return beta_reduction(body.func, body.arg)
            #     else:
            #         return App(Lambda(var, normal_order_reduction(body)), body.arg)
            # else:
            #     return Lambda(var, normal_order_reduction(body))
            reduced_body = normal_order_reduction(body)
            if alpha_equivalent(reduced_body, body):
                return e
            return Lambda(var, reduced_body)

        case App(func, arg):
            # Check if the function is a lambda
            if isinstance(func, Lambda):
                # Perform beta-reduction
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
        reduced = eta_reduction(reduced)
        if alpha_equivalent(reduced, result):
            return reduced
        result = reduced
        fuel -= 1

    print("Hello: " + pretty(result))
    raise RecursionError("Maximum recursion depth exceeded")

def int_to_church(n: int) -> LambdaExpr:

    f: Id = Id('f')
    x: Id = Id('x')
    body = x

    while n > 0:
        n -= 1
        body = App(f, body) # Get the successor - (f body)

    return Lambda(f, Lambda(x, body))  # \\ f. \\ x. (body)

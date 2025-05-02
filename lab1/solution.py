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

    if isinstance(context, Id):
        return set()
    elif isinstance(context, Int):
        return set()
    elif isinstance(context, Lambda):
        return ({context.var}
                | get_bound(context.body))
    elif isinstance(context, App):
        return (get_bound(context.func)
                | get_bound(context.arg))
    elif isinstance(context, Let):
        return ({context.decl}
                | get_bound(context.defn)
                | get_bound(context.body))
    else:
        raise NotImplementedError(f"Unsupported expression type: {type(context)}")

def get_free(e: LambdaExpr) -> set[Id]:
    if isinstance(e, Id):
        return {e}

    elif isinstance(e, Int):
        return set()

    elif isinstance(e, Lambda):
        return get_free(e.body) - {e.var}

    elif isinstance(e, App):
        return get_free(e.func) | get_free(e.arg)

    elif isinstance(e, Let):
        return get_free(e.defn) | (get_free(e.body) - {e.decl})

    else:
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

    if isinstance(context, Id):
        return False

    elif isinstance(context, Int):
        return False

    elif isinstance(context, Lambda):
        return (context.var == name
                or is_name_bound(name, context.body))

    elif isinstance(context, App):
        return (is_name_bound(name, context.func)
                or is_name_bound(name, context.arg))

    elif isinstance(context, Let):
        return (context.decl == name
                or is_name_bound(name, context.defn)
                or is_name_bound(name, context.body))

    else:
        raise NotImplementedError(f"Unsupported expression type: {type(context)}")

def is_name_free(name: Id, context: LambdaExpr) -> bool:
    """
    Check if a name is free in a given context.
    Args:
        name    (Id):           The name to check.
        context (LambdaExpr):   The context in which to check for the name.

    Returns:
        bool: `True` if the name is free in the context, `False` otherwise.

    Notes:
        - This function is the opposite of is_name_bound.

    """
    return not is_name_bound(name, context)

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

    if isinstance(e, Id):
        if e == old:
            return new
        return e

    if isinstance(e, Int):
        return e

    if isinstance(e, Let):
        if e.decl == old:             # Allow hiding!
            return Let(e.decl,
                       alpha_rename(e.defn, old, new),
                       e.body)

        return Let(e.decl,
                   alpha_rename(e.defn, old, new),
                   alpha_rename(e.body, old, new))

    if isinstance(e, Lambda):
        if e.var == old:              # Allow hiding!
            return e

        return Lambda(e.var,
                      alpha_rename(e.body, old, new))

    if isinstance(e, App):
        return App(alpha_rename(e.func, old, new),
                   alpha_rename(e.arg, old, new))

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
    if isinstance(e1, Id) and isinstance(e2, Id):
        return e1 == e2 # Should've been renamed to match

    elif isinstance(e1, Int) and isinstance(e2, Int):
        return e1.n == e2.n

    elif isinstance(e1, Lambda) and isinstance(e2, Lambda):
        if e1.var == e2.var:
            return alpha_equivalent(e1.body, e2.body)

        new_var = get_free_name(e1, e2, base_name=e1.var)
        e1_renamed = alpha_rename(e1, e1.var, new_var)
        e2_renamed = alpha_rename(e2, e2.var, new_var)

        return alpha_equivalent(e1_renamed.body, e2_renamed.body)

    elif isinstance(e1, App) and isinstance(e2, App):
        return (alpha_equivalent(e1.func, e2.func) and
                alpha_equivalent(e1.arg, e2.arg))

    elif isinstance(e1, Let) and isinstance(e2, Let):
        if e1.decl == e2.decl:
            return (alpha_equivalent(e1.defn, e2.defn) and
                    alpha_equivalent(e1.body, e2.body))

        new_var = get_free_name(e1, e2, base_name=e1.decl)
        e1_renamed: Let = alpha_rename(e1, e1.decl, new_var)
        e2_renamed: Let = alpha_rename(e2, e2.decl, new_var)

        return (alpha_equivalent(e1_renamed.defn, e2_renamed.defn) and
                alpha_equivalent(e1_renamed.body, e2_renamed.body))

    else:
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

        if isinstance(e, Id):
            if e == old:
                return new
            return e

        elif isinstance(e, Int):
            return e

        elif isinstance(e, Lambda):
            if e.var == old:              # Allow hiding!
                return e

            # We need to check if any free variables in 'new' would be captured by e.var
            # No need to rename if e.var doesn't occur in new (it can't capture anything)
            if e.var not in get_free(new):
                return Lambda(e.var,
                              replace(e.body, old, new))

            # Rename the bound variable to avoid variable capture
            new_var = get_free_name(e.body, new, bound_names={old}, base_name=e.var)
            new_body = alpha_rename(e.body, old=e.var, new=new_var)
            return Lambda(new_var,
                          replace(new_body, old, new))

        elif isinstance(e, App):
            return App(replace(e.func, old, new),
                       replace(e.arg, old, new))

        elif isinstance(e, Let):
            if e.decl == old:       # Allow hiding!
                return Let(e.decl,
                           replace(e.defn, old, new),
                           e.body)

            if e.decl not in get_free(new):
                return Let(e.decl,
                           replace(e.defn, old, new),
                           replace(e.body, old, new))

            new_decl = get_free_name(e.defn, e.body, new, bound_names={old}, base_name=e.decl)
            new_body = alpha_rename(e.body, old=e.decl, new=new_decl)
            return Let(new_decl,
                       replace(e.defn, old, new),
                       replace(new_body, old, new))

        else:
            raise NotImplementedError(f"Unsupported expression type: {type(e)}")

    return replace(func.body, old=func.var, new=arg)

# Eta reductions
def is_eta_redex(e: LambdaExpr) -> bool:

    return (isinstance(e, Lambda)       and
            isinstance(e.body, App)     and
            isinstance(e.body.arg, Id)  and
            e.body.arg == e.var         and
            e.var not in get_free(e.body.func))

def eta_reduction(e: LambdaExpr) -> LambdaExpr:
    if isinstance(e, Id):
        return e

    if isinstance(e, Int):
        return e

    if isinstance(e, Lambda):
        new_body = eta_reduction(e.body)

        if is_eta_redex(Lambda(e.var, new_body)):
            return new_body.func

        return Lambda(e.var, new_body)

    if isinstance(e, App):
        return App(eta_reduction(e.func),
                   eta_reduction(e.arg))

    if isinstance(e, Let):
        return Let(e.decl,
                   eta_reduction(e.defn),
                   eta_reduction(e.body))

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

    if isinstance(e, Id):
        return e

    if isinstance(e, Int):
        return int_to_church(e.n)

    if isinstance(e, Let):
        # Transform "let" statmenet to "(\lambda defl. body) defn"
        e_lambda: Lambda = Lambda(e.decl, e.body)
        return normal_order_reduction(App(e_lambda, e.defn))
        # TODO: Review this transformation, check for problems

    if isinstance(e, Lambda):
        return Lambda(e.var, normal_order_reduction(e.body))

    if isinstance(e, App):
        if isinstance(e.func, Lambda):
            return beta_reduction(e.func, e.arg)

        func_reduced = normal_order_reduction(e.func)

        # Try to use normal order reduction to reduce e
        if not alpha_equivalent(func_reduced, e.func):
            return App(func_reduced, e.arg)

        # If reduction fail - go after the arg
        arg_reduced = normal_order_reduction(e.arg)

        if not alpha_equivalent(arg_reduced, e.arg):
            return App(e.func, arg_reduced)

        return e

    raise NotImplementedError(f"Unsupported expression type: {type(e)}")

def interpret(e: LambdaExpr, fuel: int = 100_000) -> LambdaExpr:
    """Keep performing normal-order reduction steps until you reach normal form, detect divergence or run out of fuel."""

    result = e

    while fuel > 0:
        reduced = normal_order_reduction(result)

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

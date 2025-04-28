from syntax.lambda_pure import *


def alpha_equivalent(e1: LambdaExpr, e2: LambdaExpr) -> bool:
    """Check if two lambda expressions differ only in the names of their bound variables."""
    # """Preforming a series of alpha-conversions (renaming)"""
    if isinstance(e1, Id) and isinstance(e2, Id):
        return e1.name == e2.name # Should've been renamed to match

    elif isinstance(e1, Int) and isinstance(e2, Int):
        return e1.n == e2.n

    elif isinstance(e1, Lambda) and isinstance(e2, Lambda):
        if e1.var.name == e2.var.name:
            return alpha_equivalent(e1.body, e2.body)

        new_var = get_free_name(e1, e2, base_name=e1.var)
        e1_renamed = alpha_rename(e1, e1.var, new_var)
        e2_renamed = alpha_rename(e2, e2.var, new_var)

        return alpha_equivalent(e1_renamed.body, e2_renamed.body)

    elif isinstance(e1, App) and isinstance(e2, App):
        return (alpha_equivalent(e1.func, e2.func) and
                alpha_equivalent(e1.arg, e2.arg))

    elif isinstance(e1, Let) and isinstance(e2, Let):
        if e1.decl.name == e2.decl.name:
            return (alpha_equivalent(e1.defn, e2.defn) and
                    alpha_equivalent(e1.body, e2.body))

        new_var = get_free_name(e1, e2, base_name=e1.decl)
        e1_renamed: Let = alpha_rename(e1, e1.decl, new_var)
        e2_renamed: Let = alpha_rename(e2, e2.decl, new_var)

        return (alpha_equivalent(e1_renamed.defn, e2_renamed.defn) and
                alpha_equivalent(e1_renamed.body, e2_renamed.body))

    else:
        return False


def interpret(e: LambdaExpr, fuel: int = 100_000) -> LambdaExpr:
    """Keep performing normal-order reduction steps until you reach normal form, detect divergence or run out of fuel."""

    if fuel <= 0:
        raise RecursionError("Maximum recursion depth exceeded")

    if isinstance(e, Id):
        return e
    elif isinstance(e, App) or isinstance(e, Lambda) or isinstance(e, Let):
        reduced: LambdaExpr = normal_order_reduction(e)

        if alpha_equivalent(reduced, e):
            return reduced

        return interpret(reduced, fuel - 1)
    else:
        return e


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
            if e.name == old.name:
                return new
            if is_name_bound(e, context=new):
                return get_free_name(new, bound_names={old}, base_name=e)
            return e

        elif isinstance(e, Int):
            return e

        elif isinstance(e, Lambda):
            # Allow hiding!
            if e.var.name == old.name:
                return Lambda(e.var, e.body)

            # If the variable is bound in this context, rename it
            if is_name_bound(e.var, context=new):
                new_var = get_free_name(e, old)
                e_renamed = alpha_rename(e, e.var, new_var)
                return Lambda(e_renamed.var,
                              replace(e_renamed.body, old, new))

            return Lambda(e.var,
                          replace(e.body, old, new))

        elif isinstance(e, App):
            return App(replace(e.func, old, new),
                       replace(e.arg, old, new))

        elif isinstance(e, Let):
            if e.decl.name == old.name:
                raise NotImplementedError("Idk how to handle that")
                # TODO: Handle this case

            if is_name_bound(e.decl, context=new):
                new_decl = get_free_name(e, old)
                e_renamed = alpha_rename(e, e.decl, new_decl)
                return Let(e_renamed.decl,
                           replace(e_renamed.defn, old, new),
                           replace(e_renamed.body, old, new))

            return Let(e.decl,
                       replace(e.defn, old, new),
                       replace(e.body, old, new))

        else:
            raise NotImplementedError(f"Unsupported expression type: {type(e)}")

    return replace(func.body, old=func.var, new=arg)


def get_bound_names(context: LambdaExpr) -> set[Id]:
    """
    Get the names of all bound variables in a lambda expression.

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
        return ({context.var.name}
                | get_bound_names(context.body))
    elif isinstance(context, App):
        return (get_bound_names(context.func)
                | get_bound_names(context.arg))
    elif isinstance(context, Let):
        return ({context.decl.name}
                | get_bound_names(context.defn)
                | get_bound_names(context.body))
    else:
        raise NotImplementedError(f"Unsupported expression type: {type(context)}")

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
        return (context.var.name == name.name
                or is_name_bound(name, context.body))

    elif isinstance(context, App):
        return (is_name_bound(name, context.func)
                or is_name_bound(name, context.arg))

    elif isinstance(context, Let):
        return (context.decl.name == name.name
                or is_name_bound(name, context.defn)
                or is_name_bound(name, context.body))

    else:
        raise NotImplementedError(f"Unsupported expression type: {type(context)}")

    # return name in get_bound_names(e)

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
                  base_name: Id = Id("z"),
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
            new_name: Id = Id(f"{base_name.name}")
        else:
            new_name: Id = Id(f"{base_name.name}{counter}")

        is_free: bool = new_name not in bound_names

        if is_free:
            for expr in args:
                if is_name_bound(new_name, expr):
                    is_free = False
                    break

            if is_free:
                return new_name

        counter += 1

    raise RecursionError(f"Maximum recursion depth {safety_limit} exceeded")

def alpha_reduction(e1: LambdaExpr, e2: LambdaExpr) -> LambdaExpr:
    """
    Perform alpha-reduction on the second expression to match the first expression.

    Args:
        e1 (LambdaExpr):   The first lambda expression.
        e2 (LambdaExpr):   The second lambda expression to be reduced.

    Returns:
        LambdaExpr: The second expression after alpha-reduction.

    Raises:
        NotImplementedError: If the expression type is not supported.

    """
    bound_names_1: set = get_bound_names(e1)
    bound_names_2: set = get_bound_names(e2)

    shared_names: set = bound_names_1.intersection(bound_names_2)

    for name in shared_names:
        new_name: Id = get_free_name(e1, e2, base_name=name)
        e2 = alpha_rename(e=e2, old=name, new=new_name)

    return e2

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
        if e.name == old.name:
            return new
        return e

    if isinstance(e, Int):
        return e

    if isinstance(e, Let):
        return Let(alpha_rename(e.decl, old, new),
                   alpha_rename(e.defn, old, new),
                   alpha_rename(e.body, old, new))

    if isinstance(e, Lambda):
        return Lambda(alpha_rename(e.var, old, new),
                      alpha_rename(e.body, old, new))

    if isinstance(e, App):
        return App(alpha_rename(e.func, old, new),
                   alpha_rename(e.arg, old, new))

    raise NotImplementedError(f"Unsupported expression type: {type(e)}")

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
        return e

    if isinstance(e, Let):
        # Transform "let" statmenet to "(\lambda defl. body) defn"
        e_lambda: Lambda = Lambda(e.decl, e.body)
        return normal_order_reduction(App(e_lambda, e.defn))
        # TODO: Review this transformation, check for problems

    if isinstance(e, Lambda):
        return Lambda(e.var, normal_order_reduction(e.body))

    if isinstance(e, App):
        if isinstance(e.func, Lambda):
            print(pretty(beta_reduction(e.func, e.arg)))
            return beta_reduction(e.func, e.arg)

        func_reduced = normal_order_reduction(e.func)

        # Try to use normal order reduction to reduce e
        if not alpha_equivalent(func_reduced, e.func):
            print(pretty(App(func_reduced, e.arg)))
            return App(func_reduced, e.arg)

        # If reduction fail - go after the arg
        arg_reduced = normal_order_reduction(e.arg)

        if not alpha_equivalent(arg_reduced, e.arg):
            print(pretty(App(e.func, arg_reduced)))
            return App(e.func, arg_reduced)

        print(pretty(e))
        return e

    raise NotImplementedError(f"Unsupported expression type: {type(e)}")

    # if isinstance(e, App):
    #     # If the function is a lambda abstraction, perform beta reduction
    #     if isinstance(e.func, Lambda):
    #         return beta_reduction(e.func, e.arg)
    #     # Otherwise, reduce the function part
    #     return App(normal_order_reduction(e.func), e.arg)
    # elif isinstance(e, Lambda):
    #     # If the body is an application, reduce the body
    #     return Lambda(e.var, normal_order_reduction(e.body))
    # elif isinstance(e, Let):
    #     # Reduce the definition first
    #     return Let(e.decl, normal_order_reduction(e.defn), e.body)
    # elif isinstance(e, Id):
    #     return Id(e.name)
    # else:
    #     raise NotImplementedError(f"Unsupported expression type: {type(e)}")

def int_to_church(x: int) -> LambdaExpr:
    """
    Convert an integer to its Church numeral representation.

    Args:
        x (int): The integer to be converted.

    Returns:
        LambdaExpr: The Church numeral representation of the integer.

    """

    f: Id = Id('f')
    x: Id = Id('x')
    body = x

    while x > 0:
        x -= 1
        body = App(f, body) # Get the successor - (f body)

    return Lambda(f, Lambda(x, body))  # \\ f. \\ x. (body)

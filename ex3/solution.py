import typing
import operator

import z3

from syntax.while_lang import (
    parse,
    Id,
    Expr,
    Int,
    BinOp,
    Skip,
    Assign,
    Seq,
    If,
    While,
    Stmt, pretty,
)


type Formula = z3.Ast | bool
type PVar = str
type Env = dict[PVar, Formula]
type Invariant = typing.Callable[[Env], Formula]

TRIVIAL: typing.Final = lambda _: True


OP = {
    "+": operator.add,
    "-": operator.sub,
    "*": operator.mul,
    "/": lambda a,b: a / b,
    "!=": operator.ne,
    ">": operator.gt,
    "<": operator.lt,
    "<=": operator.le,
    ">=": operator.ge,
    "=": operator.eq,
}


def mk_env(pvars: set[PVar]) -> Env:
    return {v: z3.Int(v) for v in pvars}


def upd(d: Env, k: PVar, v: Formula) -> Env:
    d = d.copy()
    d[k] = v
    return d


def collect_modified_vars(stmt: Stmt) -> set[PVar]:
    """Finds all variables that are assigned to within a statement."""
    modified = set()

    def collect_modified(s: Stmt):
        match s:
            case Assign(var, _):
                modified.add(var.name)
            case Seq(first, second):
                collect_modified(first)
                collect_modified(second)
            case If(_, then_branch, else_branch):
                collect_modified(then_branch)
                collect_modified(else_branch)
            case While(_, body):
                collect_modified(body)
            case _:
                pass

    collect_modified(stmt)
    return modified


def isolate_loop(stmt: Stmt) -> tuple[Stmt | None, Stmt | None]:
    """
    Isolates the loop from the beginning of the program.
    """
    match stmt:
        case While(_, _):
            return None, stmt
        case Seq(first, second):
            prologue, maybe_loop = isolate_loop(second)
            if maybe_loop is None:
                return stmt, None
            if prologue is None:
                return first, maybe_loop
            return Seq(first, prologue), maybe_loop  # Prologue found, continue with second part
        case Skip():
            return None, None  # No prologue, no loop
        case Assign(var, expr):
            return Assign(var, expr), None  # Prologue with a single assignment
        case _:
            return stmt, None



def eval_expr(expr: Expr, env: Env) -> Formula:
    match expr:
        case Id(name):
            return env[name]
        case Int(value):
            return z3.IntVal(value)
        case BinOp(op, left, right):
            # Using our fixed 'eval_expr' logic here
            eval_l = eval_expr(left, env)
            eval_r = eval_expr(right, env)
            return OP[op](eval_l, eval_r)
    raise Exception(f"Unexpected expression: {expr} of type {type(expr)}")


def get_prologue_state(prologue: Stmt, env: Env) -> Env:
    """Symbolically executes the prologue to find the state of variables."""

    # This is a simplified version of `eval_expr` and `wp` for forward execution.
    def eval_in_env(expr: Expr, current_env: Env) -> Formula:
        try:
            return eval_expr(expr, current_env)
        except Exception:
            raise Exception(f'Unsupported expression in prologue {expr} of type {type(expr)}')

    def execute(s: Stmt, current_env: Env) -> Env:
        match s:
            case Assign(var, expr):
                val = eval_in_env(expr, current_env)
                return upd(current_env, var.name, val)
            case Seq(first, second):
                env_after_first = execute(first, current_env)
                return execute(second, env_after_first)
            case Skip():
                return current_env
            case _:
                # Only a simple prologue is expected, does not support complex statements
                raise Exception(f"Unsupported statement in prologue for strengthening {s} of type {type(s)}")

    if prologue is None:
        return env
    return execute(prologue, env)

def find_solution(
    P: Invariant, stmt: Stmt, Q: Invariant, linv: Invariant = lambda _: True, strong_linv_flag: bool = False
) -> z3.Solver:
    """
    Try to find proof for Hoare triple {P} c {Q}
    Where P, Q are assertions, and stmt is the modern AST.
    Returns a z3.Solver object, ready to be checked.
    """

    def weakest_precondition(stmt: Stmt, Q: Invariant) -> Invariant:
        match stmt:
            case Skip():
                return Q
            case Assign(var, expr):

                def reQ(env: Env) -> Formula:
                    evale = eval_expr(expr, env)
                    new_env = upd(env, var.name, evale)
                    return Q(new_env)

                return reQ

            case Seq(first, second):
                # return weakest_precondition(first, weakest_precondition(second, Q))
                precondition_from_second = weakest_precondition(second, Q)
                precondition_from_first = weakest_precondition(first, precondition_from_second)
                return precondition_from_first

            case If(cond, then_branch, else_branch):

                wp_then = weakest_precondition(then_branch, Q)
                wp_else = weakest_precondition(else_branch, Q)

                def reQ(env: Env) -> Formula:
                    cond_formula = eval_expr(cond, env)

                    precondition_then = z3.Implies(cond_formula, wp_then(env))
                    precondition_else = z3.Implies(z3.Not(cond_formula), wp_else(env))

                    return z3.And(precondition_then, precondition_else)

                return reQ

            case While(cond, body):
                return linv # Weakest precondition is the loop invariant

        raise Exception(f"Unexpected statement: {stmt} of type {type(stmt)}")

    # Collect all program variables
    pvars = set()

    def collect_vars_from_expr(expr: Expr) -> None:
        match expr:
            case Id(name):
                pvars.add(name)
            case Int(_):
                pass
            case BinOp(op, left, right):
                collect_vars_from_expr(left)
                collect_vars_from_expr(right)

    def collect_vars(stmt: Stmt) -> None:
        match stmt:
            case Skip():
                pass
            case Assign(var, expr):
                collect_vars_from_expr(var)
                collect_vars_from_expr(expr)
            case Seq(first, second):
                collect_vars(first)
                collect_vars(second)
            case If(cond, then_branch, else_branch):
                collect_vars_from_expr(cond)
                collect_vars(then_branch)
                collect_vars(else_branch)
            case While(cond, body):
                collect_vars_from_expr(cond)
                collect_vars(body)
    collect_vars(stmt)

    # Create env
    env = mk_env(pvars)

    constraints = []

    prologue, loop = isolate_loop(stmt)

    strong_linv = linv
    if loop is not None and strong_linv_flag:
        all_vars = pvars
        mod_vars = collect_modified_vars(loop)
        const_vars = all_vars - mod_vars

        prologue_state = get_prologue_state(prologue, env)

        const_costraints = []
        for var in const_vars:
            const_costraints.append(operator.eq(prologue_state[var], env[var]))

        def slinv(e: Env) -> Formula:
            return z3.And(linv(e), *const_costraints)
        print("Loop invariant with constant constraints:")
        print(const_costraints)
        strong_linv = slinv


    # Precondition `P` implies weakest precondition
    wp_main = weakest_precondition(stmt, Q)
    constraint = z3.Implies(P(env), wp_main(env))
    constraints.append(constraint)

    # constraint for the loop invariant
    def collect_loop_constraints(stmt: Stmt, Q: Invariant) -> None:
        match stmt:
            case While(cond, body):
                # Body preserves loop invariant ; [ linv /\ cond --> wp(body) ]
                wp_body = weakest_precondition(body, strong_linv)
                eval_cond = eval_expr(cond, env)
                preservation = z3.Implies(
                    z3.And(strong_linv(env), eval_cond),
                    wp_body(env)
                )
                constraints.append(preservation)

                # End loop case ; [ linv /\ ~cond --> Q ]
                exit_cond = z3.Implies(
                    z3.And(strong_linv(env), z3.Not(eval_cond)),
                    Q(env)
                )
                constraints.append(exit_cond)

                # No need to recusively collect, as there is only one loop in the program

            case Seq(first, second):
                wp_second = weakest_precondition(second, Q)
                collect_loop_constraints(first, wp_second)
                collect_loop_constraints(second, Q)
            case If(_, then_branch, else_branch):
                collect_loop_constraints(then_branch, Q)
                collect_loop_constraints(else_branch, Q)
            case _:
                pass

    collect_loop_constraints(stmt, Q)

    solver = z3.Solver()
    solver.add(z3.Or([z3.Not(c) for c in constraints]))

    print("Constraints:")
    for c in constraints:
        print(c)

    return solver


def verify(P: Invariant, stmt: Stmt, Q: Invariant, linv: Invariant = TRIVIAL) -> bool:
    """
    Verifies a Hoare triple {P} c {Q}
    Where P, Q are assertions, and stmt is the modern AST.
    Returns True if the triple is valid.
    """
    print(pretty(stmt))
    solver = find_solution(P, stmt, Q, linv)
    if solver.check() == z3.sat:
        print("Counterexample found:")
        print(solver.model())
    else:
        print("No counterexample found. The Hoare triple is valid.")
    return solver.check() == z3.unsat


def main() -> None:
    # example program
    program = "a := b ; while i < n do ( a := a + 1 ; b := b + 1 )"
    P = TRIVIAL
    Q = lambda d: d["a"] == d["b"]
    linv = lambda d: d["a"] == d["b"]

    ast = parse(program)
    # Your task is to implement "verify"
    solver = find_solution(P, ast, Q, linv=linv)
    if solver.check() == z3.sat:
        print("Counterexample found:")
        print(solver.model())
    else:
        print("No counterexample found. The Hoare triple is valid.")


if __name__ == "__main__":
    main()

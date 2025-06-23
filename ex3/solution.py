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
    Stmt,
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
    "/": operator.floordiv,
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


def find_solution(
    P: Invariant, stmt: Stmt, Q: Invariant, linv: Invariant = lambda _: True
) -> z3.Solver:
    """
    Try to find proof for Hoare triple {P} c {Q}
    Where P, Q are assertions, and stmt is the modern AST.
    Returns a z3.Solver object, ready to be checked.
    """

    def eval_expr(expr: Expr, env: Env) -> Formula:
        match expr:
            case Id(name):
                return env[name]
            case Int(value):
                return z3.IntVal(value)
            case BinOp(left, op, right):
                evall = eval_expr(left, env)
                evalr = eval_expr(right, env)
                return OP[op](evall, evalr)
        raise Exception(f"Unexpected expression: {expr}")

    def weakest_precondition(stmt: Stmt, Q: Invariant) -> Invariant:
        match stmt:
            case Skip():
                return Q
            case Assign(var, expr):

                def reQ(env: Env) -> Formula:
                    evale = eval_expr(expr, env)
                    new_env = upd(env, var, evale)
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
                return linv

        return

    return z3.Solver()


def verify(P: Invariant, stmt: Stmt, Q: Invariant, linv: Invariant = TRIVIAL) -> bool:
    """
    Verifies a Hoare triple {P} c {Q}
    Where P, Q are assertions, and stmt is the modern AST.
    Returns True if the triple is valid.
    """
    solver = find_solution(P, stmt, Q, linv)
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

import pytest

from syntax.lambda_pure import parse, pretty

import solution


@pytest.mark.parametrize(
    "program, expected",
    [
        # Multiple applications
        pytest.param(r"((\x. \y. x y) a) b", "(a b)", id="nested_application"),
        pytest.param(r"(\x. \y. \z. x z (y z)) a b c", "(a c) (b c)", id="s_combinator_application"),

        # Nested let expressions
        pytest.param(r"let x = a in let y = b in x", "a", id="nested_let_first"),
        pytest.param(r"let x = a in let y = b in y", "b", id="nested_let_second"),
        pytest.param(r"let x = a in let x = b in x", "b", id="let_shadowing"),

        # More complex shadowing
        pytest.param(r"(\x. (\x. \y. x)) a b", r"\y. b", id="complex_shadowing"),
        pytest.param(r"let x = a in (\x. x) b", "b", id="let_lambda_shadowing"),

        # Church booleans
        pytest.param(r"(\p. \q. p q p) (\t. \f. t) (\t. \f. t)", r"\t. \f. t", id="church_and_true_true"),
        pytest.param(r"(\p. \q. p q p) (\t. \f. f) (\t. \f. t)", r"\t. \f. f", id="church_and_false_true"),

        # Y combinator application (terminating case)
        pytest.param(
            r"(\f. (\x. f (\y. x x y)) (\x. f (\y. x x y))) (\f. \n. (\c. c (\t. \f. f) (\t. \f. t)) n (\t. \f. t) (f ((\n. \f. \x. n (\g. \h. h (g f)) (\u. x) (\u. u)) n)))",
            r"\n. (\c. c (\t. \f. f) (\t. \f. t)) n (\t. \f. t) ((\f. (\x. f (\y. x x y)) (\x. f (\y. x x y))) (\f. \n. (\c. c (\t. \f. f) (\t. \f. t)) n (\t. \f. t) (f ((\n. \f. \x. n (\g. \h. h (g f)) (\u. x) (\u. u)) n))) ((\n. \f. \x. n (\g. \h. h (g f)) (\u. x) (\u. u)) n))",
            id="y_combinator_factorial"
        ),

        # Interesting reductions
        pytest.param(r"(\x. (\y. y) x) ((\z. z) a)", "a", id="double_application"),
        pytest.param(r"(\x. (\y. x)) ((\z. z z) (\z. z z))", r"\y. (\z. z z) (\z. z z)", id="omega_as_argument"),
        pytest.param(r"(\x. (\y. y)) ((\z. z z) (\z. z z))", r"\y. y", id="discard_omega"),

        # Edge cases for normal order
        pytest.param(r"(\x. \y. y x) ((\z. z z) (\z. z z)) a", "a ((\z. z z) (\z. z z))", id="normal_order_omega"),

        # Eta conversion cases
        pytest.param(r"(\x. (\y. y) x)", r"\x. x", id="eta_reduction_nested"),
        pytest.param(r"(\x. (\y. y x) z)", r"\x. z x", id="eta_with_free_var"),
    ],
)
def test_normal_form_advanced(program: str, expected: str) -> None:
    expr = parse(program)
    print(f"Expected: {expected}")
    print(f"Program: {pretty(solution.interpret(expr))}")
    assert expr is not None, f"Failed to parse: {program}"
    assert solution.interpret(expr) == parse(expected)
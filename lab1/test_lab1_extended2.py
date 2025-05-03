import pytest

from syntax.lambda_pure import parse, pretty

import solution


@pytest.mark.parametrize(
    "program, expected",
    [
        # Advanced Church numerals and arithmetic
        pytest.param(r"(\n.\f.\x.n f (f x)) (\f.\x.f (f x))", r"\f. \x. f (f (f x))", id="church_numeral_successor"),
        pytest.param(r"(\m.\n.\f.\x.m f (n f x)) (\f.\x.f (f x)) (\f.\x.f (f (f x)))", r"\f. \x. f (f (f (f (f x))))", id="church_numeral_addition"),
        pytest.param(r"(\m.\n.\f.m (n f)) (\f.\x.f (f x)) (\f.\x.f (f (f x)))", r"\f. \x. f (f (f (f (f (f x)))))", id="church_numeral_multiplication"),

        # Complex combinators and compositions
        pytest.param(r"((\x.\y.\z.x z (y z)) (\x.\y.x)) (\x.\y.y)", r"\z. z", id="s_k_i_composition"),
        pytest.param(r"((\x.\y.\z.x z (y z)) (\x.\y.\z.x (y z))) (\x.\y.y) a b", "a b", id="s_s_i_application"),
        pytest.param(r"((\x.\y.\z.x z (y z)) (\x.\y.\z.x (y z))) (\x.\y.x) a b", "a a", id="s_s_k_application"),

        # Complex variable capture and shadowing scenarios
        pytest.param(r"(\x. let y = x in (\x. \z. y x)) (\w. w)", r"\x. \z. x", id="shadowing_with_let_lambda"),
        pytest.param(r"(\x. \y. (\x. \y. x) y) a b", r"\y. b", id="triple_nested_shadowing"),
        pytest.param(r"let x = a in let y = x in let x = b in (\z. y z x)", r"\z. a z b", id="let_shadowing_chain"),

        # Church boolean logic with complex operations
        pytest.param(
            r"(\a.\b.\c. a (b c) (a c b)) (\t.\f.t) (\t.\f.f) (\t.\f.t)",
            r"\f. f",
            id="church_boolean_complex_true"
        ),
        pytest.param(
            r"(\p.\q. (\b. b p q) (\t.\f.f)) (\t.\f.t) (\t.\f.f)",
            r"\t. \f. f",
            id="church_boolean_conditional_false"
        ),

        # Lazy evaluation with potential infinite recursion but avoiding it
        pytest.param(
            r"(\x. \y. x) a ((\x. x x) (\x. x x))",
            r"a",
            id="lazy_eval_avoiding_omega"
        ),
        pytest.param(
            r"(\p.\t.\f. p t f) (\t.\f.t) a ((\x. x x) (\x. x x))",
            r"a",
            id="conditional_avoiding_omega"
        ),

        # Eta-reduction with higher-order functions
        pytest.param(
            r"(\f. \x. (\g. g x) (f))",
            r"\f. \x. f x",
            id="eta_higher_order"
        ),
        pytest.param(
            r"(\f. \x. (\g. \y. g y) (f x))",
            r"\f. \x. \y. f x y",
            id="nested_eta_reduction"
        ),
    ],
)
def test_normal_form_harder(program: str, expected: str) -> None:
    expr = parse(program)
    print(f"Input: {program}")
    print(f"Expected: {expected}")
    print(f"Program: {pretty(solution.interpret(expr))}")
    assert expr is not None, f"Failed to parse: {program}"
    assert solution.interpret(expr) == parse(expected)
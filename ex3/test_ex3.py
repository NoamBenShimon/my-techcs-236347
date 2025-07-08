from z3 import And,Or

from syntax.while_lang import parse, pretty

from solution import verify, Env, Formula


def test_0() -> None:
    ast = parse(
        """
        a := b;
        while i < n do (
            a := a + 1;
            b := b + 1
        )
    """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return env["a"] == env["b"]

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return And(env["a"] == env["b"], env["i"] >= env["n"])

    assert verify(P, ast, Q, linv)


def test_1() -> None:
    ast = parse(
        """
        y := 0 ;
        while y < i do (
            x := x + y;
            if (x * y) < 10
                then y := y + 1 
                else skip
        )
    """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["y"] >= 0, env["x"] > 0)

    def P(env: Env) -> Formula:
        return env["x"] > 0

    def Q(env: Env) -> Formula:
        return env["x"] > 0

    assert verify(P, ast, Q, linv)


def test_2() -> None:
    ast = parse(
        """
        while a != b do
            if a > b
                then a := a - b
                else b := b - a
    """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return env["a"] > 0

    def P(env: Env) -> Formula:
        return And(env["a"] > 0, env["b"] > 0)

    def Q(env: Env) -> Formula:
        return And(env["a"] > 0, env["a"] == env["b"])

    assert verify(P, ast, Q, linv)

def test_3() -> None:
    ast = parse(
        """
        x := 1;
        while x < n do
            x := x * 2
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["x"] >= 1)

    def P(env: Env) -> Formula:
        return env["n"] > 1

    def Q(env: Env) -> Formula:
        return env["x"] >= env["n"]

    assert verify(P, ast, Q, linv)

def test_4() -> None:
    ast = parse(
        """
        t := a;
        a := b;
        b := t
        """
    )
    assert ast is not None

    def P(env: Env) -> Formula:
        return True

    def Q_weaker(env: Env) -> Formula:
        return env["b"] == env["t"]

    assert verify(P, ast, Q_weaker)

def test_5() -> None:
    ast = parse(
        """
        while x > 0 do
            x := x - 1
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return env["x"] >= 0

    def P(env: Env) -> Formula:
        return env["x"] >= 0

    def Q(env: Env) -> Formula:
        return env["x"] == 0

    assert verify(P, ast, Q, linv)

def test_6() -> None:
    ast = parse(
        """
        if x > 0
            then x := x
            else x := x
        """
    )
    assert ast is not None

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return True

    assert verify(P, ast, Q)

def test_7() -> None:
    ast = parse(
        """
        x := 0;
        y := 0;
        while x < n do (
            x := x + 1;
            y := y + 2
        )
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["y"] == 2 * env["x"], env["x"] <= env["n"])

    def P(env: Env) -> Formula:
        return env["n"] >= 0

    def Q(env: Env) -> Formula:
        return And(env["x"] == env["n"], env["y"] == 2 * env["n"])

    assert verify(P, ast, Q, linv)

def test_8() -> None:
    ast = parse(
        """
        x := 0;
        while x < 5 do
            x := x + 1
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return env["x"] <= 5

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["x"] == 10

    assert not (verify(P, ast, Q, linv))

def test_9() -> None:
    ast = parse(
        """
        x := 0;
        y := 0;
        while y < 5 do
           ( x := x + 1;
            y := y + 1 )
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["y"] == env["x"], env["y"]<=5)

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["x"] == 5

    assert verify(P, ast, Q, linv)

def test_10() -> None:
    ast = parse(
        """
        x := 1;
        while x < n do
            x := x * 3
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return env["x"] >= 1

    def P(env: Env) -> Formula:
        return env["n"] >= 1

    def Q(env: Env) -> Formula:
        return env["x"] >= env["n"]

    assert verify(P, ast, Q, linv)


def test_11() -> None:
    ast = parse(
        """
        a := 0;
        while a < 10 do
            a := a + 2
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["a"] >= 0, env["a"] % 2 == 0)

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["a"] >= 10

    assert verify(P, ast, Q, linv)


def test_12() -> None:
    ast = parse(
        """
        x := 0;
        if y > 0
            then x := y
            else x := -y
        """
    )
    assert ast is not None

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["x"] >= 0

    assert verify(P, ast, Q)


def test_13() -> None:
    ast = parse(
        """
        x := 0;
        while x < 5 do
            x := x + 1
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return env["x"] <= 5

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["x"] == 5

    assert verify(P, ast, Q, linv)

def test_14() -> None:
    ast = parse(
        """
        x := 1;
        y := 2;
        while x < n do (
            y := y + 2;
            x := x + 1
        )
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["y"] == 2 * env["x"], env["x"] <= env["n"])

    def P(env: Env) -> Formula:
        return env["n"] >= 1

    def Q(env: Env) -> Formula:
        return env["y"] == 2 * env["n"]

    assert verify(P, ast, Q, linv)

def test_15() -> None:
    ast = parse(
        """
        x := 1;
        y := 2;
        while x < n do (
            y := y + 2;
            x := x + 1
        );
        if y < 2*n
            then y:=0
            else y:=1
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["y"] == 2 * env["x"], env["x"] <= env["n"])

    def P(env: Env) -> Formula:
        return env["n"] >= 1

    def Q(env: Env) -> Formula:
        return env["y"] == 1

    assert verify(P, ast, Q, linv)

def test_16() -> None:
    ast = parse(
        """
        x := 1;
        y := 2;
        while x < n do (
            y := y + 2;
            x := x + 1
        );
        if y < 2*n
            then y:=0
            else y:=1
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["y"] == 2 * env["x"], env["x"] <= env["n"])

    def P(env: Env) -> Formula:
        return env["n"] >= 0

    def Q(env: Env) -> Formula:
        return env["y"] == 0

    assert not verify(P, ast, Q, linv)

def test_17() -> None:
    ast = parse(
        """
        y := 10;
        while y > x do
            y := y - 1
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["y"] >= env["x"], env["x"] == 1)

    def P(env: Env) -> Formula:
        return env["x"]==1

    def Q(env: Env) -> Formula:
        return env["y"] == 1

    assert verify(P, ast, Q, linv)

def test_18() -> None:
    ast = parse(
        """
        y := 10;
        x := y-2;
        y := y-x
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return True

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["y"] == 2

    assert verify(P, ast, Q, linv)

def test_19() -> None:
    ast = parse(
        """
        y := 10;
        x := y-2;
        y := y-y
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return True

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["y"] == 2

    assert not verify(P, ast, Q, linv)

def test_20() -> None:
    ast = parse(
        """
        if x >= 1
            then x := x / 2
            else x := x + 1
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return True

    def P(env: Env) -> Formula:
        return env["x"] == 1

    def Q(env: Env) -> Formula:
        return env["x"] == 0

    assert verify(P, ast, Q, linv)

def test_21() -> None:
    ast = parse(
        """
        if x != y
            then x := x / 2
            else x := x + 1
        """
    )
    assert ast is not None

    def P(env: Env) -> Formula:
        return And(env["x"] == 1,env["y"]==3)

    def Q(env: Env) -> Formula:
        return env["x"] == 0

    assert verify(P, ast, Q)

def test_22() -> None:
    ast = parse(
        """
        x := 32;
        y := 1;
        while x >= y do
            x := x / 2
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["x"]>=env["y"]-1, env["y"]==1)

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["x"] == 0

    assert verify(P, ast, Q, linv)

def test_23() -> None:
    ast = parse(
        """
        x := 32;
        y := 1;
        while x >= y do
            x := x / 2
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["x"] >=env["y"]-1, env["y"]==1)

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["x"] == 1

    assert not verify(P, ast, Q, linv)

def test_24() -> None:
    ast = parse(
        """
        x := 1;
        y := 32;
        while x <= y do
            x := x * 2
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["x"]<=64, env["x"]>=1, env["y"]==32)

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["x"] <=64

    assert verify(P, ast, Q, linv)

def test_25() -> None:
    ast = parse(
        """
        x := 1;
        y := 32;
        while x <= y do
            x := x * 2
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["x"]<=64, env["x"]>=1, env["y"]==32)

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["x"] < 64

    assert not verify(P, ast, Q, linv)

def test_26() -> None:
    ast = parse(
        """
        x := 10;
        y := 0;
        while y < x do
        (
            x := x - 1;
            y := y + 1
        )
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["x"]+env["y"]==10, env["y"]<=env["x"])

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["x"]==5

    assert verify(P, ast, Q, linv)

def test_27() -> None:
    ast = parse(
        """
        x := 10;
        y := 0;
        while y < x do
        (
            x := x - 1;
            y := y + 1
        )
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["x"]+env["y"]==10, env["y"]<=env["x"])

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["x"]!=5

    assert not verify(P, ast, Q, linv)

def test_28() -> None:
    ast = parse(
        """
        while a != b do
            if a > b
                then a := a - b
                else b := b - a
    """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return env["a"] > 0

    def P(env: Env) -> Formula:
        return And(env["a"] > 0, env["b"] > 0)

    def Q(env: Env) -> Formula:
        return env["a"] != env["b"]

    assert not verify(P, ast, Q, linv)

def test_29() -> None:
    ast = parse(
        """
        a := b;
        while i < n do (
            a := a + 1;
            b := b + 1
        )
    """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return env["a"] == env["b"]

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["a"] > env["b"]

    assert not verify(P, ast, Q, linv)

def test_30() -> None:
    ast = parse(
        """
        x := 0;
        y := 0;
        while y < 5 do
           ( x := x + 1;
            y := y + 1 )
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["y"] == env["x"], env["y"]<=5)

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return Or(env["x"] > 5, env["x"] < 5)

    assert not verify(P, ast, Q, linv)

def test_31() -> None:
    ast = parse(
        """
        t := 1;
        s := 2;
        while x > 0 do
            x := x - 1
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["x"] >= 0, env["t"]==1)

    def P(env: Env) -> Formula:
        return env["x"] >= 0

    def Q(env: Env) -> Formula:
        return env["t"] == 1

    assert verify(P, ast, Q, linv)

def test_32() -> None:
    ast = parse(
        """
        t := 1;
        s := 2;
        while x > 0 do
            x := x - 1
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["x"] >= 0, env["t"]==1)

    def P(env: Env) -> Formula:
        return env["x"] >= 0

    def Q(env: Env) -> Formula:
        return env["x"] > 0

    assert not verify(P, ast, Q, linv)

def test_33() -> None:
    ast = parse(
        """
        x := 1;
        y := 32;
        while x <= y do
            x := x * 2
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["x"]<=64, env["x"]>=1, env["y"]==32)

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["x"] > env["y"]

    assert verify(P, ast, Q, linv)

def test_34() -> None:
    ast = parse(
        """
        x := 32;
        y := 1;
        while x >= y do
            x := x / 2
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["x"] >=env["y"]-1, env["y"]==1)

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["x"] + 1 == env["y"]

    assert verify(P, ast, Q, linv)

def test_35() -> None:
    ast = parse(
        """
        x := 32;
        y := 1;
        while x >= y do
            x := x / 2
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["x"] >=env["y"]-1, env["y"]==1)

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return (env["x"]+1)*2 + 1 == env["y"]

    assert not verify(P, ast, Q, linv)


def test_36() -> None:
    ast = parse(
        """
        x := 5;
        y := 0;
        while y < x do (
            y := y + 1
        )
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["y"] >= 0, env["y"] <= env["x"])

    def P(env: Env) -> Formula:
        return env["x"] == 5

    def Q(env: Env) -> Formula:
        return env["y"] == 5

    assert verify(P, ast, Q, linv)

def test_37() -> None:
    ast = parse(
        """
        if a > b
            then max := a
            else max := b
        """
    )
    assert ast is not None

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return Or(
            And(env["a"] >= env["b"], env["max"] == env["a"]),
            And(env["b"] > env["a"], env["max"] == env["b"])
        )

    assert verify(P, ast, Q)

def test_38() -> None:
    ast = parse(
        """
        z := 0;
        while x > 0 do (
            z := z + y;
            x := x - 1
        )
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["x"] >= 0, env["z"] >= 0)

    def P(env: Env) -> Formula:
        return And(env["x"] >= 0, env["y"] >= 0, env["z"] == 0)

    def Q(env: Env) -> Formula:
        return env["z"] == env["y"] * env["x"]

    assert verify(P, ast, Q, linv)

def test_39() -> None:
    ast = parse(
        """
        x := 1;
        while x < 100 do
            x := x * 3
        """
    )
    assert ast is not None

    def linv(env: Env) -> Formula:
        return And(env["x"] >= 1)

    def P(env: Env) -> Formula:
        return True

    def Q(env: Env) -> Formula:
        return env["x"] >= 100

    assert verify(P, ast, Q, linv)

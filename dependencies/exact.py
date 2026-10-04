"""Shared exact linear algebra for untrusted certificate synthesis."""


class SingularSystem(ValueError):
    """The square linear system has no unique solution."""


def solve_linear(matrix, rhs):
    """Solve a square system over Fraction values without changing the inputs."""
    n = len(rhs)
    rows = [list(row) + [value] for row, value in zip(matrix, rhs)]
    for column in range(n):
        pivot = next((i for i in range(column, n) if rows[i][column]), None)
        if pivot is None:
            raise SingularSystem("Singular linear system")
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scale = rows[column][column]
        rows[column] = [value / scale for value in rows[column]]
        for i in range(n):
            if i != column:
                scale = rows[i][column]
                rows[i] = [x - scale*y for x, y in zip(rows[i], rows[column])]
    return tuple(row[-1] for row in rows)

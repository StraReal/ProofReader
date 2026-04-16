import re
import sys
from dataclasses import dataclass
from typing import List, Dict, Set, Optional


def load_file(filename: str) -> str:
    try:
        with open(filename, 'r') as f:
            return f.read()
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found")
        return ""

# ============ LEXER ============

@dataclass
class Token:
    type: str  # 'HYPOTHESIS', 'LET', 'IDENT', 'EQUALS', 'ANGLE', 'NUMBER', 'COLON', 'EOF'
    value: str
    line: int


def tokenize(code: str) -> List[Token]:
    tokens = []
    lines = code.split('\n')

    for line_num, line in enumerate(lines, 1):
        pos = 0
        while pos < len(line):
            if line[pos].isspace():
                pos += 1
                continue

            # Hypothesis keyword
            if line[pos:].startswith('Hypothesis'):
                tokens.append(Token('HYPOTHESIS', 'Hypothesis', line_num))
                pos += 10

            # Proof keyword
            elif line[pos:].startswith('Proof'):
                tokens.append(Token('PROOF', 'Proof', line_num))
                pos += 5

            # Let keyword and following ones to it
            elif line[pos:].startswith('let'):
                tokens.append(Token('LET', 'let', line_num))
                pos += 3
            elif line[pos:].startswith('iso'):
                tokens.append(Token('ISO', 'iso', line_num))
                pos += 3
            elif line[pos:].startswith('square'):
                tokens.append(Token('SQUARE', 'square', line_num))
                pos += 6
            elif line[pos:].startswith('equilateral'):
                tokens.append(Token('EQUILATERAL', 'equilateral', line_num))
                pos += 6
            elif line[pos:].startswith('base'):
                tokens.append(Token('BASE', 'base', line_num))
                pos += 4

            # Angle prefix
            elif line[pos:].startswith('ang'):
                pos += 3
                word = ''
                while pos < len(line) and line[pos].isalnum():
                    word += line[pos]
                    pos += 1
                tokens.append(Token('ANGLE', f'ang{word}', line_num))
                continue

            # Identifiers (ABC, AC, etc.)
            elif line[pos].isalpha():
                word = ''
                while pos < len(line) and line[pos].isalnum():
                    word += line[pos]
                    pos += 1
                tokens.append(Token('IDENT', word, line_num))
                continue

            # Numbers
            elif line[pos].isdigit():
                num = ''
                while pos < len(line) and line[pos].isdigit():
                    num += line[pos]
                    pos += 1
                tokens.append(Token('NUMBER', num, line_num))
                continue

            # Operators
            elif line[pos] == '=':
                tokens.append(Token('EQUALS', '=', line_num))
                pos += 1
            elif line[pos] == ':':
                tokens.append(Token('COLON', ':', line_num))
                pos += 1
            else:
                pos += 1

    tokens.append(Token('EOF', '', len(lines)))
    return tokens


# ============ PARSER ============

@dataclass
class HypothesisBlock:
    statements: List['Statement']


@dataclass
class Statement:
    type: str  # 'let', 'equality', 'angle_claim'
    objects: List[str]  # ABC, AC, BC, etc.
    value: Optional[str] = None  # For equalities/angles
    line: int = 0

class Parser:
    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.pos = 0

    def current(self) -> Token:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else self.tokens[-1]

    def advance(self):
        self.pos += 1

    def parse(self) -> tuple[Optional[HypothesisBlock], List[Statement]]:
        hypothesis = None
        proofs = []

        if self.current().type == 'HYPOTHESIS':
            self.advance()
            if self.current().type == 'COLON':
                self.advance()
            hypothesis = self.parse_hypothesis_block()

        while self.current().type != 'EOF':
            stmt = self.parse_statement()
            if stmt:
                proofs.extend(stmt)

        return hypothesis, proofs

    def parse_hypothesis_block(self) -> HypothesisBlock:
        statements = []
        while self.current().type not in ['PROOF', 'EOF']:  # Stop at PROOF delimiter
            stmt = self.parse_statement()
            if stmt:
                statements.extend(stmt)
        return HypothesisBlock(statements)

    def parse_statement(self) -> List[Statement]:
        statements = []
        line = self.current().line

        if self.current().type == 'LET':
            self.advance()
            obj = self.current().value if self.current().type == 'IDENT' else None
            self.advance()
            line = self.current().line

            statements.append(Statement('let', [obj], line=line))

            if self.current().type == 'ISO':
                self.advance()
                points = list(obj)
                if len(points) != 3:
                    print(f"Syntax Error on line {line}: 'iso' requires a 3-point plane, given: {''.join(points)}")
                    sys.exit(1)
                base = points[0] + points[1]

                if self.current().type == 'BASE':
                    self.advance()
                    base = self.current().value if self.current().type == 'IDENT' else base

                    if len(base) != 2:
                        print(f"Syntax Error on line {line}: 'base' requires a 2-letter edge name (given {base})")
                        sys.exit(1)

                    if not (base[0] in points and base[1] in points):
                        print(f"Syntax Error on line {line}: 'base' must use points from triangle (given: {base} to {points})")
                        sys.exit(1)

                    self.advance()

                # Compute equal sides
                if base == points[0] + points[1]:
                    equal_sides = [points[0] + points[2], points[1] + points[2]]
                elif base == points[0] + points[2]:
                    equal_sides = [points[0] + points[1], points[1] + points[2]]
                else:
                    equal_sides = [points[0] + points[1], points[0] + points[2]]

                for i in range(len(equal_sides) - 1):
                    statements.append(Statement('equality', [equal_sides[i], equal_sides[i + 1]], line=line))

            if self.current().type == 'SQUARE':
                self.advance()
                points = list(obj)
                if len(points) != 4:
                    print(f"Syntax Error on line {line}: 'iso' requires a 4-point plane, given: {''.join(points)}")
                    sys.exit(1)

                for i in range(len(points)-2):
                    statements.append(Statement('equality', [points[i] + points[i + 1], points[i+1] + points[(i + 2)%len(points)]], line=line))

            if self.current().type == 'EQUILATERAL':
                self.advance()
                points = list(obj)
                for i in range(len(points) - 2):
                    statements.append(Statement('equality', [points[i] + points[i + 1],
                                                             points[i + 1] + points[(i + 2) % len(points)]], line=line))



        elif self.current().type == 'IDENT':
            left = self.current().value
            self.advance()
            if self.current().type == 'EQUALS':
                self.advance()
                if self.current().type != 'IDENT':
                    print(f"Syntax Error on line {line}: Expected identifier after '='")
                    sys.exit(1)
                right = self.current().value
                if len(right) != len(left):
                    print(
                        f"Syntax Error on line {line}: Only two objects with the same amount of points can be equal (given {left}, {right})")
                    sys.exit(1)
                self.advance()
                statements.append(Statement('equality', [left, right], line=line))

        elif self.current().type == 'ANGLE':
            angle = self.current().value
            self.advance()
            if self.current().type == 'EQUALS':
                self.advance()
                value = self.current().value if self.current().type == 'NUMBER' else None
                self.advance()
                statements.append(Statement('angle_claim', [angle], value, line=line))

        else:
            self.advance()

        return statements


class Validator:
    def __init__(self):
        self.defined_objects: Set[str] = set()
        self.defined_edges: Set[tuple] = set()
        self.known_equalities: Set[frozenset] = set()  # Track proven equalities
        self.errors: List[str] = []

    def normalize_edge(self, edge: str) -> str:
        return ''.join(sorted(edge))

    def validate(self, hypothesis: Optional[HypothesisBlock], proofs: List[Statement]):
        # Process hypothesis first to build known equalities
        if hypothesis:
            for stmt in hypothesis.statements:
                self.process_statement(stmt, is_hypothesis=True)
            self.propagate_transitivity()
            print("DEBUG: after propagate_transitivity, know_equalities: ", self.known_equalities)

        # validate proofs against known equalities
        for stmt in proofs:
            self.process_statement(stmt, is_hypothesis=False)

    def propagate_transitivity(self):
        changed = True
        while changed:
            changed = False

            eq_list = list(self.known_equalities)

            for i, eq1 in enumerate(eq_list):
                for eq2 in eq_list[i + 1:]:
                    if eq1 & eq2:
                        union = eq1 | eq2
                        self.known_equalities.discard(eq1)
                        self.known_equalities.discard(eq2)
                        self.known_equalities.add(union)
                        changed = True
                        break
                if changed:
                    break

    def process_statement(self, stmt: Statement, is_hypothesis: bool):
        if stmt.type == 'let':
            obj = stmt.objects[0]
            print(f"DEBUG: Processing 'let {obj}'")
            points = list(obj)
            print(f"DEBUG: Points = {points}")
            for p in points:
                self.defined_objects.add(p)
            if len(points) > 2:
                print(f"DEBUG: Adding edges for {points}")
                for point in points:
                    for other_point in points:
                        if point != other_point:
                            self.defined_edges.add(tuple(sorted([point, other_point])))
                print(f"DEBUG: defined_edges = {self.defined_edges}")
        if stmt.type == 'equality':
            left_str, right_str = stmt.objects[0], stmt.objects[1]
            left = self.normalize_edge(stmt.objects[0])
            right = self.normalize_edge(stmt.objects[1])

            if not self.edge_exists(left):
                self.errors.append(f"Line {stmt.line}: '{left_str}' is not a defined edge")
            if not self.edge_exists(right):
                self.errors.append(f"Line {stmt.line}: '{right_str}' is not a defined edge")

            equality_pair = frozenset([left, right])

            if is_hypothesis:
                self.known_equalities.add(equality_pair)
                print(f"DEBUG: known_equalities = {self.known_equalities}")
            else:
                if stmt.type == 'equality':
                    left = self.normalize_edge(stmt.objects[0])
                    right = self.normalize_edge(stmt.objects[1])

                    if not self.edge_exists(left):
                        self.errors.append(f"Line {stmt.line}: '{left}' is not a defined edge")
                    if not self.edge_exists(right):
                        self.errors.append(f"Line {stmt.line}: '{right}' is not a defined edge")

                    left_class = None
                    right_class = None

                    for eq_class in self.known_equalities:
                        if left in eq_class:
                            left_class = eq_class
                        if right in eq_class:
                            right_class = eq_class

                    if is_hypothesis:
                        self.known_equalities.add(frozenset([left, right]))
                    else:
                        if left_class is None or right_class is None or left_class != right_class:
                            self.errors.append(f"Line {stmt.line}: '{left} = {right}' is unproven")
                else:
                    self.known_equalities.add(equality_pair)

    def edge_exists(self, edge: str) -> bool:
        if len(edge) != 2:
            return False
        return tuple(sorted(edge)) in self.defined_edges

# test

code = load_file('statement.math')

tokens = tokenize(code)
parser = Parser(tokens)
hypothesis, proofs = parser.parse()

validator = Validator()
validator.validate(hypothesis, proofs)

print("=== PARSED ===")
if hypothesis:
    print(f"Hypothesis: {len(hypothesis.statements)} statements")
    for s in hypothesis.statements:
        print(f"  {s}")
print(f"Proofs: {len(proofs)} statements")
for s in proofs:
    print(f"  {s}")

print("\n=== VALIDATION ===")
if validator.errors:
    for error in validator.errors:
        print(f"Error: {error}")
else:
    print("Statement returned valid")
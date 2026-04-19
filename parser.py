from common_classes import *
from itertools import combinations

class Parser:
    def __init__(self, tokens: List[Token], import_map: dict):
        self.tokens = tokens
        self.pos = 0
        self.axioms: Dict[str, AxiomDefinition] = {}
        self.theorems: Dict[str, TheoremDefinition] = {}
        self.import_map: dict = import_map

    def current(self) -> Token:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else self.tokens[-1]

    def advance(self):
        self.pos += 1

    def parse(self) -> tuple[Dict[str, AxiomDefinition], Dict[str, TheoremDefinition], Optional[HypothesisBlock], List[Statement], list, list]:
        hypothesis = None
        proofs = []
        ordered = []

        while self.current().type != 'EOF':
            if self.current().type == 'AXIOM':
                axiom = self.parse_axiom()
                self.axioms[axiom.name] = axiom
                ordered.append(('axiom', axiom))
            elif self.current().type == 'THEOREM':
                theorem = self.parse_theorem()
                self.theorems[theorem.name] = theorem
                ordered.append(('theorem', theorem))
            elif self.current().type == 'IMPORT':
                self.advance()
                if self.current().type == 'IDENT':
                    return self.axioms, self.theorems, hypothesis, proofs, [self.current().value, self.current().line_num], ordered
            elif self.current().type == 'HYPOTHESIS':
                self.advance()
                if self.current().type == 'COLON':
                    self.advance()
                hypothesis = self.parse_hypothesis_block()
            else:
                stmt = self.parse_statement()
                if stmt:
                    proofs.extend(stmt)

        return self.axioms, self.theorems, hypothesis, proofs, [], ordered

    def parse_hypothesis_block(self, stop_tokens: List[str] = None) -> HypothesisBlock:
        if stop_tokens is None:
            stop_tokens = ['PROOF', 'EOF']

        statements = []
        while self.current().type not in stop_tokens:
            stmt = self.parse_statement()
            if stmt:
                statements.extend(stmt)
        return HypothesisBlock(statements)

    def parse_axiom(self) -> AxiomDefinition:
        self.advance()  # skip 'axiom'

        line = self.current().line_num
        if self.current().type != 'IDENT':
            print_error(line, f"Syntax Error: Expected axiom name", self.import_map)
            sys.exit(1)
        name = self.current().value
        self.advance()

        if self.current().type != 'COLON':
            print_error(line, "Syntax Error: Expected ':' after axiom name", self.import_map)
            sys.exit(1)
        self.advance()

        if self.current().type != 'GIVEN':
            print_error(line, "Syntax Error: Expected 'Given' in axiom", self.import_map)
            sys.exit(1)
        self.advance()
        if self.current().type == 'COLON':
            self.advance()

        given = self.parse_hypothesis_block(stop_tokens=['THEN'])

        if self.current().type != 'THEN':
            print_error(line, "Syntax Error: Expected 'Then' in axiom", self.import_map)
            sys.exit(1)
        self.advance()
        if self.current().type == 'COLON':
            self.advance()

        then_statements = []
        while self.current().type not in ('AXIOM', 'THEOREM', 'HYPOTHESIS', 'PROOF', 'EOF'):
            stmts = self.parse_statement()
            if stmts:
                then_statements.extend(stmts)

        let_objects = []
        let_numvars = []
        for stmt in given.statements:
            if stmt.type == 'let':
                let_objects.append(stmt.objects[0])
            elif stmt.type == 'let_numvar':
                let_numvars.append(stmt.objects[0])

        return AxiomDefinition(name, given, then_statements, let_objects, let_numvars)

    def parse_theorem(self) -> TheoremDefinition:
        self.advance()
        line = self.current().line_num

        if self.current().type != 'IDENT':
            print_error(line, "Syntax Error: Expected theorem name", self.import_map)
            sys.exit(1)
        name = self.current().value
        self.advance()

        if self.current().type != 'COLON':
            print_error(line, "Syntax Error: Expected theorem name", self.import_map)
            print("Syntax Error: Expected ':' after theorem name")
            sys.exit(1)
        self.advance()

        if self.current().type != 'GIVEN':
            print_error(line, "Syntax Error: Expected 'Given' in theorem", self.import_map)
            sys.exit(1)
        self.advance()
        if self.current().type == 'COLON':
            self.advance()

        given = self.parse_hypothesis_block(stop_tokens=['THEN'])

        if self.current().type != 'THEN':
            print_error(line, "Syntax Error: Expected 'Then' in theorem", self.import_map)
            sys.exit(1)
        self.advance()
        if self.current().type == 'COLON':
            self.advance()

        then_statements = []
        while self.current().type not in ('PROOF', 'AXIOM', 'THEOREM', 'HYPOTHESIS', 'EOF'):
            stmts = self.parse_statement()
            if stmts:
                then_statements.extend(stmts)

        if self.current().type != 'PROOF':
            print_error(line, "Syntax Error: Expected 'Proof' block in theorem '{name}'", self.import_map)
            sys.exit(1)
        self.advance()
        if self.current().type == 'COLON':
            self.advance()

        proof_statements = []
        while self.current().type not in ('AXIOM', 'THEOREM', 'HYPOTHESIS', 'EOF'):
            stmts = self.parse_statement()
            if stmts:
                proof_statements.extend(stmts)

        let_objects = []
        let_numvars = []
        for stmt in given.statements:
            if stmt.type == 'let':
                let_objects.append(stmt.objects[0])
            elif stmt.type == 'let_numvar':
                let_numvars.append(stmt.objects[0])

        return TheoremDefinition(name, given, then_statements, proof_statements, let_objects, let_numvars)

    def parse_sum_operands(self, first_operand: str, allowed_types: Sequence[str]) -> List[tuple]:
        """Returns list of (sign, name) pairs. First operand always gets '+'."""
        operands = [('+', first_operand)]
        while self.current().type in ('PLUS', 'MINUS'):
            sign = '+' if self.current().type == 'PLUS' else '-'
            self.advance()
            if self.current().type not in allowed_types:
                line = self.current().line_num
                print_error(line, f"Syntax Error: Expected {allowed_types} after '+'/'-'", self.import_map)
                sys.exit(1)
            operands.append((sign, self.current().value))
            self.advance()
        return operands

    def parse_axiom_bindings(self) -> list:
        raw_args = []
        while self.current().type != 'RBRACE':
            if self.current().type in ('IDENT', 'NUMBER', 'ANGLE'):
                raw_args.append(self.current().value)
                self.advance()
                if self.current().type == 'COMMA':
                    self.advance()
            else:
                break
        return raw_args

    def _parse_equality_chain(self, first_operands, left_type, line):
        """Parse = B = C = D... and return list of all sides."""
        sides = [first_operands]
        while self.current().type == 'EQUALS':
            self.advance()
            rhs = self.parse_rhs(left_type, line)
            if rhs[0] == 'single':
                _, right, right_type = rhs
                sides.append((right, right_type))
            else:
                _, right_operands = rhs
                sides.append(right_operands)
        return sides

    def _emit_pair(self, left, right, line):
        statements = []
        # Normalize both sides to operand lists
        if isinstance(left, tuple) and not isinstance(left[0], tuple):
            # it's a (value, type) single token
            left_val, left_type = left
            left_ops = [('+', left_val)]
        else:
            left_ops = left
            left_type = 'IDENT'  # default

        if isinstance(right, tuple) and not isinstance(right[0], tuple):
            right_val, right_type = right
            right_ops = [('+', right_val)]
        else:
            right_val = None
            right_type = None
            right_ops = right

        # Single = single
        if len(left_ops) == 1 and right_val is not None:
            if right_type in ('NUMBER', 'NUMVAR'):
                statements.append(Statement('assignment', [left_ops[0][1], right_val], line=line))
            else:
                statements.append(Statement('equality', [left_ops[0][1], right_val], line=line))
        # Multi = single number
        elif right_val is not None and right_type in ('NUMBER', 'NUMVAR'):
            statements.append(Statement('sum_assignment', [left_ops, right_val], line=line))
        # anything = multi, or multi = single ident
        else:
            statements.append(Statement('sum_equality', [left_ops, right_ops], line=line))

        return statements

    def parse_statement(self) -> List[Statement]:
        statements = []
        line = self.current().line_num
        line_val = self.current().line

        if self.current().type == 'IDENT' and self.pos + 1 < len(self.tokens) and self.tokens[
            self.pos + 1].type == 'LBRACE':
            axiom_name = self.current().value
            self.advance()
            self.advance()

            raw_args = self.parse_axiom_bindings()

            if self.current().type != 'RBRACE':
                print(f"Syntax Error: Expected '}}' after axiom bindings")
                sys.exit(1)
            self.advance()

            if self.current().type == 'ARROW':
                self.advance()
                conclusion = self.parse_statement()
                statements.append(Statement('axiom_application', [axiom_name], value=str(raw_args), line=line))
                statements.extend(conclusion)
            return statements

        elif self.current().type == 'LET':
            self.advance()

            obj_type = self.current().type
            obj = self.current().value if obj_type in ('IDENT', 'ANGLE', 'NUMVAR', 'VARIABLE') else None
            self.advance()

            statements.append(Statement('let', [obj], line=line))

            if obj_type == 'NUMVAR':
                left = obj
                left_operands = self.parse_sum_operands(left, ('NUMBER', 'IDENT', 'ANGLE', 'NUMVAR'))

                if self.current().type == 'EQUALS':
                    self.advance()
                    rhs = self.parse_rhs(('NUMVAR', 'ANGLE', 'IDENT', 'NUMBER'), line)
                    if rhs[0] == 'single':
                        _, right, right_type = rhs
                        if right_type in ('NUMBER', 'NUMVAR'):
                            if len(left_operands) == 1:
                                statements.append(Statement('assignment', [left, right], line=line))
                            else:
                                statements.append(Statement('sum_assignment', [left_operands, right], line=line))
                        elif right_type in ('IDENT', 'ANGLE'):
                            if len(left_operands) == 1:
                                statements.append(Statement('equality', [left, right], line=line))
                            else:
                                statements.append(Statement('sum_equality', [left_operands, [('+', right)]], line=line))
                    else:
                        _, right_operands = rhs
                        statements.append(Statement('sum_equality', [left_operands, right_operands], line=line))

                if self.current().type == 'INEQUALS':
                    self.advance()
                    right = self.current().value
                    self.advance()
                    statements.append(Statement('inequality', [left, right], line=line))

            if obj_type == 'IDENT':
                left = obj
                left_operands = self.parse_sum_operands(left, ('NUMBER', 'IDENT', 'ANGLE', 'NUMVAR'))

                if self.current().type == 'EQUALS':
                    self.advance()
                    rhs = self.parse_rhs(('NUMVAR', 'ANGLE', 'IDENT', 'NUMBER'), line)
                    if rhs[0] == 'single':
                        _, right, right_type = rhs
                        if right_type in ('NUMBER', 'NUMVAR'):
                            if len(left_operands) == 1:
                                statements.append(Statement('assignment', [left, right], line=line, in_let=True))
                            else:
                                statements.append(Statement('sum_assignment', [left_operands, right], line=line, in_let=True))
                        elif right_type in ('IDENT', 'ANGLE'):
                            if len(left_operands) == 1:
                                statements.append(Statement('equality', [left, right], line=line, in_let=True))
                            else:
                                statements.append(Statement('sum_equality', [left_operands, [('+', right)]], line=line, in_let=True))
                    else:
                        _, right_operands = rhs
                        statements.append(Statement('sum_equality', [left_operands, right_operands], line=line, in_let=True))

                if self.current().type == 'INEQUALS':
                    self.advance()
                    right = self.current().value
                    self.advance()
                    statements.append(Statement('equality', [left, right], line=line, goal=False))

            if self.current().type == 'EQUALS':
                self.advance()
            if self.current().type == 'ISO':
                self.advance()
                points = list(obj)
                if len(points) != 3:
                    print_error(line, f"Syntax Error: 'iso' requires a 3-point plane, given: {''.join(points)}",
                                self.import_map)
                    sys.exit(1)
                base = points[0] + points[1]
                if self.current().type == 'BASE':
                    self.advance()
                    base = self.current().value if self.current().type == 'IDENT' else base
                    if len(base) != 2:
                        print_error(line,
                                    f"Syntax Error: 'base' requires a 2-letter edge name (given {base})",
                                    self.import_map)
                        sys.exit(1)
                    if not (base[0] in points and base[1] in points):
                        print_error(line, f"Syntax Error: 'base' must use points from triangle (given: {base} to {points})", self.import_map)
                        sys.exit(1)
                    self.advance()
                if base == points[0] + points[1]:
                    equal_sides = [points[0] + points[2], points[1] + points[2]]
                elif base == points[0] + points[2]:
                    equal_sides = [points[0] + points[1], points[1] + points[2]]
                else:
                    equal_sides = [points[0] + points[1], points[0] + points[2]]
                for i in range(len(equal_sides) - 1):
                    statements.append(Statement('equality', [equal_sides[i], equal_sides[i + 1]], line=line))

            if self.current().type == 'MEDIAN':
                self.advance()
                point = list(obj)
                if obj_type != 'IDENT':
                    print_error(line, f"Syntax Error: 'median' requires an identifier, given: {obj_type}", self.import_map)
                    sys.exit(1)
                if len(point) != 1:
                    print_error(line, f"Syntax Error: 'median' requires a single point, given: {''.join(point)}",
                                self.import_map)
                    sys.exit(1)
                if self.current().type != 'IDENT':
                    print_error(line, f"Syntax Error: identifier expected after 'median', given {self.current().type}",
                                self.import_map)
                    sys.exit(1)
                base = self.current().value
                if len(base) != 2:
                    print_error(line, f"Syntax Error: 'median' is defined by a 2-letter edge name, given {base}",
                                self.import_map)
                    sys.exit(1)

                equality_pair = [base[0] + point[0], base[1] + point[0]]
                statements.append(Statement('equality', equality_pair, line=line))
                statements.append(Statement('contains', [base, point[0]], line=line))

            if self.current().type == 'BISECTOR':
                self.advance()
                point = list(obj)
                if obj_type != 'IDENT':
                    print_error(line, f"Syntax Error: 'bisector' requires an identifier, given: {obj_type}",
                                self.import_map)
                    sys.exit(1)
                if len(point) != 1:
                    print_error(line, f"Syntax Error: 'bisector' requires a single point, given: {''.join(point)}",
                                self.import_map)
                    sys.exit(1)

                base = self.current().value
                if self.current().type != 'ANGLE' or len(base) != 6:
                    print_error(line, f"Syntax Error: valid angle expected after 'bisector' (given {base})",
                                self.import_map)
                    sys.exit(1)
                base = base[3:]

                equality_pair = ['ang'+base[0]+base[1]+point[0], 'ang'+point[0]+base[1]+base[2]]
                statements.append(Statement('equality', equality_pair, line=line))

            if self.current().type == 'SQUARE':
                self.advance()
                points = list(obj)
                if len(points) != 4:
                    print_error(line, f"Syntax Error: 'square' requires a 4-point plane, given: {''.join(points)}",
                                self.import_map)
                    sys.exit(1)
                for i in range(len(points) - 2):
                    statements.append(Statement('equality', [points[i] + points[i + 1],
                                                             points[i + 1] + points[(i + 2) % len(points)]], line=line))

            if self.current().type == 'RECTANGLE':
                self.advance()
                points = list(obj)
                if obj_type != 'IDENT':
                    print_error(line, f"Syntax Error: 'rectangle' requires an identifier, given: {obj_type}",
                                self.import_map)
                    sys.exit(1)
                if len(points) != 4:
                    print_error(line, f"Syntax Error: 'rectangle' requires a 4-point plane, given: {''.join(points)}",
                                self.import_map)
                    sys.exit(1)

                statements.append(Statement('equality', [points[0] + points[1],
                                                            points[2] + points[3]], line=line))
                statements.append(Statement('equality', [points[1] + points[2],
                                                         points[3] + points[0]], line=line))

            if self.current().type == 'EQUILATERAL':
                self.advance()
                points = list(obj)
                for i in range(len(points) - 1):
                    statements.append(Statement('equality', [points[i] + points[i + 1],
                                                             points[i + 1] + points[(i + 2) % len(points)]], line=line))

        elif self.current().type == 'NUMVAR':
            left = self.current().value
            self.advance()
            left_operands = self.parse_sum_operands(left, ('NUMBER', 'IDENT', 'ANGLE', 'NUMVAR'))
            if self.current().type == 'EQUALS':
                sides = [(left_operands, None, None)]
                while self.current().type == 'EQUALS':
                    self.advance()
                    rhs = self.parse_rhs(('NUMVAR', 'ANGLE', 'IDENT', 'NUMBER'), line)
                    if rhs[0] == 'single':
                        _, right, right_type = rhs
                        sides.append(([('+', right)], right_type, right))
                    else:
                        _, right_operands = rhs
                        sides.append((right_operands, None, None))
                for i in range(len(sides) - 1):
                    left_ops = sides[i][0]
                    right_ops = sides[i + 1][0]
                    right_type = sides[i + 1][1]
                    right_val = sides[i + 1][2]
                    if right_val is not None and right_type in ('NUMBER', 'NUMVAR'):
                        if len(left_ops) == 1:
                            statements.append(Statement('assignment', [left_ops[0][1], right_val], line=line))
                        else:
                            statements.append(Statement('sum_assignment', [left_ops, right_val], line=line))
                    elif right_val is not None:
                        if len(left_ops) == 1:
                            statements.append(Statement('equality', [left_ops[0][1], right_val], line=line))
                        else:
                            statements.append(Statement('sum_equality', [left_ops, right_ops], line=line))
                    else:
                        statements.append(Statement('sum_equality', [left_ops, right_ops], line=line))

            if self.current().type == 'INEQUALS':
                self.advance()
                right = self.current().value
                self.advance()
                statements.append(Statement('equality', [left, right], line=line, goal=False))

        elif self.current().type == 'IDENT':
            left = self.current().value
            left_type = self.current().type
            self.advance()
            left_operands = self.parse_sum_operands(left, (left_type,))
            if self.current().type == 'EQUALS':
                sides = [(left_operands, None, None)]
                while self.current().type == 'EQUALS':
                    self.advance()
                    rhs = self.parse_rhs(left_type, line)
                    if rhs[0] == 'single':
                        _, right, right_type = rhs
                        sides.append(([('+', right)], right_type, right))
                    else:
                        _, right_operands = rhs
                        sides.append((right_operands, None, None))
                for i in range(len(sides) - 1):
                    left_ops = sides[i][0]
                    right_ops = sides[i + 1][0]
                    right_type = sides[i + 1][1]
                    right_val = sides[i + 1][2]
                    if right_val is not None and right_type in ('NUMBER', 'NUMVAR'):
                        if len(left_ops) == 1:
                            statements.append(Statement('assignment', [left_ops[0][1], right_val], line=line))
                        else:
                            statements.append(Statement('sum_assignment', [left_ops, right_val], line=line))
                    elif right_val is not None:
                        if len(left_ops) == 1:
                            statements.append(Statement('equality', [left_ops[0][1], right_val], line=line))
                        else:
                            statements.append(Statement('sum_equality', [left_ops, right_ops], line=line))
                    else:
                        statements.append(Statement('sum_equality', [left_ops, right_ops], line=line))

            if self.current().type == 'INEQUALS':
                self.advance()
                if self.current().type not in ('IDENT', 'NUMVAR'):
                    print(f"{line_val}\nSyntax Error on line {line}: Expected identifier or numvar after '!='")
                    sys.exit(1)
                right = self.current().value
                self.advance()
                statements.append(Statement('equality', [left, right], line=line, goal=False))

            if self.current().type == 'IN':
                if len(left) != 1:
                    print_error(line, f"Syntax Error: only a point can be contained, given: {left}",
                                self.import_map)
                    sys.exit(1)
                self.advance()
                segment = self.current().value
                if len(segment) < 2:
                    print_error(line, f"Syntax Error: points can only be contained in edges or planes, given: {segment}",
                                self.import_map)
                    sys.exit(1)
                self.advance()
                statements.append(Statement('contains', [segment, left], line=line))

            if self.current().type == 'CONTAINS':
                if len(left) < 2:
                    print_error(line, f"Syntax Error: points can only be contained in edges or planes, given: {left}",
                                self.import_map)
                    sys.exit(1)
                self.advance()
                point = self.current().value
                if len(point) != 1:
                    print_error(line, f"Syntax Error: only a point can be contained, given: {point}",
                                self.import_map)
                    sys.exit(1)
                self.advance()
                statements.append(Statement('contains', [left, point], line=line))

        elif self.current().type == 'ANGLE':
            left_angle = self.current().value
            left_type = self.current().type
            self.advance()
            left_operands = self.parse_sum_operands(left_angle, (left_type,))
            if self.current().type == 'EQUALS':
                sides = [(left_operands, None, None)]
                while self.current().type == 'EQUALS':
                    self.advance()
                    rhs = self.parse_rhs(left_type, line)
                    if rhs[0] == 'single':
                        _, right, right_type = rhs
                        sides.append(([('+', right)], right_type, right))
                    else:
                        _, right_operands = rhs
                        sides.append((right_operands, None, None))
                for i in range(len(sides) - 1):
                    left_ops = sides[i][0]
                    right_ops = sides[i + 1][0]
                    right_type = sides[i + 1][1]
                    right_val = sides[i + 1][2]
                    if right_val is not None and right_type in ('NUMBER', 'NUMVAR'):
                        if len(left_ops) == 1:
                            statements.append(Statement('assignment', [left_ops[0][1], right_val], line=line))
                        else:
                            statements.append(Statement('sum_assignment', [left_ops, right_val], line=line))
                    elif right_val is not None:
                        if len(left_ops) == 1:
                            statements.append(Statement('equality', [left_ops[0][1], right_val], line=line))
                        else:
                            statements.append(Statement('sum_equality', [left_ops, right_ops], line=line))
                    else:
                        statements.append(Statement('sum_equality', [left_ops, right_ops], line=line))
                for i, j in combinations(range(len(sides)), 2):
                    if j == i + 1:
                        continue
                    left_ops = sides[i][0]
                    right_ops = sides[j][0]
                    right_type = sides[j][1]
                    right_val = sides[j][2]
                    statements.append(
                        Statement('chain_conclusion', [left_ops, right_ops, right_type, right_val], line=line))
            if self.current().type == 'INEQUALS':
                self.advance()
                if self.current().type not in ('ANGLE', 'NUMVAR'):
                    print(f"{line_val}\nSyntax Error on line {line}: Expected angle or numvar after '!='")
                    sys.exit(1)
                right = self.current().value
                self.advance()
                statements.append(Statement('equality', [left_angle, right], line=line, goal=False))
            if self.current().type == 'LESS':
                self.advance()
                right = self.current().value
                self.advance()
                # flip
                statements.append(Statement('greater_than', [right, left_angle], line=line))

            if self.current().type == 'GREATER':
                self.advance()
                right = self.current().value
                self.advance()
                statements.append(Statement('greater_than', [left_angle, right], line=line))

        elif self.current().type == 'NUMBER':
            left = self.current().value
            self.advance()
            left_operands = self.parse_sum_operands(left, ('NUMBER', 'ANGLE', 'IDENT'))
            if self.current().type == 'EQUALS':
                sides = [(left_operands, None, None)]
                while self.current().type == 'EQUALS':
                    self.advance()
                    rhs = self.parse_rhs(('NUMBER', 'ANGLE', 'IDENT'), line)
                    if rhs[0] == 'single':
                        _, right, right_type = rhs
                        sides.append(([('+', right)], right_type, right))
                    else:
                        _, right_operands = rhs
                        sides.append((right_operands, None, None))
                for i in range(len(sides) - 1):
                    left_ops = sides[i][0]
                    right_ops = sides[i + 1][0]
                    right_type = sides[i + 1][1]
                    right_val = sides[i + 1][2]
                    if right_val is not None and right_type in ('NUMBER', 'NUMVAR'):
                        statements.append(Statement('sum_assignment', [left_ops, right_val], line=line))
                    elif right_val is not None:
                        statements.append(Statement('sum_equality', [left_ops, right_ops], line=line))
                    else:
                        statements.append(Statement('sum_equality', [left_ops, right_ops], line=line))

        elif self.current().type == 'TRUE':
            statements.append(Statement('true', self.current().value, line=line))
            self.advance()
        elif self.current().type == 'FALSE':
            statements.append(Statement('true', self.current().value, line=line, goal=False))
            self.advance()

        elif self.current().type == 'PRINT':
            self.advance()
            statements.append(Statement('print', [self.current().value], line=line))
        else:
            self.advance()
        while self.current().type == 'IS':
            self.advance()
            if self.current().type in ('TRUE', 'FALSE'):
                goal = self.current().type == 'TRUE'
                self.advance()
                for s in statements:
                    if not goal:
                        s.goal = not s.goal
        return statements

    def parse_rhs(self, allowed_types: Sequence[str], line: int) -> tuple:
        if self.current().type not in ('NUMBER', 'NUMVAR') and self.current().type not in allowed_types:
            print_error(line, f"Syntax Error: Unexpected token '{self.current().value}' after '='",
                        self.import_map)
            sys.exit(1)

        first_val = self.current().value
        first_type = self.current().type
        self.advance()

        if first_type == 'NUMBER' and self.current().type in ('PLUS', 'MINUS'):
            operands = [('+', first_val)]
            while self.current().type in ('PLUS', 'MINUS'):
                sign = '+' if self.current().type == 'PLUS' else '-'
                self.advance()
                if self.current().type not in allowed_types and self.current().type not in ('NUMBER', 'NUMVAR'):
                    print_error(line, f"Syntax Error: Expected {allowed_types}, number, or numvar after '+'/'-'",
                                self.import_map)
                    sys.exit(1)
                operands.append((sign, self.current().value))
                self.advance()
            return ('sum', operands)

        if first_type not in ('NUMBER', 'NUMVAR') and self.current().type in ('PLUS', 'MINUS'):
            rhs_operands = self.parse_sum_operands(first_val, allowed_types)
            return ('sum', rhs_operands)

        return ('single', first_val, first_type)
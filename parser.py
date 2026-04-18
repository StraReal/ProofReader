from common_classes import *

class Parser:
    def __init__(self, tokens: List[Token], import_map: dict):
        self.tokens = tokens
        self.pos = 0
        self.axioms: Dict[str, AxiomDefinition] = {}
        self.theorems: Dict[str, TheoremDefinition] = {}
        self.import_map: dict = import_map

    def _err(self, line, msg):
        file, lineno = self.get_infile_line(line)
        return f"{file} | Line {lineno}: {msg}"

    def get_infile_line(self, line_num):
        if line_num in self.import_map:
            filename, original_line = self.import_map[line_num]
            return (filename, original_line)
        else:
            return (None, line_num)

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
                print(f"DEBUG: after hypothesis, current token = {self.current()}")
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

        if self.current().type != 'IDENT':
            print("Syntax Error: Expected axiom name")
            sys.exit(1)
        name = self.current().value
        self.advance()

        if self.current().type != 'COLON':
            print("Syntax Error: Expected ':' after axiom name")
            sys.exit(1)
        self.advance()

        if self.current().type != 'GIVEN':
            print("Syntax Error: Expected 'Given' in axiom")
            sys.exit(1)
        self.advance()
        if self.current().type == 'COLON':
            self.advance()

        given = self.parse_hypothesis_block(stop_tokens=['THEN'])

        if self.current().type != 'THEN':
            print("Syntax Error: Expected 'Then' in axiom")
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

        if self.current().type != 'IDENT':
            print("Syntax Error: Expected theorem name")
            sys.exit(1)
        name = self.current().value
        self.advance()

        if self.current().type != 'COLON':
            print("Syntax Error: Expected ':' after theorem name")
            sys.exit(1)
        self.advance()

        if self.current().type != 'GIVEN':
            print("Syntax Error: Expected 'Given' in theorem")
            sys.exit(1)
        self.advance()
        if self.current().type == 'COLON':
            self.advance()

        given = self.parse_hypothesis_block(stop_tokens=['THEN'])

        if self.current().type != 'THEN':
            print("Syntax Error: Expected 'Then' in theorem")
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
            print(f"Syntax Error: Expected 'Proof' block in theorem '{name}'")
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
                print(self._err(line, f"Syntax Error: Expected {allowed_types} after '+'/'-'"))
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
            obj = self.current().value if obj_type in ('IDENT', 'ANGLE', 'NUMVAR') else None
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
                                print(left, right)
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

            if self.current().type == 'EQUALS':
                self.advance()
            if self.current().type == 'ISO':
                self.advance()
                points = list(obj)
                if len(points) != 3:
                    print(self._err(line, f"Syntax Error: 'iso' requires a 3-point plane, given: {''.join(points)}"))
                    sys.exit(1)
                base = points[0] + points[1]
                if self.current().type == 'BASE':
                    self.advance()
                    base = self.current().value if self.current().type == 'IDENT' else base
                    if len(base) != 2:
                        print(self._err(line, f"Syntax Error: 'base' requires a 2-letter edge name (given {base})"))
                        sys.exit(1)
                    if not (base[0] in points and base[1] in points):
                        print(self._err(line, f"Syntax Error: 'base' must use points from triangle (given: {base} to {points})"))
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
                    print(self._err(line, f"Syntax Error: 'median' requires an identifier, given: {obj_type}"))
                    sys.exit(1)
                if len(point) != 1:
                    print(self._err(line, f"Syntax Error: 'median' requires a single point, given: {''.join(point)}"))
                    sys.exit(1)
                if self.current().type != 'IDENT':
                    print(self._err(line, f"Syntax Error: identifier expected after 'median', given {self.current().type}"))
                    sys.exit(1)
                base = self.current().value
                if len(base) != 2:
                    print(self._err(line, f"Syntax Error: 'median' is defined by a 2-letter edge name, given {base}"))
                    sys.exit(1)

                equality_pair = [base[0] + point[0], base[1] + point[0]]
                statements.append(Statement('equality', equality_pair, line=line))

            if self.current().type == 'BISECTOR':
                self.advance()
                point = list(obj)
                if obj_type != 'IDENT':
                    print(self._err(line, f"Syntax Error: 'bisector' requires an identifier, given: {obj_type}"))
                    sys.exit(1)
                if len(point) != 1:
                    print(self._err(line, f"Syntax Error: 'bisector' requires a single point, given: {''.join(point)}"))
                    sys.exit(1)

                base = self.current().value
                if self.current().type != 'ANGLE' or len(base) != 6:
                    print(self._err(line, f"Syntax Error: valid angle expected after 'bisector' (given {base})"))
                    sys.exit(1)
                base = base[3:]

                equality_pair = ['ang'+base[0]+base[1]+point[0], 'ang'+point[0]+base[1]+base[2]]
                statements.append(Statement('equality', equality_pair, line=line))

            if self.current().type == 'SQUARE':
                self.advance()
                points = list(obj)
                if len(points) != 4:
                    print(self._err(line, f"Syntax Error: 'square' requires a 4-point plane, given: {''.join(points)}"))
                    sys.exit(1)
                for i in range(len(points) - 2):
                    statements.append(Statement('equality', [points[i] + points[i + 1],
                                                             points[i + 1] + points[(i + 2) % len(points)]], line=line))

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
                self.advance()
                rhs = self.parse_rhs(('NUMVAR','ANGLE','IDENT','NUMBER'), line)
                if rhs[0] == 'single':
                    _, right, right_type = rhs
                    if right_type in ('NUMBER', 'NUMVAR'):
                        if len(left_operands) == 1:
                            print(left, right)
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

        elif self.current().type == 'IDENT':
            left = self.current().value
            left_type = self.current().type
            self.advance()
            left_operands = self.parse_sum_operands(left, (left_type,))

            if self.current().type == 'EQUALS':
                self.advance()
                rhs = self.parse_rhs(left_type, line)
                if rhs[0] == 'single':
                    _, right, right_type = rhs
                    if right_type in ('NUMBER', 'NUMVAR'):
                        if len(left_operands) == 1:
                            statements.append(Statement('assignment', [left, right], line=line))
                        else:
                            statements.append(Statement('sum_assignment', [left_operands, right], line=line))
                    elif right_type == 'IDENT':
                        if len(left_operands) == 1:
                            statements.append(Statement('equality', [left, right], line=line))
                        else:
                            statements.append(Statement('sum_equality', [left_operands, [('+', right)]], line=line))
                else:
                    _, right_operands = rhs
                    statements.append(Statement('sum_equality', [left_operands, right_operands], line=line))

            if self.current().type == 'INEQUALS':
                self.advance()
                if self.current().type not in ('IDENT', 'NUMVAR'):
                    print(f"{line_val}\nSyntax Error on line {line}: Expected identifier or numvar after '!='")
                    sys.exit(1)
                right = self.current().value
                self.advance()
                statements.append(Statement('inequality', [left, right], line=line))

        elif self.current().type == 'ANGLE':
            left_angle = self.current().value
            left_type = self.current().type
            self.advance()
            left_operands = self.parse_sum_operands(left_angle, (left_type,))

            if self.current().type == 'EQUALS':
                self.advance()
                rhs = self.parse_rhs(left_type, line)
                if rhs[0] == 'single':
                    _, right, right_type = rhs
                    if right_type in ('NUMBER', 'NUMVAR'):
                        if len(left_operands) == 1:
                            statements.append(Statement('assignment', [left_angle, right], line=line))
                        else:
                            statements.append(Statement('sum_assignment', [left_operands, right], line=line))
                    elif right_type == 'ANGLE':
                        if len(left_operands) == 1:
                            statements.append(Statement('equality', [left_angle, right], line=line))
                        else:
                            statements.append(Statement('sum_equality', [left_operands, [('+', right)]], line=line))
                else:
                    _, right_operands = rhs
                    statements.append(Statement('sum_equality', [left_operands, right_operands], line=line))
            if self.current().type == 'INEQUALS':
                self.advance()
                if self.current().type not in ('ANGLE', 'NUMVAR'):
                    print(f"{line_val}\nSyntax Error on line {line}: Expected angle or numvar after '!='")
                    sys.exit(1)
                right = self.current().value
                self.advance()
                statements.append(Statement('inequality', [left_angle, right], line=line))

        elif self.current().type == 'NUMBER':
            left = self.current().value
            self.advance()
            left_operands = self.parse_sum_operands(left, ('NUMBER','ANGLE', 'IDENT'))

            if self.current().type == 'EQUALS':
                self.advance()
                rhs = self.parse_rhs(('NUMBER','ANGLE', 'IDENT'), line)
                if rhs[0] == 'single':
                    _, right, right_type = rhs
                    if right_type in ('NUMBER', 'NUMVAR'):
                        statements.append(Statement('sum_assignment', [left_operands, right], line=line))
                    elif right_type in ('IDENT', 'ANGLE'):
                        statements.append(Statement('sum_equality', [left_operands, [('+', right)]], line=line))
                else:
                    _, right_operands = rhs
                    statements.append(Statement('sum_equality', [left_operands, right_operands], line=line))

        else:
            self.advance()
        return statements

    def parse_rhs(self, allowed_types: Sequence[str], line: int) -> tuple:
        if self.current().type not in ('NUMBER', 'NUMVAR') and self.current().type not in allowed_types:
            print(self._err(line, f"Syntax Error: Unexpected token '{self.current().value}' after '='"))
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
                    print(self._err(line, f"Syntax Error: Expected {allowed_types}, number, or numvar after '+'/'-'"))
                    sys.exit(1)
                operands.append((sign, self.current().value))
                self.advance()
            return ('sum', operands)

        if first_type not in ('NUMBER', 'NUMVAR') and self.current().type in ('PLUS', 'MINUS'):
            rhs_operands = self.parse_sum_operands(first_val, allowed_types)
            return ('sum', rhs_operands)

        return ('single', first_val, first_type)
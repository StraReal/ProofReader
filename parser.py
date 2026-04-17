from common_classes import *

class Parser:
    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.pos = 0
        self.axioms: Dict[str, AxiomDefinition] = {}
        self.theorems: Dict[str, TheoremDefinition] = {}

    def current(self) -> Token:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else self.tokens[-1]

    def advance(self):
        self.pos += 1

    def parse(self) -> tuple[Dict[str, AxiomDefinition], Optional[HypothesisBlock], List[Statement], list]:
        hypothesis = None
        proofs = []

        while self.current().type != 'EOF':
            if self.current().type == 'AXIOM':
                axiom = self.parse_axiom()
                self.axioms[axiom.name] = axiom
            elif self.current().type == 'THEOREM':
                theorem = self.parse_theorem()
                self.theorems[theorem.name] = theorem
            elif self.current().type == 'IMPORT':
                self.advance()
                if self.current().type == 'IDENT':
                    return self.axioms, hypothesis, proofs, [self.current().value, self.current().line]
            elif self.current().type == 'HYPOTHESIS':
                self.advance()
                if self.current().type == 'COLON':
                    self.advance()
                hypothesis = self.parse_hypothesis_block()
            else:
                stmt = self.parse_statement()
                if stmt:
                    proofs.extend(stmt)

        return self.axioms, hypothesis, proofs, []

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
            print(f"Syntax Error: Expected axiom name")
            sys.exit(1)

        name = self.current().value
        self.advance()

        if self.current().type != 'COLON':
            print(f"Syntax Error: Expected ':' after axiom name")
            sys.exit(1)
        self.advance()

        if self.current().type != 'GIVEN':
            print(f"Syntax Error: Expected 'Given' in axiom")
            sys.exit(1)
        self.advance()
        if self.current().type == 'COLON':
            self.advance()

        given = self.parse_hypothesis_block(stop_tokens=['THEN'])

        if self.current().type != 'THEN':
            print(f"Syntax Error: Expected 'Then' in axiom")
            sys.exit(1)
        self.advance()
        if self.current().type == 'COLON':
            self.advance()

        then_statements = []
        while self.current().type not in ('AXIOM', 'HYPOTHESIS', 'PROOF', 'EOF'):
            stmts = self.parse_statement()
            if stmts:
                then_statements.extend(stmts)

        let_objects = []
        for stmt in given.statements:
            if stmt.type == 'let':
                let_objects.append(stmt.objects[0])

        return AxiomDefinition(name, given, then_statements, let_objects)

    def parse_statement(self) -> List[Statement]:
        statements = []
        line = self.current().line
        print(self.current().type, line)

        if self.current().type == 'IDENT' and self.pos + 1 < len(self.tokens) and self.tokens[
            self.pos + 1].type == 'LBRACE':
            axiom_name = self.current().value
            self.advance()
            self.advance()

            axiom = self.axioms[axiom_name]
            bindings = self.parse_axiom_bindings(axiom)

            if self.current().type != 'RBRACE':
                print(f"Syntax Error: Expected '}}' after axiom bindings")
                sys.exit(1)
            self.advance()

            if self.current().type == 'ARROW':
                self.advance()
                # follows conclusions (axioms, theorems) with =>
                conclusion = self.parse_statement()
                # return application and conclusion
                statements.append(Statement('axiom_application', [axiom_name], value=str(bindings), line=line))
                statements.extend(conclusion)

            return statements

        elif self.current().type == 'LET':
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
            if self.current().type == 'INEQUALS':
                self.advance()
                if self.current().type != 'IDENT':
                    print(f"Syntax Error on line {line}: Expected identifier after '!='")
                    sys.exit(1)
                right = self.current().value
                if len(right) != len(left):
                    print(
                        f"Syntax Error on line {line}: Only two objects with the same amount of points can be inequal (given {left}, {right})")
                    sys.exit(1)
                self.advance()
                statements.append(Statement('inequality', [left, right], line=line))

        elif self.current().type == 'ANGLE':
            left_angle = self.current().value
            self.advance()

            if self.current().type == 'EQUALS':
                self.advance()

                if self.current().type not in ('ANGLE', 'NUMBER'):
                    print(f"Syntax Error on line {line}: Expected number or angle after '{left_angle} ='")
                    sys.exit(1)
                right = self.current().value
                self.advance()
                statements.append(Statement('angle_equality', [left_angle, right], line=line))

        else:
            self.advance()

        return statements

    def parse_axiom_bindings(self, axiom: AxiomDefinition) -> Dict[str, str]:
        """Parse: identifier {, identifier}* and map to axiom's let objects"""
        bindings = {}
        provided_objects = []

        while self.current().type != 'RBRACE':
            if self.current().type == 'IDENT':
                provided_objects.append(self.current().value)
                self.advance()

                if self.current().type == 'COMMA':
                    self.advance()
            else:
                break

        # Match provided objects to axiom's let objects in order
        if len(provided_objects) != len(axiom.let_objects):
            print(f"Error: Axiom expects {len(axiom.let_objects)} objects, got {len(provided_objects)}")
            sys.exit(1)

        for axiom_obj, provided_obj in zip(axiom.let_objects, provided_objects):
            # Map each character: A->A, B->B, etc.
            for axiom_char, provided_char in zip(axiom_obj, provided_obj):
                bindings[axiom_char] = provided_char

        return bindings
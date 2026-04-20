from common_classes import *
from itertools import combinations

attributes = {}
op_map = {
            'PLUS': ('+', 2),
            'MINUS': ('-', 2),
            'ASSIGN': ('=', 0),
            'MULTIPLY': ('*', 3),
            'DIVIDE': ('/', 3),
            'EQUALS': ('equals', 1)
        }

class Parser:
    def __init__(self, tokens: List[Token], import_map: dict):
        self.tokens = tokens
        self.pos = 0
        self.axioms: Dict[str, AxiomDefinition] = {}
        self.theorems: Dict[str, TheoremDefinition] = {}
        self.import_map: dict = import_map
        self.operations = {}
        self.types = {}
        self.pending_attributes = {}

    def current(self) -> Token:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else self.tokens[-1]

    def advance(self):
        self.pos += 1

    def regress(self):
        self.pos -= 1

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

            elif self.current().type == 'AT':
                self.advance()  # @
                self.advance()  # [
                attr_name = self.current().value
                self.advance()
                attr_args = []
                while self.current().type != 'RBRACKET':
                    attr_args.append(self.current().value)
                    self.advance()
                self.advance()  # ]
                self.pending_attributes[attr_name] = attr_args

            elif self.current().type == 'OPERATION':
                op = self.parse_operation_definition()
                self.operations[(op.left_type, op.operator, op.right_type)] = (op.return_type, op.cases, op.attributes)
                ordered.append(('operation', op))

            elif self.current().type == 'TYPE':
                td = self.parse_type()
                self.types[td] = td
                ordered.append(('type', td))
            elif self.current().type == 'IMPORT':
                self.advance()
                if self.current().type == 'VARIABLE':
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
        if self.current().type != 'VARIABLE':
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
        while self.current().type not in ('PROOF', 'AXIOM', 'THEOREM', 'TYPE','OPERATION','HYPOTHESIS', 'EOF', 'AT'):
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

        if self.current().type != 'VARIABLE':
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
        while self.current().type not in ('PROOF', 'AXIOM', 'THEOREM', 'TYPE','OPERATION','HYPOTHESIS', 'EOF', 'AT'):
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
        while self.current().type not in ('PROOF', 'AXIOM', 'THEOREM', 'TYPE','OPERATION','HYPOTHESIS', 'EOF', 'AT'):
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

    def parse_operation_definition(self):
        self.advance()  # skip 'operation'

        left_type = self.current().value
        self.advance()

        line = self.current().line_num
        if self.types.get(left_type) is None:
            print_error(line, f"Syntax Error: Undefined type '{left_type}'",
                        self.import_map)
            sys.exit(1)

        operator = self.current().type  # PLUS, MINUS, MULTIPLY
        self.advance()

        right_type = self.current().value
        self.advance()

        line = self.current().line_num
        if self.types.get(left_type) is None:
            print_error(line, f"Syntax Error: Undefined type '{right_type}'",
                        self.import_map)
            sys.exit(1)

        return_type = None
        if self.current().type == 'ARROW_TYPE':
            self.advance()
            return_type = self.current().value
            self.advance()

        cases = []
        if self.current().type == 'COLON':
            self.advance()
            while self.current().type not in ('EOF', 'OPERATION', 'TYPE', 'THEOREM', 'AXIOM'):
                case = self.parse_statement()
                if case:
                    cases.extend(case)

        attributes = self.pending_attributes
        self.pending_attributes = {}
        return OperationDefinition(
            left_type=left_type,
            operator=operator,
            right_type=right_type,
            return_type=return_type,
            cases=cases,
            attributes=attributes,  # from @[...] if any
        )

    def parse_type(self):
        self.advance()  # skip 'type'

        name = self.current().value
        self.advance()

        constructors = []
        if self.current().type == 'COLON':
            self.advance()
            while self.current().type not in ('EOF', 'OPERATION', 'TYPE', 'THEOREM', 'AXIOM', 'HYPOTHESIS'):
                if self.current().type == 'VARIABLE':
                    constructor_name = self.current().value
                    self.advance()
                    args = []
                    if self.current().type == 'LPAR':
                        self.advance()
                        while self.current().type != 'RPAR':
                            args.append(self.current().value)
                            self.advance()
                            if self.current().type == 'COMMA':
                                self.advance()
                        self.advance()  # skip )
                    constructors.append((constructor_name, args))
                else:
                    self.advance()

        return name

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
        while self.current().type == 'ASSIGN':
            self.advance()
            rhs = self.parse_rhs(left_type, line)
            if rhs[0] == 'single':
                _, right, right_type = rhs
                sides.append((right, right_type))
            else:
                _, right_operands = rhs
                sides.append(right_operands)
        return sides

    def parse_expression(self, left):

        max_prec = 0
        operators = []
        operands = [left]

        while self.current().type in op_map:
            operators.append((self.current().type, op_map[self.current().type][1]))
            max_prec = max(max_prec, op_map[self.current().type][1])
            self.advance()
            if self.current().type == 'VARIABLE' or self.current().type.startswith('LIT'):
                operands.append((self.current().type, self.current().value))
            else:
                print_error(self.current().line_num, f"Unexpected value in expression: {self.current().value}", self.import_map)
            self.advance()

        if len(operands) != len(operators) + 1:
            print_error(self.current().line_num, f"Unexpected error",
                        self.import_map)

        if len(operators) == 0:
            return Expression(operator='pass', left=left, right=left, line=self.current().line_num)
        expr = None

        for i in range(max_prec, -1, -1):
            j = 0
            while j < len(operators):
                if operators[j][1] == i:
                    l = operands[j]
                    r = operands[j + 1]
                    expr = Expression(operator=operators[j][0], left=l, right=r, line=self.current().line_num)
                    operands[j] = expr
                    operands.pop(j + 1)
                    operators.pop(j)
                else:
                    j += 1
        return expr

    def parse_primary(self, val_type, value):
        """Parse a single operand (valued or variable)"""
        if val_type in ('INT', 'NAT','FLOAT','BOOL'):
            if value == 'true':
                value = True
            if value == 'false':
                value = False
            return val_type, value
        elif val_type == 'VARIABLE':
            return 'VARIABLE', value
        else:
            print_error(self.current().line, f"Expected operand, got {val_type}", self.import_map)
            sys.exit(1)

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

            statements.append(Statement('let', [obj], line=line))

            following = self.parse_statement()
            for s in following:
                if s.line == line:
                    s.in_let = True
            statements.extend(following)

        elif self.current().type == 'NUMVAR':
            left = self.current().value
            self.advance()
            left_operands = self.parse_sum_operands(left, ('NUMBER', 'IDENT', 'ANGLE', 'NUMVAR'))
            if self.current().type in ('ASSIGN', 'EQUALS'):
                sides = [(left_operands, None, None)]
                while self.current().type in ('ASSIGN', 'EQUALS'):
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

        elif self.current().type == 'VARIABLE':
            left_obj = self.current().value
            left_type = self.current().type
            self.regress()
            if self.current().type == 'LET':
                self.advance()
                self.advance()
                if self.current().type != 'COLON':
                    print_error(line, f"Syntax Error: must define variable type: {left_obj}",
                                self.import_map)
                    sys.exit(1)
                self.advance()
                if self.current().type != 'VARIABLE':
                    print_error(line, f"Syntax Error: must define variable type: {left_obj}",
                                self.import_map)
                    sys.exit(1)
                var_type = self.current().value
                if self.types.get(var_type) is None:
                    print_error(line, f"Syntax Error: Undefined type '{var_type}'",
                                self.import_map)
                    sys.exit(1)
                statements.append(Statement('typehint', [left_obj, var_type], line=line))
                make_operation = True
            elif self.current().type == 'COLON': #this is a type
                self.advance() # var (self)
                make_operation = False
            else:
                self.advance() # var (self)
                make_operation = True

            self.advance()  # next token
            if make_operation:
                expr = self.parse_expression((left_type, left_obj))
                self.regress()
                l = self.current().line
                self.advance()
                s = Statement('expression', [expr, l.strip()], line=self.current().line_num)
                statements.append(s)

        elif self.current().type == 'IDENT':
            left = self.current().value
            left_type = self.current().type
            self.advance()
            left_operands = self.parse_sum_operands(left, (left_type,))
            if self.current().type in ('ASSIGN', 'EQUALS'):
                sides = [(left_operands, None, None)]
                while self.current().type in ('ASSIGN', 'EQUALS'):
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

            elif self.current().type == 'INEQUALS':
                self.advance()
                if self.current().type not in ('IDENT', 'NUMVAR'):
                    print(f"{line_val}\nSyntax Error on line {line}: Expected identifier or numvar after '!='")
                    sys.exit(1)
                right = self.current().value
                self.advance()
                statements.append(Statement('equality', [left, right], line=line, goal=False))

            elif self.current().type == 'IN':
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

            elif self.current().type == 'CONTAINS':
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
            if self.current().type in ('ASSIGN', 'EQUALS'):
                sides = [(left_operands, None, None)]
                while self.current().type in ('ASSIGN', 'EQUALS'):
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
            if self.current().type in ('ASSIGN', 'EQUALS'):
                sides = [(left_operands, None, None)]
                while self.current().type in ('ASSIGN', 'EQUALS'):
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

        elif self.current().type.startswith('LIT'):
            left_type = self.current().type
            left_obj = self.current().value
            l = self.current().line
            self.advance()
            expr = self.parse_expression((left_type, left_obj))
            s = Statement('expression', [expr, l.strip()], line=self.current().line_num)
            statements.append(s)
            self.advance()

        elif self.current().type == 'PRINT':
            self.advance()
            statements.append(Statement('print', [self.current().value], line=line))
            self.advance()
        else:
            self.advance()
        while self.current().type == 'EQUALS':
            self.advance()
            if self.current().type == 'LITBOOL':
                goal = self.current().value == 'true'
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
from common_classes import *
from itertools import combinations

attributes = {}
OP_MAP = {  # Use https://docs.python.org/3/reference/expressions.html#operator-precedence for reference
            # TOKEN TYPE |      SYMBOL     | INFIX PREC,LEFT-ASS |  PREFIX PREC   | POSTFIX PREC
            'FIELDACCESS':Operator("'s ",    infix=(10, True)),
            'EXPONENT':   Operator('^',      infix=(9, True)),
            'MULTIPLY':   Operator('*',      infix=(7, True)),
            'DIVIDE':     Operator('/',      infix=(7, True)),
            'PLUS':       Operator('+',      infix=(6, True)),
            'MINUS':      Operator('-',      infix=(6, True) ,        prefix=8),
            'INEQUALS':   Operator('!=',     infix=(5, True)),
            'EQUALS':     Operator('equals', infix=(5, True)),
            'GETHAN':     Operator('>=',     infix=(5, True)),
            'LETHAN':     Operator('<=',     infix=(5, True)),
            'GREATERTHAN':Operator('>',      infix=(5, True)),
            'LESSTHAN':   Operator('<',      infix=(5, True)),
            'NOT':        Operator('not',                             prefix=4),
            'NAND':       Operator('nand',   infix=(3, True)),
            'AND':        Operator('and',    infix=(3, True)),
            'XOR':        Operator('xor',    infix=(2, True)),
            'NOR':        Operator('nor',    infix=(1, True)),
            'OR':         Operator('or',     infix=(1, True)),
            'ASSIGN':     Operator('=',      infix=(0, True)),
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
        self.last_precolon = None

    def current(self) -> Token:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else self.tokens[-1]

    def next(self) -> Token:
        return self.tokens[self.pos+1] if self.pos+1 < len(self.tokens) else self.tokens[-1]

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
                if op.left_type is None:
                    self.operations[(op.operator, op.right_type)] = (op.return_type, op.cases, op.attributes)
                else:
                    self.operations[(op.left_type, op.operator, op.right_type)] = (op.return_type, op.cases,
                                                                                   op.attributes)
                ordered.append(('operation', op))

            elif self.current().type == 'TYPE':
                td = self.parse_type()
                self.types[td[0]] = td[0]
                ordered.append(('type', td)) # name, aliases, accepts, matches
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

    def parse_hypothesis_block(self) -> HypothesisBlock:

        statements = []
        while self.current().type != 'DEDENT':
            stmt = self.parse_statement()
            if stmt:
                statements.extend(stmt)
        return HypothesisBlock(statements)

    def parse_axiom(self) -> AxiomDefinition:
        self.advance()  # skip 'axiom'

        self.last_precolon = self.current().type
        line = self.current().line_num
        if self.current().type != 'VARIABLE':
            print_error(line, f"Syntax Error: Expected axiom name", self.import_map)
            sys.exit(1)
        name = self.current().value

        self.advance()
        if self.current().type != 'COLON':
            print_error(line, f"Syntax Error: Expected colon after '{self.last_precolon}'", self.import_map)
        self.advance()
        if self.current().type == 'NEWLINE':
            self.advance()
        if self.current().type != 'INDENT':
            print_error(line, f"Syntax Error: Expected indented block after '{self.last_precolon}'", self.import_map)
            sys.exit(1)
        self.advance()

        if self.current().type != 'GIVEN':
            print_error(line, "Syntax Error: Expected 'Given' in axiom", self.import_map)
            sys.exit(1)

        self.last_precolon = self.current().type
        self.advance()
        if self.current().type != 'COLON':
            print_error(line, f"Syntax Error: Expected colon after '{self.last_precolon}'", self.import_map)
            sys.exit(1)
        self.advance()
        if self.current().type == 'NEWLINE':
            self.advance()
        if self.current().type != 'INDENT':
            print_error(line, f"Syntax Error: Expected indented block after '{self.last_precolon}'", self.import_map)
            sys.exit(1)
        self.advance()

        given = self.parse_hypothesis_block()
        self.advance()

        if self.current().type != 'THEN':
            print_error(line, "Syntax Error: Expected 'Then' in axiom", self.import_map)
            sys.exit(1)

        self.last_precolon = self.current().type
        self.advance()
        if self.current().type != 'COLON':
            print_error(line, f"Syntax Error: Expected colon after '{self.last_precolon}'", self.import_map)
        self.advance()
        if self.current().type == 'NEWLINE':
            self.advance()
        if self.current().type != 'INDENT':
            print_error(line, f"Syntax Error: Expected indented block after '{self.last_precolon}'", self.import_map)
            sys.exit(1)
        self.advance()

        then_statements = []
        while self.current().type != 'DEDENT':
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

        self.last_precolon = self.current().type
        self.advance()
        if self.current().type != 'COLON':
            print_error(line, f"Syntax Error: Expected colon after '{self.last_precolon}'", self.import_map)
        self.advance()
        if self.current().type == 'NEWLINE':
            self.advance()
        if self.current().type != 'INDENT':
            print_error(line, f"Syntax Error: Expected indented block after '{self.last_precolon}'", self.import_map)
            sys.exit(1)
        self.advance()

        if self.current().type != 'GIVEN':
            print_error(line, "Syntax Error: Expected 'Given' in theorem", self.import_map)
            sys.exit(1)

        self.last_precolon = self.current().type
        self.advance()
        if self.current().type != 'COLON':
            print_error(line, f"Syntax Error: Expected colon after '{self.last_precolon}'", self.import_map)
        self.advance()
        if self.current().type == 'NEWLINE':
            self.advance()
        if self.current().type != 'INDENT':
            print_error(line, f"Syntax Error: Expected indented block after '{self.last_precolon}'", self.import_map)
            sys.exit(1)
        self.advance()

        given = self.parse_hypothesis_block()
        self.advance()
        if self.current().type != 'THEN':
            print_error(line, "Syntax Error: Expected 'Then' in theorem", self.import_map)
            sys.exit(1)
        self.last_precolon = self.current().type
        self.advance()
        if self.current().type != 'COLON':
            print_error(line, f"Syntax Error: Expected colon after '{self.last_precolon}'", self.import_map)
        self.advance()
        if self.current().type == 'NEWLINE':
            self.advance()
        if self.current().type != 'INDENT':
            print_error(line, f"Syntax Error: Expected indented block after '{self.last_precolon}'", self.import_map)
            sys.exit(1)
        self.advance()

        then_statements = []
        while self.current().type != 'DEDENT':
            stmts = self.parse_statement()
            if stmts:
                then_statements.extend(stmts)
        self.advance()

        if self.current().type != 'PROOF':
            print_error(line, f"Syntax Error: Expected 'Proof' block in theorem '{name}'", self.import_map)
            sys.exit(1)
        self.advance()
        if self.current().type == 'COLON':
            self.advance()

        proof_statements = []
        while self.current().type != 'DEDENT':
            stmts = self.parse_statement()
            if stmts:
                proof_statements.extend(stmts)
        self.advance()
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

        first = self.current()
        self.advance()

        second = self.current()

        if second.type in OP_MAP:
            left_type = first.value
            operator = second.type
            self.advance()
            right_type = self.current().value
            self.advance()

            return_type = None
            if self.current().type == 'ARROW_TYPE':
                self.advance()
                return_type = self.current().value
                self.advance()
        else:
            operator = first.type
            right_type = second.value
            left_type = None
            self.advance()
            self.advance()
            return_type = self.current().value
            self.advance()

        cases = []
        self.advance()
        if self.current().type == 'INDENT':
            self.advance()
            while self.current().type != 'DEDENT':
                case = self.parse_statement()
                cases.extend(case)
            self.advance()  # skip DEDENT

        attributes = self.pending_attributes
        self.pending_attributes = {}

        return OperationDefinition(
            left_type=left_type,
            operator=operator,
            right_type=right_type,
            return_type=return_type,
            cases=cases,
            attributes=attributes,
        )

    def parse_type(self):
        self.advance()  # skip 'type'

        name = self.current().value
        self.advance()

        aliases = []

        # Optional single alias on the same line
        if self.current().value == 'alias':
            self.advance()
            aliases.append(self.current().value)
            self.advance()

        accepts = []
        matches = []

        if self.current().type == 'INDENT':
            self.advance()
            while self.current().type != 'DEDENT':
                if self.current().type == 'ALIAS':
                    self.advance()
                    aliases.append(self.current().value)
                    self.advance()
                elif self.current().type == 'ACCEPTS':
                    self.advance()
                    accepts.append(self.current().value)
                    self.advance()
                elif self.current().type == 'MATCHES':
                    self.advance()
                    matches.append(self.current().value)
                    self.advance()
                else:
                    self.advance()
            self.advance()  # skip DEDENT

        return name, aliases, accepts, matches

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

    def expr(self, prev_prec=-1):
        left = self.atom()
        while self.current().type in OP_MAP:
            op = self.current().type
            op_info = OP_MAP[op]
            if op_info.infix is None or op_info.infix[0] <= prev_prec:
                break
            prec, left_assoc = op_info.infix
            self.advance()
            left = Expression(op, left, self.expr(prec if left_assoc else prec - 1))
        return left

    def atom(self):
        tok = self.current()
        val_type = tok.type
        value = tok.value

        if val_type.startswith('LIT'):
            self.advance()
            return val_type, value



        elif val_type == 'VARIABLE':
            self.advance()
            return 'VARIABLE', value

        elif val_type in OP_MAP and OP_MAP[val_type].prefix is not None:
            self.advance()
            return Expression(val_type, self.expr(OP_MAP[val_type].prefix), 'none_for_unary', line=self.current().line_num)


        elif val_type == 'LPAR':
            self.advance()
            first = self.expr(-1)
            if self.current().type == 'COMMA':
                elements = [first]
                while self.current().type == 'COMMA':
                    self.advance()  # consume ','
                    elements.append(self.expr(-1))
                if self.current().type != 'RPAR':
                    print_error(tok.line_num, "Expected closing ')'", self.import_map)
                    sys.exit(1)
                self.advance()
                return 'TUPLE', elements
            else:
                if self.current().type != 'RPAR':
                    print_error(tok.line_num, "Expected closing ')'", self.import_map)
                    sys.exit(1)
                self.advance()
                return first

        else:
            print_error(tok.line_num, f"Expected operand, got {val_type}", self.import_map)
            sys.exit(1)

    def parse_statement(self) -> List[Statement]:
        statements = []
        line = self.current().line_num
        line_val = self.current().line

        if self.current().type == 'VARIABLE' and self.pos + 1 < len(self.tokens) and self.tokens[
            self.pos + 1].type == 'LBRACE':
            axiom_name = self.current().value
            self.advance()
            self.advance()

            raw_args = self.parse_axiom_bindings()

            if self.current().type != 'RBRACE':
                print(f"Syntax Error: Expected '}}' after axiom bindings")
                sys.exit(1)
            self.advance()
            if self.current().type == 'CONCL_ARROW':
                self.advance()
                conclusion = self.parse_statement()
                statements.append(Statement('axiom_application', [axiom_name], value=str(raw_args), line=line))
                statements.extend(conclusion)
            return statements



        elif self.current().type == 'LET':
            self.advance()
            name_type = self.current().type
            name = self.current().value
            self.advance()
            type_annotation = None
            value = None
            if name_type == 'VARIABLE':
                if self.current().type in ('COLON', 'BE'):
                    self.advance()
                    type_annotation = self.current().value
                    self.advance()
                if self.current().type == 'ASSIGN':
                    self.advance()
                    value = self.expr()
            statements.append(Statement('let', [(name_type, name)], value=value, line=line))
            if type_annotation is not None:
                statements.append(Statement('typehint', [name, type_annotation], line=line))

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
            self.regress()
            if self.current().type in ('COLON','BE'): #this is a type
                self.advance() # var (self)
                make_operation = False
            else:
                self.advance()
                make_operation = True

            if make_operation:
                expr = self.expr()
                self.regress()
                l = self.current().line
                self.advance()
                s = Statement('expression', [expr, l.strip()], line=self.current().line_num)
                statements.append(s)

        elif self.current().type in OP_MAP or self.current().type == 'LPAR':
            expr = self.expr()
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
                    if right_val is not None and right_type in ('LITINT', 'NUMVAR', 'LITNAT', 'LITFLOAT'):
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
                    if right_val is not None and right_type in  ('LITINT', 'NUMVAR', 'LITNAT', 'LITFLOAT'):
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
            l = self.current().line
            expr = self.expr()
            s = Statement('expression', [expr, l.strip()], line=self.current().line_num)
            statements.append(s)
            self.advance()

        elif self.current().type == 'PRINT':
            self.advance()
            statements.append(Statement('print', [self.current().value], line=line))
            self.advance()

        elif self.current().type == 'GIVES':
            self.advance()
            l = self.current().line
            expr = self.expr()
            self.regress()
            self.advance()
            s = Statement('gives', [expr, l.strip()], line=line)
            statements.append(s)

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

        if self.current().type == 'NEWLINE':
            self.advance()

        return statements

    def parse_rhs(self, allowed_types: Sequence[str], line: int) -> tuple:
        if self.current().type not in  ('LITINT', 'NUMVAR', 'LITNAT', 'LITFLOAT') and self.current().type not in allowed_types:
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
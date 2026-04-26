import re
from itertools import permutations

from common_classes import *
from externs import externs


class Validator:
    def __init__(self, import_map: dict):
        self.defined_objects: Set[str] = set()
        self.proof_defined_objects: Set[str] = set()
        self.operations = {}
        self.types = {}
        self.axioms: Dict[str, AxiomDefinition] = {}
        self.errors: List[str] = []
        self.class_values: Dict[frozenset, Optional[float]] = {}
        self.import_map: dict = import_map
        self.last_let_failed: bool = False
        self.last_axiom_failed: bool = False
        self.known_greater_than = set()
        self.known_contains = set()
        self.contradictory = False
        self.congruence_pools: Dict[int, Set[str]] = {}  # pool_id → set of ident names
        self._next_pool_id: int = 1
        self.aliases = {}

        self.variables: Dict[str, [str, any]] = {}

    def normalize_comparison(self, left_type, operator, right_type):

        if left_type > right_type:
            left_type, right_type = right_type, left_type

        return left_type, operator, right_type


    def validate(self, axioms: Dict[str, AxiomDefinition],
                 hypothesis: Optional[HypothesisBlock], ordered: List[Statement], proofs: List[Statement]) -> None:
        self.axioms = axioms

        for kind, item in ordered:
            if kind == 'axiom':
                pass
            elif kind == 'theorem':
                self.validate_theorem(item)
            elif kind == 'proof':
                self.process_statement(item, is_hypothesis=False)
            elif kind == 'operation':
                if item.left_type is None:
                    t = (item.operator, item.right_type)
                else:
                    t = self.normalize_comparison(item.left_type, item.operator, item.right_type)
                self.operations[t] = (item.return_type, item.cases, item.attributes)
            elif kind == 'type':
                self.types[item[0]] = item
                for alias in item[1]:
                    self.aliases[alias] = item[0]

        if hypothesis:
            for stmt in hypothesis.statements:
                self.process_statement(stmt, is_hypothesis=True)


        for stmt in proofs:
            self.process_statement(stmt, is_hypothesis=False)


    def validate_theorem(self, theorem: TheoremDefinition):
        child = Validator(self.import_map)
        child.axioms = self.axioms

        for stmt in theorem.given:
            child.process_statement(stmt, is_hypothesis=True)

        for stmt in theorem.proof:
            child.process_statement(stmt, is_hypothesis=False)

        # verify then is valid
        for then_stmt in theorem.then:
            child.process_statement(then_stmt, is_hypothesis=False)

        if child.errors:
            self.errors.append(f"Theorem '{theorem.name}' has a faulty proof:")
            for err in child.errors:
                self.errors.append(f"|| {err}")
            return

        # once verified, it's used exactly like an axiom
        self.axioms[theorem.name] = AxiomDefinition(
            theorem.name,
            theorem.given,
            theorem.then,
            theorem.let_objects,
            theorem.let_numvars
        )
        print(f"Theorem '{theorem.name}' proven and registered.")

    def normalize_object(self, unnorm_object: str) -> str:
        if re.match(r'^[xyz]_\d+$', unnorm_object):
            return unnorm_object
        try:
            float(unnorm_object)
            return unnorm_object
        except ValueError:
            if unnorm_object.startswith('ang'):
                angle = unnorm_object[3:]
                mid = angle[1]
                extremes = sorted(angle[0] + angle[2])
                angle = 'ang' + extremes[0] + mid + extremes[1]
                return angle
            else:
                return ''.join(sorted(unnorm_object))

    def _err(self, line, msg):
        file, lineno = self.get_infile_line(line)
        return f"{file} | Line {lineno}: {msg}"

    def get_infile_line(self, line_num):
        if line_num in self.import_map:
            filename, original_line = self.import_map[line_num]
            return (filename, original_line)
        else:
            return (None, line_num)

    def normalize_signed_sum(self, operands: List[tuple]) -> tuple:
        normalised = []
        for sign, name in operands:
            try:
                float(name)
                normalised.append((sign, name))  # keep numeric literals as-is
                continue
            except ValueError:
                pass
            norm_name = self.normalize_object(name)
            normalised.append((sign, norm_name))
        normalised.sort()
        return tuple(normalised)

    def resolve_sum_value(self, canonical_sum: tuple) -> Optional[float]:
        """
        Try to compute a numeric value for a canonical signed sum by looking up
        each term in known_equalities / class_values.
        Returns the float if every term resolves, otherwise None.
        """
        total = 0.0
        for sign, name in canonical_sum:
            term_class = self._find_sum_class(name)
            val = self.class_values.get(term_class)
            if val is None:
                return None
            total += val if sign == '+' else -val
        return total

    def get_equality_value(self, obj1, obj2, inequality=False):
        """
        Compare two objects for equality.
        Returns: 0 = equal/proven, 1 = unproven, 2 = false/contradictory
        Errors: 11 = obj1 undefined, 12 = obj2 undefined
        """

        val1 = self.evaluate_object(obj1)
        val2 = self.evaluate_object(obj2)

        if val1 is None:
            return 11
        if val2 is None:
            return 12

        if isinstance(val1, (int, float)) and isinstance(val2, (int, float)):
            if val1 == val2:
                return 0
            else:
                return 2

        if isinstance(val1, str) and isinstance(val2, str):
            return self._check_object_equality(val1, val2, inequality)

        if isinstance(val1, (int, float)) and isinstance(val2, str):
            return self._check_numeric_equality(val2, val1)
        if isinstance(val1, str) and isinstance(val2, (int, float)):
            return self._check_numeric_equality(val1, val2)

        return 1

    def evaluate_object(self, obj):
        """
        Evaluate an object to either:
        - A numeric value (int/float)
        - A normalized object string (for comparison)
        - None (undefined)
        """
        # man i hated doing this
        # case 1: single numeric value
        if isinstance(obj, (int, float)):
            return obj

        # case 2: object (angle/ident)
        if isinstance(obj, str):
            try:
                return float(obj)
            except ValueError:
                pass

            norm = self.normalize_object(obj)
            iter_norm = norm
            if obj.startswith('ang'):
                iter_norm = norm[3:]

            if not all(p in self.defined_objects for p in iter_norm):
                return None
            return norm

        # Case 3: sum (list of (sign, operand) tuples)
        if isinstance(obj, (list, tuple)):
            return self.evaluate_sum(obj)

        return None

    def evaluate_sum(self, operands):
        """
        Evaluate a sum of the form: [('+', 'AB'), ('-', 'CD'), ('+', '70')]

        Returns:
        - A float if all operands are numeric
        - A normalized canonical form if symbolic
        - None if any operand is undefined
        """
        total = 0
        all_numeric = True
        symbolic_parts = []

        for sign, operand in operands:
            sign_val = 1 if sign == '+' else -1

            # Try to parse as number
            try:
                num = float(operand)
                total += sign_val * num
                continue
            except ValueError:
                pass

            # It's a symbolic operand
            all_numeric = False
            norm = self.normalize_object(operand)
            if operand.startswith('ang'):
                norm = norm[3:]

            # Check if defined
            if not all(p in self.defined_objects for p in norm):
                return None

            symbolic_parts.append((sign, norm))

        # If everything is numeric, return the sum
        if all_numeric:
            return total

        # If we have symbolic parts, return the canonical form
        if symbolic_parts:
            return tuple(symbolic_parts)

        # Empty sum = 0
        return 0

    def resolve_numvar_binding(self, value: str) -> Optional[float]:
        try:
            return float(value)
        except ValueError:
            pass
        norm = self.normalize_object(value)
        obj_class = self._find_sum_class(norm)
        return self.class_values.get(obj_class)

    def substitute_variables(self, name, bindings):
        import re
        pattern = '|'.join(re.escape(k) for k in sorted(bindings.keys(), key=len, reverse=True))
        if not pattern:
            return name
        return re.sub(pattern, lambda m: bindings[m.group(0)], name)

    def _substitute_numeric_values(self, canon):
        result = []
        for sign, name in canon:
            try:
                float(name)
                result.append((sign, name))
                continue
            except (ValueError, TypeError):
                pass
            norm = self.normalize_object(name)
            cls = self._find_sum_class(norm)
            val = self.class_values.get(cls) if cls else None
            result.append((sign, str(val) if val is not None else norm))
        return result

    def _split_numeric_symbolic(self, canon):
        """
        Partition a signed-sum into a float total and a list of remaining
        symbolic (sign, name) pairs.
        """
        total = 0.0
        symbolic = []
        for sign, name in canon:
            try:
                v = float(name)
                total += v if sign == '+' else -v
            except ValueError:
                symbolic.append((sign, name))
        return total, symbolic

    def _concretize_statement(self, stmt, bindings):
        """Return a new Statement with all variables substituted with bindings."""
        if stmt.type in ('equality', 'inequality'):
            left = self.substitute_variables(stmt.objects[0], bindings)
            right = self.substitute_variables(stmt.objects[1], bindings)
            return Statement(stmt.type, [left, right], line=stmt.line, goal=stmt.goal)

        elif stmt.type == 'assignment':
            left = self.substitute_variables(stmt.objects[0], bindings)
            right = self.substitute_variables(stmt.objects[1], bindings)
            return Statement(stmt.type, [left, right], line=stmt.line, goal=stmt.goal)

        elif stmt.type in ('sum_assignment', 'sum_equality'):
            new_objects = []
            for obj in stmt.objects:
                if isinstance(obj, list):
                    new_objects.append([(s, self.substitute_variables(n, bindings)) for s, n in obj])
                else:
                    new_objects.append(self.substitute_variables(obj, bindings))
            return Statement(stmt.type, new_objects, line=stmt.line, goal=stmt.goal)

        elif stmt.type == 'contains':
            segment = self.substitute_variables(stmt.objects[0], bindings)
            point = self.substitute_variables(stmt.objects[1], bindings)
            return Statement(stmt.type, [segment, point], line=stmt.line, goal=stmt.goal)

        elif stmt.type == 'greater_than':
            left = self.substitute_variables(stmt.objects[0], bindings)
            right = self.substitute_variables(stmt.objects[1], bindings)
            return Statement(stmt.type, [left, right], line=stmt.line, goal=stmt.goal)

        elif stmt.type == 'let':
            obj = self.substitute_variables(stmt.objects[0], bindings)
            return Statement(stmt.type, [obj], line=stmt.line, goal=stmt.goal)

        elif stmt.type in ('true', 'false'):
            return Statement(stmt.type, stmt.objects, line=stmt.line, goal=stmt.goal)

        return stmt

    def call_extern(self, extern_name: str, left_value, right_value, line, ret_type):
        """Call an external function by name"""

        if extern_name in externs:
            extern_func = externs[extern_name]
            if left_value == 'true': left_value = True
            elif left_value == 'false': left_value = False
            if right_value == 'true': right_value = True
            elif right_value == 'false': right_value = False

            if left_value is None:
                res = extern_func(right_value)
            elif right_value is None:
                res = extern_func(left_value)
            else:
                res = extern_func(left_value, right_value)
            if res is True: res='true'
            if res is False: res='false'
            return ret_type, res
        else:
            self.errors.append(
                self._err(line, f"Unknown external function '{extern_name}'"))
            return None

    def _call_op(self, op_def, bindings):
        saved = {k: self.variables[k] for k in bindings if k in self.variables}
        self.variables.update(bindings)
        result = None
        try:
            for statement in op_def[1]:
                if isinstance(statement, Statement) and statement.type == 'gives':
                    result = self.solve_expression(statement)
                    break
                else:
                    self.solve_expression(statement, make_true=True)
        finally:
            for k in bindings:
                if k in saved:
                    self.variables[k] = saved[k]
                else:
                    self.variables.pop(k, None)
        return result

    def solve_expression(self, expression, make_true: bool = False) -> Expression | Tuple[str, any] | None:
        if isinstance(expression, tuple):
            val = expression[1]
            ex_type = expression[0]
            if ex_type.upper().startswith('LIT'):
                ex_type = ex_type[3:].capitalize()
            return ex_type, val
        if isinstance(expression, Statement):
            if expression.type == 'gives':
                expr_to_evaluate = expression.objects[0]
                return self.solve_expression(expr_to_evaluate, make_true)
            else:
                self.solve_expression(expression, make_true=True)
                return None

        if expression.operator == 'pass':
            return 'Bool', 'true'

        left = getattr(expression, 'left', None)
        right = getattr(expression, 'right', None)
        expr = expression
        operator = expression.operator

        if operator == 'ASSIGN' and isinstance(left, Expression) and left.operator == 'FIELDACCESS':
            tuple_name = left.left[1]
            field_name = left.right[1]
            t_var = self.variables.get(tuple_name)
            if t_var is None or t_var[0] != 'Namedtuple':
                self.errors.append(self._err(expr.line, f"'{tuple_name}' is not a namedtuple"))
                return None
            field = t_var[1].get(field_name)
            if field is None:
                self.errors.append(self._err(expr.line, f"No field '{field_name}' in '{tuple_name}'"))
                return None
            if make_true:
                right_val = self.solve_expression(right, make_true)
                field[0] = right_val[0]
                field[1] = right_val[1]
            return ('Bool', 'true')

        if operator == 'ASSIGN' and isinstance(left, Expression) and left.operator == 'INDEXACCESS':
            tuple_name = left.left[1]
            index = left.right[1]
            t_var = self.variables.get(tuple_name)
            if t_var is None or t_var[0] != 'Tuple':
                self.errors.append(self._err(expr.line, f"'{tuple_name}' is not a tuple"))
                return None
            if index < 0 or index >= len(t_var[1]):
                self.errors.append(self._err(expr.line, f"Index {index} out of range for '{tuple_name}'"))
                return None
            if make_true:
                right_val = self.solve_expression(right, make_true)
                t_var[1][index] = (right_val[0], right_val[1])
            return ('Bool', 'true')

        if operator == 'ASSIGN' and isinstance(left, tuple) and isinstance(right, tuple):
            if left[0] == 'VARIABLE' and right[0] == 'VARIABLE' and left[1].isupper() and right[1].isupper() and len(
                    left[1]) != 2:
                l_var = self.variables.get(left[1])
                r_var = self.variables.get(right[1])
                if l_var is None:
                    self.errors.append(self._err(expr.line, f"Undefined ident '{left[1]}'"))
                    return None
                if r_var is None:
                    self.errors.append(self._err(expr.line, f"Undefined ident '{right[1]}'"))
                    return None
                if make_true:
                    l_pool = l_var[1]['_congruence']
                    r_pool = r_var[1]['_congruence']
                    if l_pool != r_pool:
                        self.congruence_pools[l_pool].update(self.congruence_pools.pop(r_pool))
                        for ident in self.congruence_pools[l_pool]:
                            self.variables[ident][1]['_congruence'] = l_pool
                return 'Bool', 'true'

        if type(left) == Expression:
            left = self.solve_expression(expression.left, make_true)
            expression.left = left
        if type(right) == Expression:
            right = self.solve_expression(expression.right, make_true)
            expression.right = right

        if left is None:
            return None
        if right is None:
            return None

        if right == 'none_for_unary':
            if left[0] == 'VARIABLE':
                x_var = self.variables.get(left[1])
                if x_var is None:
                    self.errors.append(self._err(expr.line, f"Undefined variable '{left[1]}'."))
                    return None
                x_type = x_var[0]
                x_value = x_var[1]
            else:
                x_type = left[0].capitalize()
                if left[0].upper().startswith('LIT'):
                    x_type = x_type[3:].capitalize()
                x_value = left[1]

            if x_value is None:
                self.errors.append(self._err(expr.line, f"Cannot calculate expression with unknown (given: {left[1]})"))
                return None

            t = (operator, x_type)
            op_def = self.operations.get(t)
            if op_def is None:
                self.errors.append(self._err(expr.line, f"Operator {operator} is not defined for {x_type}"))
                return None

            if op_def[2]:
                extern_name = op_def[2]['extern'][0]
                return self.call_extern(extern_name, None, x_value, expr.line, op_def[0])
            else:
                result = self._call_op(op_def, {'first': [x_type, x_value]})
                if result is None:
                    self.errors.append(self._err(expr.line, f"Operation {operator} produced no result"))
                    return None
                return result

        if left[0] == 'VARIABLE':
            is_ident = left[1].isupper()
            is_angle = left[1].startswith('ang') and left[1][3:].isupper() and len(left[1]) > 3
            if (is_ident or is_angle) and operator != 'FIELDACCESS':
                left = left[0], self.normalize_object(left[1])
                name = left[1]
                l_var = self.variables.get(name)
                if l_var is None:
                    if is_angle or all(ch in self.variables for ch in left[1]):
                        l_var = self._create_ident(name)
                    else:
                        self.errors.append(self._err(expr.line, f"Undefined ident '{left[1]}'."))
                        return None
                l_type = l_var[0]
                left_value = l_var[1]
                if is_angle:
                    l_type = 'Int'
                    left_value = left_value['degrees'][1]
                else:
                    match len(name):
                        case 1:
                            l_type = 'special_type_pool'
                            left_value = self.congruence_pools[left_value['_congruent']]
                        case 2:
                            l_type = 'Int'
                            left_value = left_value['length'][1]
                        case n if n > 2:
                            l_type = 'special_type_pool'
                            left_value = self.congruence_pools[left_value['_congruent']]
            else:
                l_var = self.variables.get(left[1])
                if l_var is None:
                    self.errors.append(self._err(expr.line, f"Undefined variable '{left[1]}'."))
                    return None
                l_type = l_var[0]
                left_value = l_var[1]
        else:
            if operator == 'ASSIGN':
                self.errors.append(self._err(expr.line, f"Can't assign to literal {left[1]}."))
                return None
            l_type = left[0].capitalize()
            if left[0].upper().startswith('LIT'):
                l_type = l_type[3:].capitalize()
            left_value = left[1]

        if right[0] == 'VARIABLE':
            if operator == 'FIELDACCESS':
                if l_type != 'Namedtuple':
                    self.errors.append(self._err(expr.line, f"Can't access field of object of type {l_type}."))
                    return None
                field = left_value.get(right[1])
                if field is None:
                    self.errors.append(self._err(expr.line, f"Can't access field '{right[1]}' of object '{left[1]}'."))
                    return None
                return (field[0], field[1])
            elif operator == 'INDEXACCESS':
                if l_type != 'Tuple':
                    self.errors.append(self._err(expr.line, f"Can't access index of object of type {l_type}."))
                    return None
                index = right[1] - 1
                if index < 0 or index >= len(left_value):
                    self.errors.append(self._err(expr.line, f"Index {right[1]} out of range for '{left[1]}'."))
                    return None
                element = left_value[index]
                if element is None:
                    self.errors.append(self._err(expr.line, f"Can't access index {right[1]} of '{left[1]}'."))
                    return None
                return (element[0], element[1])
            else:
                is_ident = right[1].isupper()
                is_angle = right[1].startswith('ang') and right[1][3:].isupper() and len(right[1]) > 3
                if (is_ident or is_angle) and operator != 'FIELDACCESS':
                    right = right[0], self.normalize_object(right[1])
                    name = right[1]
                    r_var = self.variables.get(name)
                    if r_var is None:
                        if is_angle or all(ch in self.variables for ch in right[1]):
                            r_var = self._create_ident(name)
                        else:
                            self.errors.append(self._err(expr.line, f"Undefined ident '{right[1]}'."))
                            return None
                    r_type = r_var[0]
                    right_value = r_var[1]
                    if is_angle:
                        r_type = 'Int'
                        right_value = right_value['degrees'][1]
                    else:
                        match len(name):
                            case 1:
                                r_type = 'special_type_pool'
                                right_value = self.congruence_pools[right_value['_congruence']]
                            case 2:
                                r_type = 'Int'
                                right_value = right_value['length'][1]
                            case n if n > 2:
                                r_type = 'special_type_pool'
                                right_value = self.congruence_pools[right_value['_congruence']]
                else:
                    r_var = self.variables.get(right[1])
                    if r_var is None:
                        self.errors.append(self._err(expr.line, f"Undefined variable '{right[1]}'."))
                        return None
                    r_type = r_var[0]
                    right_value = r_var[1]
        else:
            r_type = right[0].capitalize()
            if right[0].upper().startswith('LIT'):
                r_type = r_type[3:].capitalize()
            right_value = right[1]

        if left_value is None or right_value is None:
            if operator != 'ASSIGN':
                both_unkn = left_value is None and right_value is None
                left_str = str(left[1]) if left_value is None else ''
                right_str = str(right[1]) if right_value is None else ''
                given_str = left_str + (', ' if both_unkn else '') + right_str
                self.errors.append(
                    self._err(expr.line, f"Cannot calculate expressions with unknowns (given: {given_str})"))
                return None

        if operator == 'ASSIGN':
            if self.types[l_type] is None and l_type != r_type:
                self.errors.append(self._err(expr.line, f"Cannot assign {r_type} to {l_type}"))
                return None
            if make_true:
                self.variables[left[1]][1] = right_value
            return 'Bool', 'true'
        elif operator == 'EQUALS':
            t = self.normalize_comparison(l_type, operator, r_type)
            op_def = self.operations.get(t)
            if op_def is None:
                if l_type == r_type:
                    return self.call_extern('eq_comp', left_value, right_value, expr.line, 'Bool')
                else:
                    self.errors.append(
                        self._err(expr.line, f"Operator {operator} is not defined for {l_type} and {r_type}"))
                    return None
            else:
                if op_def[2]:
                    extern_name = op_def[2]['extern'][0]
                    return self.call_extern(extern_name, left_value, right_value, expr.line, op_def[0])
                else:
                    self.variables['first'] = [l_type, left_value]
                    self.variables['second'] = [r_type, right_value]
                    result = None
                    try:
                        for statement in op_def[1]:
                            if isinstance(statement, Statement) and statement.type == 'gives':
                                result = self.solve_expression(statement)
                                break
                            else:
                                self.solve_expression(statement, make_true=True)
                    finally:
                        self.variables.pop('first', None)
                        self.variables.pop('second', None)
                    if result is None:
                        self.errors.append(self._err(expr.line, f"Operation {operator} produced no result"))
                        return None
                    return result
        else:
            t = self.normalize_comparison(l_type, operator, r_type)
            op_def = self.operations.get(t)
            if op_def is None:
                self.errors.append(
                    self._err(expr.line, f"Operator {operator} is not defined for {l_type} and {r_type}"))
                return None
            else:
                if op_def[2]:
                    extern_name = op_def[2]['extern'][0]
                    return self.call_extern(extern_name, left_value, right_value, expr.line, op_def[0])
                else:
                    result = self._call_op(op_def, {'first': [l_type, left_value], 'second': [r_type, right_value]})
                    if result is None:
                        self.errors.append(self._err(expr.line, f"Operation {operator} produced no result"))
                        return None
                    return result

    def _new_pool(self, ident_name: str) -> int:
        pid = self._next_pool_id
        self._next_pool_id += 1
        self.congruence_pools[pid] = {ident_name}
        return pid

    def _create_ident(self, name: str) -> list:
        name = self.normalize_object(name)
        if name.startswith('ang'):
            entry = ['Namedtuple', {'degrees': ['Int', None]}]
        else:
            pid = self._new_pool(name)
            match len(name):
                case 1:
                    entry = ['Namedtuple', {'_congruence': pid, 'radius': ['Int', None]}]
                case 2:
                    entry = ['Namedtuple', {'length': ['Int', None]}]
                case _:
                    entry = ['Namedtuple', {'_congruence': pid, 'area': ['Int', None], 'perimeter': ['Int', None]}]
        self.variables[name] = entry
        return entry

    def process_statement(self, stmt: Statement, is_hypothesis: bool):
        make_true = is_hypothesis or (stmt.in_let and not self.last_let_failed)
        if self.contradictory:
            return
        elif stmt.type == 'axiom_application':
            self.last_axiom_failed = not self.apply_axiom(stmt)
            return

        elif stmt.type == 'let':
            self.last_let_failed = False
            stmt_object = stmt.objects[0]
            value = stmt.value

            if stmt_object[0] == 'VARIABLE':
                def_type = None
                if value is not None:
                    if type(value) is tuple:
                        if value[0].startswith('LIT'):
                            def_type = value[0][3:].capitalize()
                            value = value[1]
                        elif value[0] == 'NAMEDTUPLE':
                            fields = {}
                            for field_expr in value[1]:
                                field_name = field_expr.left[1]
                                field_value = self.solve_expression(field_expr.right, make_true)
                                fields[field_name] = [field_value[0] if field_value else None,
                                                      field_value[1] if field_value else None]
                            self.variables[stmt_object[1]] = ['Namedtuple', fields]
                            return
                        elif value[0] == 'TUPLE':
                            fields = []
                            for field in value[1]:
                                field_value = self.solve_expression(field, make_true)
                                fields.append([field_value[0] if field_value else None,
                                               field_value[1] if field_value else None])
                            self.variables[stmt_object[1]] = ['Tuple', fields]
                            return
                    else:
                        value = self.solve_expression(value, make_true)
                if def_type is None:
                    def_type = value[0]
                self.variables[stmt_object[1]] = [def_type, value[1]]

            elif stmt_object[0] == 'IDENT':
                value_to_assign = None
                if value is not None:
                    if type(value) is tuple:
                        if value[0].startswith('LIT'):
                            value_to_assign = value[1]
                        else:
                            ref = self.variables.get(value[1])
                            if ref is None and value[1].isupper() and all(ch in self.variables for ch in value[1]):
                                ref = self._create_ident(value[1])
                            if ref is None:
                                self.errors.append(self._err(stmt.line, f"Undefined variable '{value[1]}'"))
                                return
                            value_to_assign = ref[1]
                    else:
                        resolved = self.solve_expression(value, make_true)
                        value_to_assign = resolved[1] if resolved else None

                ident = self._create_ident(stmt_object[1])

                if value_to_assign is not None:
                    if len(stmt_object[1]) == 2:
                        ident[1]['length'][1] = value_to_assign

            elif stmt_object[0] == 'ANGLE':
                value_to_assign = None
                if value is not None:
                    if type(value) is tuple:
                        if value[0].startswith('LIT'):
                            value_to_assign = value[1]
                        else:
                            ref = self.variables.get(value[1])
                            if ref is None and value[1].isupper() and all(ch in self.variables for ch in value[1]):
                                ref = self._create_ident(value[1])
                            if ref is None:
                                self.errors.append(self._err(stmt.line, f"Undefined variable '{value[1]}'"))
                                return
                            value_to_assign = ref[1]
                    else:
                        resolved = self.solve_expression(value, make_true)
                        value_to_assign = resolved[1] if resolved else None

                ident = self._create_ident(stmt_object[1])

                if value_to_assign is not None:
                    ident[1]['degrees'][1] = value_to_assign

            else:
                pass

        elif stmt.type == 'typehint':
            variable = stmt.objects[0]
            if stmt.objects[1] in self.types:
                o_type = stmt.objects[1]
                var = self.variables.get(variable)
                if var is None:
                    self.variables[variable] = [o_type, None]
                else:
                    var[0] = o_type
            else:
                if stmt.objects[1] in self.aliases:
                    o_type = self.aliases[stmt.objects[1]]
                    var = self.variables.get(variable)
                    if var is None:
                        self.variables[variable] = [o_type, None]
                    else:
                        var[0] = o_type
                else:
                    self.errors.append(self._err(stmt.line,
                                                 f"Undefined type '{stmt.objects[1]}'"))

        elif stmt.type == 'print':
            print(stmt.objects[0])
            return

        elif stmt.type == 'expression':
            res = self.solve_expression(stmt.objects[0], make_true)
            if res is not None:
                if res[0] == 'Bool':
                    if make_true:
                        if res[1] == 'false':
                            self.contradictory = True
                    else:
                        if res[1] == 'false':
                            self.errors.append(self._err(stmt.line,
                                                         f"'{stmt.objects[1]}' is false"))

        else:
            print(f"Unknown statement type {stmt.type}")

    def _build_bindings(self, axiom, raw_args):
        from itertools import permutations, product

        obj_args = raw_args[:len(axiom.let_objects)]
        num_args = raw_args[len(axiom.let_objects):]

        # Generate all permutations for each provided object
        perm_lists = [[''.join(p) for p in permutations(obj)] for obj in obj_args]

        for combo in product(*perm_lists):
            bindings = self._try_build_bindings(axiom, list(combo), num_args)
            if bindings is not None and self._check_bindings(axiom, bindings):
                return bindings

        return None

    def _try_build_bindings(self, axiom, obj_args, num_args):
        parent = {}

        def find(x):
            if x not in parent:
                parent[x] = x
            if parent[x] != x:
                parent[x] = find(parent[x])
            return parent[x]

        def union(x, y):
            px, py = find(x), find(y)
            if px != py:
                parent[px] = py

        axiom_to_provided = {}
        for axiom_obj, provided_obj in zip(axiom.let_objects, obj_args):
            for axiom_char, provided_char in zip(axiom_obj, provided_obj):
                if axiom_char in axiom_to_provided:
                    union(axiom_to_provided[axiom_char], provided_char)
                else:
                    axiom_to_provided[axiom_char] = provided_char

        bindings = {axiom_char: find(provided_char) for axiom_char, provided_char in axiom_to_provided.items()}
        for numvar, provided_num in zip(axiom.let_numvars, num_args):
            bindings[numvar] = provided_num

        return bindings

    def _check_bindings(self, axiom, bindings):
        """Check if bindings satisfy all given conditions. Returns True if all pass."""
        for hyp in axiom.given:
            if hyp.type == 'let':
                obj = hyp.objects[0]
                if obj in bindings:
                    concrete = bindings[obj]
                    if not all(p in self.defined_objects for p in concrete):
                        return False

            elif hyp.type == 'let_numvar':
                continue

            elif hyp.type == 'inequality':
                left = self.normalize_object(self.substitute_variables(hyp.objects[0], bindings))
                right = self.normalize_object(self.substitute_variables(hyp.objects[1], bindings))
                if not any(left in iq and right in iq for iq in self.known_inequalities):
                    return False

            elif hyp.type == 'sum_assignment':
                raw_ops = hyp.objects[0]
                concrete = [(s, self.substitute_variables(n, bindings)) for s, n in raw_ops]
                concrete = self._substitute_numeric_values(concrete)
                canon = self.normalize_signed_sum(concrete)
                expected = float(self.substitute_variables(hyp.objects[1], bindings))
                numeric, sym = self._split_numeric_symbolic(canon)
                net = expected - numeric
                if not sym:
                    if numeric != expected:
                        return False
                else:
                    key = tuple(sym)
                    cls = self._find_sum_class(key)
                    if self.class_values.get(cls) != net:
                        return False

            elif hyp.type == 'sum_equality':
                raw_left, raw_right = hyp.objects[0], hyp.objects[1]
                left_concrete = [(s, self.substitute_variables(n, bindings)) for s, n in raw_left]
                right_concrete = [(s, self.substitute_variables(n, bindings)) for s, n in raw_right]
                left_concrete = self._substitute_numeric_values(left_concrete)
                right_concrete = self._substitute_numeric_values(right_concrete)
                left_norm = self.normalize_signed_sum(left_concrete)
                right_norm = self.normalize_signed_sum(right_concrete)
                left_num, left_sym = self._split_numeric_symbolic(left_norm)
                right_num, right_sym = self._split_numeric_symbolic(right_norm)
                net_numeric = right_num - left_num
                flipped = [('+' if s == '-' else '-', n) for s, n in right_sym]
                combined_sym = tuple(sorted(tuple(left_sym) + tuple(flipped)))
                if not combined_sym:
                    if net_numeric != 0.0:
                        return False
                else:
                    cls = self._find_sum_class(combined_sym)
                    val = self.class_values.get(cls)
                    same_class = False
                    if net_numeric == 0.0:
                        lc = self._find_sum_class(tuple(left_sym))
                        rc = self._find_sum_class(tuple(right_sym))
                        same_class = (lc is not None and lc == rc)
                    if not same_class and (val is None or val != net_numeric):
                        return False

            elif hyp.type == 'contains':
                left = self.normalize_object(self.substitute_variables(hyp.objects[0], bindings))
                right = self.substitute_variables(hyp.objects[1], bindings)
                if (left, right) not in self.known_contains:
                    return False

            elif hyp.type in ('true', 'false'):
                if hyp.type == 'true' and not hyp.goal:
                    return False
                if hyp.type == 'false' and hyp.goal:
                    return False

        return True

    def apply_axiom(self, stmt: Statement):
        axiom_name = stmt.objects[0]
        raw_args = eval(stmt.value)
        line = stmt.line

        if axiom_name not in self.axioms:
            self.errors.append(self._err(line, f"Axiom '{axiom_name}' not defined"))
            return False

        axiom = self.axioms[axiom_name]

        if len(raw_args) != len(axiom.let_objects) + len(axiom.let_numvars):
            self.errors.append(self._err(line,
                                         f"Axiom '{axiom_name}' expects {len(axiom.let_objects)} object(s) "
                                         f"and {len(axiom.let_numvars)} numvar(s), got {len(raw_args)}"))
            return False

        bindings = self._build_bindings(axiom, raw_args)
        if bindings is None:
            self.errors.append(self._err(line,
                                         f"Axiom '{axiom_name}': no valid binding found for {raw_args}, conditions not satisfied"))
            return False

        # Resolve numvars to concrete floats
        for numvar in axiom.let_numvars:
            raw = bindings.get(numvar)
            if raw is None:
                self.errors.append(self._err(line, f"No binding provided for numvar '{numvar}'"))
                return False
            resolved = self.resolve_numvar_binding(raw)
            if resolved is None:
                self.errors.append(self._err(line, f"Cannot resolve numeric value for '{raw}' bound to '{numvar}'"))
                return False
            bindings[numvar] = str(int(resolved)) if resolved == int(resolved) else str(resolved)

        for thesis in axiom.then:
            concrete_stmt = self._concretize_statement(thesis, bindings)
            self.process_statement(concrete_stmt, is_hypothesis=True)

        return True
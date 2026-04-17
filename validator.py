import re

from common_classes import *

class Validator:
    def __init__(self, import_map: dict):
        self.defined_objects: Set[str] = set()
        self.known_equalities: Set[frozenset] = set()
        self.known_inequalities: Set[frozenset] = set()
        self.axioms: Dict[str, AxiomDefinition] = {}
        self.errors: List[str] = []
        self.class_values: Dict[frozenset, Optional[float]] = {}
        self.import_map: dict = import_map
        self.last_axiom_failed: bool = False

    def validate(self, axioms: Dict[str, AxiomDefinition], theorems: Dict[str, TheoremDefinition],
                 hypothesis: Optional[HypothesisBlock], proofs: List[Statement]):
        self.axioms = axioms

        for theorem in theorems.values():
            self.validate_theorem(theorem)

        if hypothesis:
            for stmt in hypothesis.statements:
                self.process_statement(stmt, is_hypothesis=True)
            self.propagate_transitivity()
            print(f"DEBUG: known_equalities = {self.known_equalities}")
            print(f"DEBUG: known_inequalities = {self.known_inequalities}")
            print(f"DEBUG: class_values = {self.class_values}")

        for stmt in proofs:
            self.process_statement(stmt, is_hypothesis=False)

    def validate_theorem(self, theorem: TheoremDefinition):
        child = Validator(self.import_map)
        child.axioms = self.axioms  # child can use all axioms (and already-proven theorems)

        # load the Given as hypothesis
        for stmt in theorem.given.statements:
            child.process_statement(stmt, is_hypothesis=True)
        child.propagate_transitivity()

        # test the proof
        for stmt in theorem.proof:
            child.process_statement(stmt, is_hypothesis=False)

        if child.errors:
            self.errors.append(f"Theorem '{theorem.name}' has a faulty proof:")
            for err in child.errors:
                self.errors.append(f"  {err}")
            return
        for then_stmt in theorem.then:
            result = None
            if then_stmt.type == 'equality':
                left = child.normalize_object(then_stmt.objects[0])
                right = child.normalize_object(then_stmt.objects[1])
                result = child.get_equality_value(left, right)
            elif then_stmt.type == 'inequality':
                left = child.normalize_object(then_stmt.objects[0])
                right = child.normalize_object(then_stmt.objects[1])
                result = child.get_equality_value(left, right, inequality=True)
            elif then_stmt.type == 'sum_assignment':
                canon = child.normalize_signed_sum(then_stmt.objects[0])
                expected = float(then_stmt.objects[1])
                result = child.get_equality_value(canon, expected, numeric_value=True)
            elif then_stmt.type == 'sum_equality':
                left_canon = child.normalize_signed_sum(then_stmt.objects[0])
                right_canon = child.normalize_signed_sum(then_stmt.objects[1])
                left_class = next((eq for eq in child.known_equalities if left_canon in eq), None)
                right_class = next((eq for eq in child.known_equalities if right_canon in eq), None)
                same_class = (left_class is not None and left_class == right_class)
                left_val = child.resolve_sum_value(left_canon)
                right_val = child.resolve_sum_value(right_canon)
                numeric_match = (left_val is not None and right_val is not None and left_val == right_val)
                result = 0 if (same_class or numeric_match) else 1

            if result not in (0, None):
                self.errors.append(
                    f"Theorem '{theorem.name}': Then conclusion '{then_stmt.objects}' "
                    f"is not established by the proof"
                )
                return

        self.axioms[theorem.name] = AxiomDefinition(
            theorem.name,
            theorem.given,
            theorem.then,
            theorem.let_objects,
            theorem.let_numvars
        )
        print(f"Theorem '{theorem.name}' proven and registered.")

    def normalize_object(self, unnorm_object: str) -> str:
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

    def normalize_sum(self, operands: list) -> tuple:
        operands.sort()
        return tuple(operands)

    def get_infile_line(self, line_num):
        if line_num in self.import_map:
            filename, original_line = self.import_map[line_num]
            return (filename, original_line)
        else:
            return (None, line_num)

    def merge_classes(self, class1: frozenset, class2: frozenset):
        val1 = self.class_values.get(class1)
        val2 = self.class_values.get(class2)

        if val1 is not None and val2 is not None and val1 != val2:
            self.errors.append(f"Numeric conflict: {val1} vs {val2}")
            return

        merged = class1 | class2
        self.known_equalities.discard(class1)
        self.known_equalities.discard(class2)
        self.known_equalities.add(merged)
        self.class_values[merged] = val1 or val2

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
            if norm_name.startswith('ang'):
                norm_name = norm_name[3:]
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
            term_class = next((eq for eq in self.known_equalities if name in eq), None)
            val = self.class_values.get(term_class)
            if val is None:
                return None
            total += val if sign == '+' else -val
        return total

    def propagate_transitivity(self):
        changed = True
        while changed:
            changed = False

            eq_list = list(self.known_equalities)
            for i, eq1 in enumerate(eq_list):
                for eq2 in eq_list[i + 1:]:
                    if eq1 & eq2:
                        val1 = self.class_values.get(eq1)
                        val2 = self.class_values.get(eq2)
                        if val1 is not None and val2 is not None and val1 != val2:
                            self.errors.append(f"Numeric conflict: {val1} vs {val2}")
                            return
                        union = eq1 | eq2
                        merged_val = val1 if val1 is not None else val2
                        self.known_equalities.discard(eq1)
                        self.known_equalities.discard(eq2)
                        self.known_equalities.add(union)
                        self.class_values[union] = merged_val
                        changed = True
                        break
                if changed:
                    break

            ineq_list = list(self.known_inequalities)
            for i, ineq1 in enumerate(ineq_list):
                for ineq2 in ineq_list[i + 1:]:
                    if ineq1 & ineq2:
                        union = ineq1 | ineq2
                        self.known_inequalities.discard(ineq1)
                        self.known_inequalities.discard(ineq2)
                        self.known_inequalities.add(union)
                        changed = True
                        break
                if changed:
                    break

            for eq_set in self.known_equalities:
                for ineq_set in self.known_inequalities:
                    if eq_set & ineq_set:
                        shared = eq_set & ineq_set
                        self.errors.append(f"'{shared}' are both equal and unequal")

            # Lazy resolution: try to assign numeric values to any sum stored
            # symbolically whose terms now all have known values
            for eq_class in list(self.known_equalities):
                if self.class_values.get(eq_class) is not None:
                    continue
                for member in eq_class:
                    if isinstance(member, tuple):  # its a canonical signed sum
                        resolved = self.resolve_sum_value(member)
                        if resolved is not None:
                            self.class_values[eq_class] = resolved
                            changed = True
                            break

    def process_statement(self, stmt: Statement, is_hypothesis: bool):
        if stmt.type == 'axiom_application':
            self.last_axiom_failed = not self.apply_axiom(stmt)
        if stmt.type == 'let':
            obj = stmt.objects[0]
            for p in list(obj):
                self.defined_objects.add(p)

        elif stmt.type == 'equality':
            left = self.normalize_object(stmt.objects[0])
            right = self.normalize_object(stmt.objects[1])
            result = self.get_equality_value(left, right)
            if result == 11:
                self.errors.append(
                    f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: Object '{left}' not defined")
                return
            if result == 12:
                self.errors.append(
                    f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: Object '{right}' not defined")
                return
            equality_pair = frozenset([left, right])
            if is_hypothesis:
                self.known_equalities.add(equality_pair)
            else:
                if result == 1:
                    self.errors.append(f"Line {stmt.line}: '{left} = {right}' is unproven")
                elif result == 2:
                    self.errors.append(f"Line {stmt.line}: '{left} = {right}' is false")

        elif stmt.type == 'inequality':
            left = self.normalize_object(stmt.objects[0])
            right = self.normalize_object(stmt.objects[1])
            result = self.get_equality_value(left, right, inequality=True)
            if result == 11:
                self.errors.append(
                    f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: Object '{left}' not defined")
                return
            if result == 12:
                self.errors.append(
                    f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: Object '{right}' not defined")
                return
            inequality_pair = frozenset([left, right])
            if is_hypothesis:
                self.known_inequalities.add(inequality_pair)
            else:
                if result == 1:
                    self.errors.append(
                        f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: '{left} != {right}' is unproven")
                elif result == 2:
                    self.errors.append(
                        f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: '{left} != {right}' is false")

        elif stmt.type == 'assignment':
            left = self.normalize_object(stmt.objects[0])
            right = stmt.objects[1]
            result = self.get_equality_value(left, float(right), numeric_value=True)
            if result == 11:
                self.errors.append(
                    f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: Object '{left}' not defined")
                return
            left_class = next((eq for eq in self.known_equalities if left in eq), None)
            if is_hypothesis:
                if left_class is None:
                    left_class = frozenset([left])
                    self.known_equalities.add(left_class)
                self.class_values[left_class] = float(right)
            else:
                if result == 1:
                    self.errors.append(
                        f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: '{left} = {right}' is unproven")
                elif result == 2:
                    self.errors.append(
                        f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: '{left} = {right}' is false")

        elif stmt.type == 'sum_assignment':
            # A signed sum equals a numeric literal: AB+CD-EF = 10
            left_operands = stmt.objects[0]  # list of (sign, name)
            right = float(stmt.objects[1])
            canon = self.normalize_signed_sum(left_operands)

            # Check all points are defined
            for _, name in canon:
                try:
                    float(name)
                    continue
                except ValueError:
                    pass
                norm = self.normalize_object(name) if not name.startswith('ang') else name
                if not all(p in self.defined_objects for p in norm):
                    self.errors.append(
                        f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: Object '{norm}' not defined")
                    return

            left_class = next((eq for eq in self.known_equalities if canon in eq), None)

            if is_hypothesis:
                if left_class is None:
                    left_class = frozenset([canon])
                    self.known_equalities.add(left_class)
                self.class_values[left_class] = right
            else:
                val = self.class_values.get(left_class)
                if val is None:
                    self.errors.append(
                        f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: '{canon} = {right}' is unproven")
                elif val != right:
                    self.errors.append(
                        f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: '{canon} = {right}' is false")

        elif stmt.type == 'sum_equality':
            # Two signed sums asserted equal: AB+CD-EF = GH-IJ
            left_operands, right_operands = stmt.objects[0], stmt.objects[1]
            left_canon = self.normalize_signed_sum(left_operands)
            right_canon = self.normalize_signed_sum(right_operands)

            # Check all points defined
            for canon in (left_canon, right_canon):
                for _, name in canon:
                    try:
                        float(name)
                        continue
                    except ValueError:
                        pass
                    norm = self.normalize_object(name) if not name.startswith('ang') else name
                    if not all(p in self.defined_objects for p in norm):
                        self.errors.append(
                            f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: Object '{norm}' not defined")
                        return

            left_val = self.resolve_sum_value(left_canon)
            right_val = self.resolve_sum_value(right_canon)

            if is_hypothesis:
                # If one side is fully numeric, assign the value to the other side
                if left_val is not None and right_val is None:
                    right_class = next((eq for eq in self.known_equalities if right_canon in eq), None)
                    if right_class is None:
                        right_class = frozenset([right_canon])
                        self.known_equalities.add(right_class)
                    self.class_values[right_class] = left_val
                elif right_val is not None and left_val is None:
                    left_class = next((eq for eq in self.known_equalities if left_canon in eq), None)
                    if left_class is None:
                        left_class = frozenset([left_canon])
                        self.known_equalities.add(left_class)
                    self.class_values[left_class] = right_val
                else:
                    # Both numeric: verify consistency; or neither: store symbolically
                    if left_val is not None and right_val is not None and left_val != right_val:
                        self.errors.append(
                            f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: Numeric conflict: {left_val} != {right_val}")
                        return
                    # Merge into the same equality class
                    left_class = next((eq for eq in self.known_equalities if left_canon in eq), frozenset([left_canon]))
                    right_class = next((eq for eq in self.known_equalities if right_canon in eq),
                                       frozenset([right_canon]))
                    self.known_equalities.discard(left_class)
                    self.known_equalities.discard(right_class)
                    merged = left_class | right_class
                    self.known_equalities.add(merged)
                    # Carry over any numeric value
                    merged_val = left_val if left_val is not None else right_val
                    if merged_val is not None:
                        self.class_values[merged] = merged_val
            else:
                # Proof context: verify the equality holds
                left_class = next((eq for eq in self.known_equalities if left_canon in eq), None)
                right_class = next((eq for eq in self.known_equalities if right_canon in eq), None)
                same_class = (left_class is not None and left_class == right_class)
                numeric_match = (left_val is not None and left_val == right_val)
                if not same_class and not numeric_match:
                    self.errors.append(
                        f"{self.get_infile_line(stmt.line)[0]} | Line {self.get_infile_line(stmt.line)[1]}: '{left_canon} = {right_canon}' is unproven")

    def get_equality_value(self, obj1, obj2, inequality=False, numeric_value=False):
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

        return 1  # Unproven

    def evaluate_object(self, obj):
        """
        Evaluate an object to either:
        - A numeric value (int/float)
        - A normalized object string (for comparison)
        - None (undefined)
        """
        # Case 1: Single numeric value
        if isinstance(obj, (int, float)):
            return obj

        if isinstance(obj, str):
            try:
                return float(obj)
            except ValueError:
                pass

            # It's an object reference
            norm = self.normalize_object(obj)
            if obj.startswith('ang'):
                norm = norm[3:]

            if not all(p in self.defined_objects for p in norm):
                return None
            return norm

        # Case 2: Sum (list of (sign, operand) tuples)
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

    def _check_object_equality(self, obj1, obj2, inequality=False):
        """Check if two object references are equal/unequal."""
        left_class = None
        right_class = None
        left_ineq_class = None
        right_ineq_class = None

        for eq_class in self.known_equalities:
            if obj1 in eq_class:
                left_class = eq_class
            if obj2 in eq_class:
                right_class = eq_class

        for ineq_class in self.known_inequalities:
            if obj1 in ineq_class:
                left_ineq_class = ineq_class
            if obj2 in ineq_class:
                right_ineq_class = ineq_class

        same_eq_class = (left_class is not None and right_class is not None and
                         left_class == right_class)
        same_ineq_class = (left_ineq_class is not None and right_ineq_class is not None and
                           left_ineq_class == right_ineq_class)

        if inequality:
            # For !=, they must be in different equality classes
            if same_eq_class:
                return 2  # False (they're equal)
            if same_ineq_class:
                return 0  # Proven (they're unequal)
            return 1  # Unproven
        else:
            # For =, they must be in same equality class
            if same_eq_class:
                return 0  # Proven
            if same_ineq_class:
                return 2  # False (they're unequal)
            return 1  # Unproven

    def _check_numeric_equality(self, obj, expected_value):
        """Check if an object equals an expected numeric value."""
        norm = self.normalize_object(obj)
        if obj.startswith('ang'):
            norm = norm[3:]

        left_class = None
        for eq_class in self.known_equalities:
            if norm in eq_class or obj in eq_class:
                left_class = eq_class
                break

        actual_value = self.class_values.get(left_class)

        if actual_value is None:
            return 1  # Unproven
        elif actual_value == expected_value:
            return 0  # Proven
        else:
            return 2  # False

    def flatten_value(self, value: Tuple[str, str]) -> float:
        sign, number = value
        result = float(number)
        return result if sign == '+' else -result


    def resolve_numvar_binding(self, value: str) -> Optional[float]:
        try:
            return float(value)
        except ValueError:
            pass
        norm = self.normalize_object(value)
        obj_class = next((eq for eq in self.known_equalities if norm in eq), None)
        return self.class_values.get(obj_class)

    def substitute_variables(self, template: str, bindings: Dict[str, str]) -> str:
        """
        Replace variables in template with concrete values.
        Numvars (x_1, y_2 etc.) are substituted as whole tokens before
        single-char point substitutions, to avoid partial matches.
        """
        result = template
        # Substitute numvars first (whole-token, longest keys first)
        for var in sorted(bindings.keys(), key=len, reverse=True):
            result = result.replace(var, bindings[var])
        return result

    def apply_axiom(self, stmt: Statement):
        axiom_name = stmt.objects[0]
        bindings = eval(stmt.value)
        line = stmt.line

        if axiom_name not in self.axioms:
            self.errors.append(
                f"{self.get_infile_line(line)[0]} | Line {self.get_infile_line(line)[1]}: Axiom '{axiom_name}' not defined")
            return False

        axiom = self.axioms[axiom_name]

        # Resolve numvar bindings
        for numvar in axiom.let_numvars:
            raw = bindings.get(numvar)
            if raw is None:
                self.errors.append(
                    f"{self.get_infile_line(line)[0]} | Line {self.get_infile_line(line)[1]}: No binding provided for numvar '{numvar}'")
                return False
            resolved = self.resolve_numvar_binding(raw)
            if resolved is None:
                self.errors.append(
                    f"{self.get_infile_line(line)[0]} | Line {self.get_infile_line(line)[1]}: Cannot resolve numeric value for '{raw}' bound to '{numvar}'")
                return False
            bindings[numvar] = str(int(resolved)) if resolved == int(resolved) else str(resolved)

        declared_objects = set(axiom.let_objects)
        defined_points = set()
        for dec_object in declared_objects:
            for point in dec_object:
                defined_points.add(point)

        all_statements = list(axiom.given.statements) + axiom.then
        for stmt_to_check in all_statements:
            type_item = stmt_to_check.type
            for obj in stmt_to_check.objects:
                if type_item in ('assignment', 'sum_assignment', 'sum_equality', 'let_numvar'):
                    continue
                if isinstance(obj, list):
                    continue
                if obj.startswith('ang'):
                    obj = obj[3:]
                if not obj:
                    continue
                for point in obj:
                    if point not in defined_points and not re.match(r'^[xyz]_\d+$', obj):
                        self.errors.append(f"Axiom '{axiom_name}': Point '{point}' in '{obj}' not declared")
                        return False

        for hyp_stmt in axiom.given.statements:
            if hyp_stmt.type == 'let':
                obj = hyp_stmt.objects[0]
                if obj in bindings:
                    concrete_obj = bindings[obj]
                    if not all(p in self.defined_objects for p in concrete_obj):
                        self.errors.append(
                            f"{self.get_infile_line(line)[0]} | Line {self.get_infile_line(line)[1]}: Axiom '{axiom_name}': object '{concrete_obj}' not defined")
                        return False

            elif hyp_stmt.type == 'let_numvar':
                continue

            elif hyp_stmt.type == 'equality':
                left = self.substitute_variables(hyp_stmt.objects[0], bindings)
                right = self.substitute_variables(hyp_stmt.objects[1], bindings)
                norm_left = self.normalize_object(left)
                norm_right = self.normalize_object(right)
                found = any(norm_left in eq and norm_right in eq for eq in self.known_equalities)
                if not found:
                    self.errors.append(
                        f"{self.get_infile_line(line)[0]} | Line {self.get_infile_line(line)[1]}: Axiom '{axiom_name}': condition '{norm_left} = {norm_right}' not satisfied")
                    return False

            elif hyp_stmt.type == 'inequality':
                left = self.substitute_variables(hyp_stmt.objects[0], bindings)
                right = self.substitute_variables(hyp_stmt.objects[1], bindings)
                norm_left = self.normalize_object(left)
                norm_right = self.normalize_object(right)
                found = any(norm_left in ineq and norm_right in ineq for ineq in self.known_inequalities)
                if not found:
                    self.errors.append(
                        f"{self.get_infile_line(line)[0]} | Line {self.get_infile_line(line)[1]}: Axiom '{axiom_name}': condition '{norm_left} != {norm_right}' not satisfied")
                    return False

            elif hyp_stmt.type == 'assignment':
                left = self.substitute_variables(hyp_stmt.objects[0], bindings)
                right = self.substitute_variables(hyp_stmt.objects[1], bindings)
                norm_left = self.normalize_object(left)
                left_class = next((eq for eq in self.known_equalities if norm_left in eq), None)
                actual = self.class_values.get(left_class)
                try:
                    expected = float(right)
                except ValueError:
                    expected = None
                if actual is None or actual != expected:
                    self.errors.append(
                        f"{self.get_infile_line(line)[0]} | Line {self.get_infile_line(line)[1]}: Axiom '{axiom_name}': condition '{norm_left} = {right}' not satisfied")
                    return False



            elif hyp_stmt.type == 'sum_assignment':

                raw_operands = hyp_stmt.objects[0]

                concrete_operands = [(sign, self.substitute_variables(name, bindings)) for sign, name in raw_operands]
                expected_str = hyp_stmt.objects[1]
                canon = self.normalize_signed_sum(concrete_operands)

                if expected_str in bindings:
                    expected = float(bindings[expected_str])
                else:
                    expected = float(expected_str)
                left_class = frozenset([canon])
                actual_value = self.class_values.get(left_class)
                if actual_value is None or actual_value != expected:
                    self.errors.append(
                        f"{self.get_infile_line(line)[0]} | Line {self.get_infile_line(line)[1]}: Axiom '{axiom_name}': condition '{canon} = {expected}' not satisfied")
                    return False

            elif hyp_stmt.type == 'sum_equality':
                raw_left, raw_right = hyp_stmt.objects[0], hyp_stmt.objects[1]
                concrete_left = [(sign, self.substitute_variables(name, bindings)) for sign, name in raw_left]
                concrete_right = [(sign, self.substitute_variables(name, bindings)) for sign, name in raw_right]
                left_val = self.evaluate_object(concrete_left)
                right_val = self.evaluate_object(concrete_right)
                if left_val is None or right_val is None:
                    self.errors.append(
                        f"{self.get_infile_line(line)[0]} | Line {self.get_infile_line(line)[1]}: Axiom '{axiom_name}': undefined object in condition")
                    return False
                result = self.get_equality_value(left_val, right_val)
                if result != 0:
                    self.errors.append(
                        f"{self.get_infile_line(line)[0]} | Line {self.get_infile_line(line)[1]}: Axiom '{axiom_name}': condition '{concrete_left} = {concrete_right}' not satisfied")
                    return False

        for thesis in axiom.then:
            if thesis.type == 'equality':
                left = self.substitute_variables(thesis.objects[0], bindings)
                right = self.substitute_variables(thesis.objects[1], bindings)
                self.known_equalities.add(frozenset([self.normalize_object(left), self.normalize_object(right)]))

            elif thesis.type == 'inequality':
                left = self.substitute_variables(thesis.objects[0], bindings)
                right = self.substitute_variables(thesis.objects[1], bindings)
                self.known_inequalities.add(frozenset([self.normalize_object(left), self.normalize_object(right)]))

            elif thesis.type == 'sum_assignment':
                raw_operands = thesis.objects[0]
                concrete_operands = [(sign, self.substitute_variables(name, bindings)) for sign, name in raw_operands]
                canon = self.normalize_signed_sum(concrete_operands)
                value = float(self.substitute_variables(thesis.objects[1], bindings))
                left_class = next((eq for eq in self.known_equalities if canon in eq), None)
                if left_class is None:
                    left_class = frozenset([canon])
                    self.known_equalities.add(left_class)
                self.class_values[left_class] = value


            elif thesis.type == 'sum_equality':
                raw_left, raw_right = thesis.objects[0], thesis.objects[1]
                concrete_left = [(sign, self.substitute_variables(name, bindings)) for sign, name in raw_left]
                concrete_right = [(sign, self.substitute_variables(name, bindings)) for sign, name in raw_right]
                left_val = self.evaluate_object(concrete_left)
                right_val = self.evaluate_object(concrete_right)
                left_canon = self.normalize_signed_sum(concrete_left)
                right_canon = self.normalize_signed_sum(concrete_right)
                if isinstance(left_val, (int, float)) and isinstance(right_val, (int, float)):
                    if left_val == right_val:
                        pass
                elif isinstance(left_val, (int, float)):
                    right_class = next((eq for eq in self.known_equalities if right_canon in eq),
                                       frozenset([right_canon]))
                    self.known_equalities.discard(right_class)
                    right_class = right_class | frozenset([left_val])
                    self.known_equalities.add(right_class)
                    self.class_values[right_class] = left_val
                elif isinstance(right_val, (int, float)):
                    left_class = next((eq for eq in self.known_equalities if left_canon in eq), frozenset([left_canon]))
                    self.known_equalities.discard(left_class)
                    left_class = left_class | frozenset([right_val])
                    self.known_equalities.add(left_class)
                    self.class_values[left_class] = right_val

                else:
                    left_class = next((eq for eq in self.known_equalities if left_canon in eq), frozenset([left_canon]))
                    right_class = next((eq for eq in self.known_equalities if right_canon in eq),
                                       frozenset([right_canon]))
                    self.known_equalities.discard(left_class)
                    self.known_equalities.discard(right_class)
                    merged = left_class | right_class
                    self.known_equalities.add(merged)
                    val = self.class_values.get(left_class) or self.class_values.get(right_class)
                    if val is not None:
                        self.class_values[merged] = val

        return True
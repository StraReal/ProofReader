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
        self.last_let_failed: bool = False
        self.last_axiom_failed: bool = False
        self.known_greater_than = set()
        self.known_contains = set()
        self.contradictory = False

    def validate(self, axioms: Dict[str, AxiomDefinition],
                 hypothesis: Optional[HypothesisBlock], ordered: List[Statement], proofs: List[Statement]) -> None:
        self.axioms = axioms

        if hypothesis:
            for stmt in hypothesis.statements:
                self.process_statement(stmt, is_hypothesis=True)
            self.propagate_transitivity()
            print("DEBUG: known_equalities: ", self.known_equalities)
            print("DEBUG: known_inequalities: ", self.known_inequalities)
            print("DEBUG: class_values: ", self.class_values)

        for kind, item in ordered:
            if kind == 'axiom':
                pass
            elif kind == 'theorem':
                self.validate_theorem(item)
            elif kind == 'proof':
                self.process_statement(item, is_hypothesis=False)
                self.propagate_transitivity()

        for stmt in proofs:
            self.process_statement(stmt, is_hypothesis=False)
        print("DEBUG: known_equalities: ", self.known_equalities)
        print("DEBUG: known_inequalities: ", self.known_inequalities)
        print("DEBUG: class_values: ", self.class_values)


    def validate_theorem(self, theorem: TheoremDefinition):
        child = Validator(self.import_map)
        child.axioms = self.axioms

        for stmt in theorem.given.statements:
            child.process_statement(stmt, is_hypothesis=True)
        child.propagate_transitivity()

        for stmt in theorem.proof:
            child.process_statement(stmt, is_hypothesis=False)
            child.propagate_transitivity()

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
                        merged_val = val1 if val1 is not None else val2
                        union = eq1 | eq2
                        self.known_equalities.discard(eq1)
                        self.known_equalities.discard(eq2)
                        self.class_values.pop(eq1, None)
                        self.class_values.pop(eq2, None)
                        self.known_equalities.add(union)
                        if merged_val is not None:
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

            for eq_class in list(self.known_equalities):
                if self.class_values.get(eq_class) is not None:
                    continue
                for member in eq_class:
                    if isinstance(member, tuple):
                        resolved = self.resolve_sum_value(member)
                        if resolved is not None:
                            self.class_values[eq_class] = resolved
                            changed = True
                            break

            for eq_class in list(self.known_equalities):
                val = self.class_values.get(eq_class)
                if val is None:
                    continue
                for member in eq_class:
                    if isinstance(member, str):
                        # Find if this string member is also in another class as a sum key
                        for other_class in list(self.known_equalities):
                            if other_class == eq_class:
                                continue
                            if member in other_class:
                                other_val = self.class_values.get(other_class)
                                if other_val is None:
                                    self.class_values.pop(other_class, None)
                                    merged = eq_class | other_class
                                    self.known_equalities.discard(eq_class)
                                    self.known_equalities.discard(other_class)
                                    self.known_equalities.add(merged)
                                    self.class_values[merged] = val
                                    changed = True
                                    break
                                elif other_val != val:
                                    self.errors.append(f"Numeric conflict: '{member}' = {val} vs {other_val}")
                                    return
                    if changed:
                        break
                if changed:
                    break

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

    def _check_object_equality(self, obj1, obj2, inequality=False):
        """Check if two object references are equal/unequal."""
        obj1 = self.normalize_object(obj1)
        obj2 = self.normalize_object(obj2)
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
            if same_eq_class:
                return 2
            if same_ineq_class:
                return 0
            return 1
        else:
            if same_eq_class:
                return 0
            if same_ineq_class:
                return 2
            return 1

    def _check_numeric_equality(self, obj, expected_value):
        """Check if an object equals an expected numeric value."""
        norm = self.normalize_object(obj)

        left_class = None
        for eq_class in self.known_equalities:
            if norm in eq_class or obj in eq_class:
                left_class = eq_class
                break

        actual_value = self.class_values.get(left_class)

        if actual_value is None:
            return 1
        elif actual_value == expected_value:
            return 0
        else:
            return 2

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

    def _check_defined(self, canon, line):
        """Return True if every named point in canon is in defined_objects, else append error."""
        for _, name in canon:
            try:
                float(name)
                continue
            except ValueError:
                pass
            if not re.match(r'^[xyz]_\d+$', name):
                norm = self.normalize_object(name)[3:] if name.startswith('ang') else self.normalize_object(name)
                if not all(p in self.defined_objects for p in norm):
                    self.errors.append(self._err(line, f"Object '{norm}' not defined"))
                    return False
        return True

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

    def _find_sum_class(self, key):
        if not isinstance(key, tuple) or not key or not isinstance(key[0], tuple):
            return next((eq for eq in self.known_equalities if key in eq), None)

        cls = next((eq for eq in self.known_equalities if key in eq), None)
        if cls is not None:
            return cls

        candidates = []
        for sign, name in key:
            alts = [name]
            for eq_class in self.known_equalities:
                if name in eq_class:
                    alts += [x for x in eq_class if isinstance(x, str) and x != name]
            candidates.append([(sign, alt) for alt in alts])

        from itertools import product
        for combo in product(*candidates):
            candidate_key = tuple(sorted(combo))
            cls = next((eq for eq in self.known_equalities if candidate_key in eq), None)
            if cls is not None:
                return cls

        return None

    def _store_sum(self, key, value):
        """
        Record  key = value  in known_equalities / class_values.
        key  : tuple of (sign, name), the canonical symbolic side
        value: float
        """
        cls = self._find_sum_class(key)
        if cls is None:
            cls = frozenset([key])
            self.known_equalities.add(cls)
        self.class_values[cls] = value

    def _store_sum_symbolic(self, left_key, right_key):
        """
        Record  left_key = right_key  with no numeric value yet —
        merge the two keys into one equality class.
        """
        left_cls = self._find_sum_class(left_key)
        right_cls = self._find_sum_class(right_key)

        if left_cls is None:
            left_cls = frozenset([left_key])
        if right_cls is None:
            right_cls = frozenset([right_key])

        self.known_equalities.discard(left_cls)
        self.known_equalities.discard(right_cls)
        merged = left_cls | right_cls
        self.known_equalities.add(merged)
        val = self.class_values.pop(left_cls, None) or self.class_values.pop(right_cls, None)
        if val is not None:
            self.class_values[merged] = val

    def _process_sum_assignment(self, stmt, is_hypothesis):
        """AB + CD = 50"""
        expected_str = "true" if stmt.goal else "false"
        canon = self.normalize_signed_sum(stmt.objects[0])
        right = float(stmt.objects[1])
        make_true = is_hypothesis or (stmt.in_let and not self.last_let_failed)
        if not self._check_defined(canon, stmt.line):
            return

        sub = self._substitute_numeric_values(canon)
        numeric, sym = self._split_numeric_symbolic(sub)
        net = right - numeric

        if not sym:
            ok = (numeric == right)
            if not ok:
                self.errors.append(
                    self._err(stmt.line, f"'{canon} = {right} is {expected_str}' is {'false' if not is_hypothesis else 'conflicting'}"))
            return

        key = tuple(sym)
        if make_true:
            self._store_sum(key, net)
            # Link single named object to the sum class
            if len(sym) == 1 and sym[0][0] == '+':
                name = sym[0][1]
                cls = self._find_sum_class(key)
                if cls is not None:
                    self.known_equalities.discard(cls)
                    new_cls = cls | frozenset([name])
                    self.known_equalities.add(new_cls)
                    self.class_values.pop(cls, None)
                    self.class_values[new_cls] = net
        else:
            cls = self._find_sum_class(key)
            val = self.class_values.get(cls)
            matches = (val is not None and val == net)
            if matches == stmt.goal:
                if len(sym) == 1 and sym[0][0] == '+':
                    name = sym[0][1]
                    self.known_equalities.discard(cls)
                    new_cls = cls | frozenset([name])
                    self.known_equalities.add(new_cls)
                    self.class_values.pop(cls, None)
                    self.class_values[new_cls] = val
            else:
                if val is None:
                    self.errors.append(self._err(stmt.line, f"'{key} = {net} is {expected_str}' is unproven"))
                else:
                    self.errors.append(self._err(stmt.line,
                                                 f"'{key} = {net} is {expected_str}' is false"))

    def _canonicalize_sum_key(self, key):
        """Replace each term in a sum key with the canonical representative of its equality class."""
        result = []
        for sign, name in key:
            # Find if this name is in any equality class with another sum key member
            canonical = name
            for eq_class in self.known_equalities:
                if name in eq_class:
                    # Use the lexicographically smallest member as canonical
                    candidates = [x for x in eq_class if isinstance(x, str)]
                    if candidates:
                        canonical = min(candidates)
                    break
            result.append((sign, canonical))
        return tuple(sorted(result))

    def _process_sum_equality(self, stmt, is_hypothesis):
        """AB + CD = EF - GH"""
        left_canon = self.normalize_signed_sum(stmt.objects[0])
        right_canon = self.normalize_signed_sum(stmt.objects[1])
        make_true = is_hypothesis or (stmt.in_let and not self.last_let_failed)

        if not self._check_defined(left_canon, stmt.line): return
        if not self._check_defined(right_canon, stmt.line): return

        left_sub = self._substitute_numeric_values(left_canon)
        right_sub = self._substitute_numeric_values(right_canon)
        left_num, left_sym = self._split_numeric_symbolic(left_sub)
        right_num, right_sym = self._split_numeric_symbolic(right_sub)

        # Bring all numerics to the right:
        #   left_sym - right_sym = right_num - left_num
        net_numeric = right_num - left_num
        flipped_right = [('+' if s == '-' else '-', n) for s, n in right_sym]
        combined_sym = tuple(left_sym) + tuple(flipped_right)

        if not combined_sym:
            ok = (net_numeric == 0.0)
            if not (ok == stmt.goal):
                expected_str = "true" if stmt.goal else "false"
                self.errors.append(self._err(stmt.line,
                                             f"'{left_canon} = {right_canon}' is {'true' if ok else 'false'}, expected {expected_str}"))
            return

        if combined_sym[0][0] == '-':
            combined_sym = tuple(sorted(('+' if s == '-' else '-', n) for s, n in combined_sym))
            net_numeric = -net_numeric
        else:
            combined_sym = tuple(sorted(combined_sym))
        combined_sym = self._canonicalize_sum_key(combined_sym)

        left_key = tuple(left_sym)
        right_key = tuple(right_sym)

        if make_true:
            if not left_sym and right_sym:
                self._store_sum(right_key, -net_numeric)
            elif left_sym and not right_sym:
                self._store_sum(left_key, net_numeric)
            else:
                self._store_sum_symbolic(left_key, right_key)
        else:
            cls = self._find_sum_class(combined_sym)
            val = self.class_values.get(cls)
            if val is not None:
                matches = (val == net_numeric)
                if matches == stmt.goal:
                    if len(left_sym) == 1 and left_sym[0][0] == '+' and not right_sym:
                        name = left_sym[0][1]
                        self.known_equalities.discard(cls)
                        new_cls = cls | frozenset([name])
                        self.known_equalities.add(new_cls)
                        self.class_values.pop(cls, None)
                        self.class_values[new_cls] = val
                    return
                else:
                    expected_str = "true" if stmt.goal else "false"
                    self.errors.append(self._err(stmt.line,
                                                 f"'{left_canon} = {right_canon}' is {'true' if matches else 'false'}, expected {expected_str}"))
            elif net_numeric == 0.0:
                lc = self._find_sum_class(tuple(left_sym))
                rc = self._find_sum_class(tuple(right_sym))
                if (lc is not None and lc == rc) == stmt.goal:
                    return
                self.errors.append(self._err(stmt.line,
                                             f"'{left_canon} = {right_canon}' is unproven as {'true' if stmt.goal else 'false'}"))
            else:
                self.errors.append(self._err(stmt.line,
                                             f"'{left_canon} = {right_canon}' is unproven as {'true' if stmt.goal else 'false'}"))

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
        return stmt

    def process_statement(self, stmt: Statement, is_hypothesis: bool):
        make_true = is_hypothesis or (stmt.in_let and not self.last_let_failed)
        if self.contradictory:
            return
        if stmt.type == 'axiom_application':
            self.last_axiom_failed = not self.apply_axiom(stmt)
            return

        if stmt.type == 'let':
            for p in list(stmt.objects[0]):
                if not is_hypothesis and p in self.defined_objects:
                    self.errors.append(self._err(stmt.line, f"Point '{p}' already defined"))
                    self.last_let_failed = True
                    return
                self.defined_objects.add(p)
                self.last_let_failed = False
            return

        if stmt.type == 'chain_conclusion':
            left_ops, right_ops, right_type, right_val = stmt.objects
            if right_val is not None and right_type in ('NUMBER', 'NUMVAR'):
                if len(left_ops) == 1:
                    left_class = next((eq for eq in self.known_equalities if left_ops[0][1] in eq), None)
                    if left_class is None:
                        left_class = frozenset([left_ops[0][1]])
                        self.known_equalities.add(left_class)
                    self.class_values[left_class] = float(right_val)
                else:
                    self._store_sum(tuple(left_ops), float(right_val))
            else:
                if len(left_ops) == 1 and len(right_ops) == 1:
                    left_name = self.normalize_object(left_ops[0][1])
                    right_name = self.normalize_object(right_ops[0][1])
                    self.known_equalities.add(frozenset([left_name, right_name]))
                else:
                    self._store_sum_symbolic(tuple(left_ops), tuple(right_ops))
            return

        if stmt.type == 'contains':
            segment = stmt.objects[0]
            point = stmt.objects[1]
            if is_hypothesis:
                self.known_contains.add((segment, point))
            else:
                if (segment, point) not in self.known_contains and point not in segment:
                    self.errors.append(self._err(stmt.line, f"'{point} in {segment}' is unproven"))

        if stmt.type == 'equality':
            left = self.normalize_object(stmt.objects[0])
            right = self.normalize_object(stmt.objects[1])
            result = self.get_equality_value(left, right)
            pair = frozenset([left, right])
            expected_str = "true" if stmt.goal else "false"

            if result == 11:
                self.errors.append(self._err(stmt.line, f"Object '{left}' not defined"))
                return
            if result == 12:
                self.errors.append(self._err(stmt.line, f"Object '{right}' not defined"))
                return

            if make_true:
                if stmt.goal:
                    self.known_equalities.add(pair)
                else:
                    self.known_inequalities.add(pair)
            else:
                if result == 1: self.errors.append(self._err(stmt.line, f"'{left} = {right} is {'true' if stmt.goal else 'false'}' is unproven"))
                elif bool(result) == stmt.goal : self.errors.append(self._err(stmt.line, f"'{left} = {right}' is {'false' if stmt.goal else 'true'}, expected {expected_str}"))
            return

        if stmt.type == 'assignment':
            left = self.normalize_object(stmt.objects[0])
            right = stmt.objects[1]
            result = self.get_equality_value(left, float(right))
            if result == 11:
                self.errors.append(self._err(stmt.line, f"Object '{left}' not defined"))
                return

            left_class = self._find_sum_class(left)
            if make_true:
                if left_class is None:
                    left_class = frozenset([left])
                    self.known_equalities.add(left_class)
                self.class_values[left_class] = float(right)
            else:
                if result == 1: self.errors.append(self._err(stmt.line, f"'{left} = {right} is {'true' if stmt.goal else 'false'}' is unproven"))
                elif bool(result) == stmt.goal: self.errors.append(self._err(stmt.line, f"'{left} = {right} is {'true' if stmt.goal else 'false'}' is false"))
            return

        if stmt.type == 'sum_assignment':
            self._process_sum_assignment(stmt, is_hypothesis)
            return

        if stmt.type == 'sum_equality':
            self._process_sum_equality(stmt, is_hypothesis)
            return

        if stmt.type == 'print':
            print(stmt.objects[0])
            return

        if stmt.type == 'true':
            if make_true:
                if not stmt.goal:
                    self.contradictory = True
            else:
                if not stmt.goal:
                    self.errors.append(self._err(stmt.line, f"'{stmt.objects} is {'false' if stmt.objects == 'true' else 'true'}' was disproven"))
            return


    def apply_axiom(self, stmt: Statement):
        axiom_name = stmt.objects[0]
        raw_args   = eval(stmt.value)
        raw_args = [self.normalize_object(a) for a in raw_args]
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

        a_binds = []
        p_binds = []
        for axiom_obj, provided_obj in zip(axiom.let_objects, raw_args[:len(axiom.let_objects)]):
            axiom_obj, provided_obj = self.normalize_object(axiom_obj), self.normalize_object(provided_obj)
            for axiom_char in axiom_obj:
                if axiom_char not in a_binds:
                    a_binds.append(axiom_char)
            for provided_char in provided_obj:
                if provided_char not in p_binds:
                    p_binds.append(provided_char)

        bindings = dict(zip(a_binds, p_binds))

        for numvar, provided_num in zip(axiom.let_numvars, raw_args[len(axiom.let_objects):]):
            bindings[numvar] = provided_num

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

        declared_points = {p for obj in axiom.let_objects for p in obj}
        for s in list(axiom.given.statements) + axiom.then:
            if s.type in ('assignment', 'sum_assignment', 'sum_equality', 'let_numvar', 'true'):
                continue
            for obj in s.objects:
                if isinstance(obj, list):
                    continue
                raw = obj[3:] if obj.startswith('ang') else obj
                if not raw:
                    continue
                for point in raw:
                    if point not in declared_points and not re.match(r'^[xyz]_\d+$', raw):
                        self.errors.append(f"Axiom '{axiom_name}': point '{point}' in '{raw}' not declared")
                        return False

        def concretize(operands):
            """(sign, name) list > substitute bindings > substitute numeric values."""
            with_bindings = [(s, self.substitute_variables(n, bindings)) for s, n in operands]
            return self._substitute_numeric_values(with_bindings)

        for hyp in axiom.given.statements:
            if hyp.type == 'let':
                obj = hyp.objects[0]
                if obj in bindings:
                    concrete = bindings[obj]
                    if not all(p in self.defined_objects for p in concrete):
                        self.errors.append(self._err(line, f"Axiom '{axiom_name}': object '{concrete}' not defined"))
                        return False

            elif hyp.type == 'let_numvar':
                continue

            elif hyp.type == 'equality':
                left = self.normalize_object(self.substitute_variables(hyp.objects[0], bindings))
                right = self.normalize_object(self.substitute_variables(hyp.objects[1], bindings))
                if not any(left in eq and right in eq for eq in (self.known_equalities if hyp.goal else self.known_inequalities)):
                    self.errors.append(
                        self._err(line, f"Axiom '{axiom_name}': condition '{left} = {right} is {'true' if hyp.goal else 'false'}' not satisfied"))
                    return False

            elif hyp.type == 'contains':
                left = self.normalize_object(self.substitute_variables(hyp.objects[0], bindings))
                right = self.normalize_object(self.substitute_variables(hyp.objects[1], bindings))
                if (left, right) not in self.known_contains and right not in left:
                    self.errors.append(
                        self._err(line, f"Axiom '{axiom_name}': condition '{left} contains {right}' not satisfied"))
                    return False

            elif hyp.type == 'assignment':
                left = self.normalize_object(self.substitute_variables(hyp.objects[0], bindings))
                expected = float(self.substitute_variables(hyp.objects[1], bindings))
                cls = self._find_sum_class(left)
                if self.class_values.get(cls) != expected:
                    self.errors.append(
                        self._err(line, f"Axiom '{axiom_name}': condition '{left} = {expected}' not satisfied"))
                    return False

            elif hyp.type == 'sum_assignment':
                raw_ops = hyp.objects[0]
                concrete = concretize(raw_ops)
                canon = self.normalize_signed_sum(concrete)
                expected = float(self.substitute_variables(hyp.objects[1], bindings))

                numeric, sym = self._split_numeric_symbolic(canon)
                net = expected - numeric  # what the symbolic part must equal

                if not sym:
                    if numeric != expected:
                        self.errors.append(
                            self._err(line, f"Axiom '{axiom_name}': condition '{canon} = {expected}' not satisfied"))
                        return False
                else:
                    key = tuple(sym)
                    cls = self._find_sum_class(key)
                    if self.class_values.get(cls) != net:
                        self.errors.append(
                            self._err(line, f"Axiom '{axiom_name}': condition '{key} = {net}' not satisfied"))
                        return False

            elif hyp.type == 'sum_equality':
                left_concrete = concretize(hyp.objects[0])
                right_concrete = concretize(hyp.objects[1])
                left_norm = self.normalize_signed_sum(left_concrete)
                right_norm = self.normalize_signed_sum(right_concrete)

                left_num, left_sym = self._split_numeric_symbolic(left_norm)
                right_num, right_sym = self._split_numeric_symbolic(right_norm)
                net_numeric = right_num - left_num

                flipped = [('+' if s == '-' else '-', n) for s, n in right_sym]
                combined_sym = tuple(left_sym) + tuple(flipped)

                if not combined_sym:
                    if net_numeric != 0.0:
                        self.errors.append(self._err(line, f"Axiom '{axiom_name}': numeric conflict in condition"))
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
                        self.errors.append(self._err(line, f"Axiom '{axiom_name}': condition not satisfied"))
                        return False

            elif hyp.type == 'true':
                if not hyp.goal:
                    return True

        for thesis in axiom.then:
            concrete_stmt = self._concretize_statement(thesis, bindings)
            self.process_statement(concrete_stmt, is_hypothesis=True)

        return True
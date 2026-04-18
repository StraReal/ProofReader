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
        child.axioms = self.axioms

        for stmt in theorem.given.statements:
            child.process_statement(stmt, is_hypothesis=True)
        child.propagate_transitivity()

        for stmt in theorem.proof:
            child.process_statement(stmt, is_hypothesis=False)

        if child.errors:
            self.errors.append(f"Theorem '{theorem.name}' has a faulty proof:")
            for err in child.errors:
                self.errors.append(f"  {err}")
            return

        # Verify every 'then' conclusion is established by the proof
        for then_stmt in theorem.then:

            if then_stmt.type == 'equality':
                left = child.normalize_object(then_stmt.objects[0])
                right = child.normalize_object(then_stmt.objects[1])
                result = child.get_equality_value(left, right)
                if result != 0:
                    self.errors.append(
                        f"Theorem '{theorem.name}': conclusion '{left} = {right}' was not proven")
                    return

            elif then_stmt.type == 'inequality':
                left = child.normalize_object(then_stmt.objects[0])
                right = child.normalize_object(then_stmt.objects[1])
                result = child.get_equality_value(left, right, inequality=True)
                if result != 0:
                    self.errors.append(
                        f"Theorem '{theorem.name}': conclusion '{left} != {right}' was not proven")
                    return

            elif then_stmt.type == 'assignment':
                left = child.normalize_object(then_stmt.objects[0])
                expected = float(then_stmt.objects[1])
                cls = next((eq for eq in child.known_equalities if left in eq), None)
                val = child.class_values.get(cls)
                if val != expected:
                    self.errors.append(
                        f"Theorem '{theorem.name}': conclusion '{left} = {expected}' was not proven")
                    return

            elif then_stmt.type == 'sum_assignment':
                canon = child.normalize_signed_sum(then_stmt.objects[0])
                expected = float(then_stmt.objects[1])
                sub = child._substitute_numeric_values(canon)
                numeric, sym = child._split_numeric_symbolic(sub)
                net = expected - numeric

                if not sym:
                    if numeric != expected:
                        self.errors.append(
                            f"Theorem '{theorem.name}': conclusion '{canon} = {expected}' is false")
                        return
                else:
                    key = tuple(sym)
                    cls = next((eq for eq in child.known_equalities if key in eq), None)
                    val = child.class_values.get(cls)
                    if val != net:
                        self.errors.append(
                            f"Theorem '{theorem.name}': conclusion '{canon} = {expected}' was not proven")
                        return

            elif then_stmt.type == 'sum_equality':
                left_canon = child.normalize_signed_sum(then_stmt.objects[0])
                right_canon = child.normalize_signed_sum(then_stmt.objects[1])
                left_sub = child._substitute_numeric_values(left_canon)
                right_sub = child._substitute_numeric_values(right_canon)
                left_num, left_sym = child._split_numeric_symbolic(left_sub)
                right_num, right_sym = child._split_numeric_symbolic(right_sub)
                net_numeric = right_num - left_num

                flipped = [('+' if s == '-' else '-', n) for s, n in right_sym]
                combined_sym = tuple(left_sym) + tuple(flipped)

                proven = False
                if not combined_sym:
                    proven = (net_numeric == 0.0)
                else:
                    cls = next((eq for eq in child.known_equalities if combined_sym in eq), None)
                    val = child.class_values.get(cls)
                    if val is not None and val == net_numeric:
                        proven = True
                    elif net_numeric == 0.0:
                        lc = next((eq for eq in child.known_equalities if tuple(left_sym) in eq), None)
                        rc = next((eq for eq in child.known_equalities if tuple(right_sym) in eq), None)
                        proven = (lc is not None and lc == rc)

                if not proven:
                    self.errors.append(
                        f"Theorem '{theorem.name}': conclusion '{left_canon} = {right_canon}' was not proven")
                    return

        # All conclusions verified — register as reusable axiom
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

    def resolve_numvar_binding(self, value: str) -> Optional[float]:
        try:
            return float(value)
        except ValueError:
            pass
        norm = self.normalize_object(value)
        obj_class = next((eq for eq in self.known_equalities if norm in eq), None)
        return self.class_values.get(obj_class)

    def _err(self, line, msg):
        file, lineno = self.get_infile_line(line)
        return f"{file} | Line {lineno}: {msg}"

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

    def _check_defined(self, canon, line):
        """Return True if every named point in canon is in defined_objects, else append error."""
        for _, name in canon:
            try:
                float(name)
                continue
            except ValueError:
                pass
            norm = self.normalize_object(name) if not name.startswith('ang') else name
            if not all(p in self.defined_objects for p in norm):
                self.errors.append(self._err(line, f"Object '{norm}' not defined"))
                return False
        return True

    def _substitute_numeric_values(self, canon):
        """
        Walk a canonical signed-sum and replace any named segment whose
        equality class has a known numeric value with that number (as a string).
        Bare numeric strings are passed through unchanged.
        """
        result = []
        for sign, name in canon:
            try:
                float(name)  # already a number literal
                result.append((sign, name))
                continue
            except ValueError:
                pass
            norm = self.normalize_object(name) if not name.startswith('ang') else name
            cls = next((eq for eq in self.known_equalities if norm in eq), None)
            val = self.class_values.get(cls) if cls else None
            result.append((sign, str(val) if val is not None else name))
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

    def _store_sum(self, key, value):
        """
        Record  key = value  in known_equalities / class_values.
        key  : tuple of (sign, name) — the canonical symbolic side
        value: float
        """
        cls = next((eq for eq in self.known_equalities if key in eq), None)
        if cls is None:
            cls = frozenset([key])
            self.known_equalities.add(cls)
        self.class_values[cls] = value

    def _store_sum_symbolic(self, left_key, right_key):
        """
        Record  left_key = right_key  with no numeric value yet —
        merge the two keys into one equality class.
        """
        left_cls = next((eq for eq in self.known_equalities if left_key in eq), frozenset([left_key]))
        right_cls = next((eq for eq in self.known_equalities if right_key in eq), frozenset([right_key]))
        self.known_equalities.discard(left_cls)
        self.known_equalities.discard(right_cls)
        merged = left_cls | right_cls
        self.known_equalities.add(merged)
        val = self.class_values.pop(left_cls, None) or self.class_values.pop(right_cls, None)
        if val is not None:
            self.class_values[merged] = val

    def _process_sum_assignment(self, stmt, is_hypothesis):
        """AB + CD = 50"""
        canon = self.normalize_signed_sum(stmt.objects[0])
        right = float(stmt.objects[1])

        if not self._check_defined(canon, stmt.line):
            return

        sub = self._substitute_numeric_values(canon)
        numeric, sym = self._split_numeric_symbolic(sub)
        net = right - numeric  # symbolic part equals this

        if not sym:
            # Fully resolved
            ok = (numeric == right)
            if not ok:
                self.errors.append(
                    self._err(stmt.line, f"'{canon} = {right}' is {'false' if not is_hypothesis else 'conflicting'}"))
            return

        key = tuple(sym)
        if is_hypothesis:
            self._store_sum(key, net)
        else:
            cls = next((eq for eq in self.known_equalities if key in eq), None)
            val = self.class_values.get(cls)
            if val is None:
                self.errors.append(self._err(stmt.line, f"'{key} = {net}' is unproven"))
            elif val != net:
                self.errors.append(self._err(stmt.line, f"'{key} = {net}' is false"))

    def _process_sum_equality(self, stmt, is_hypothesis):
        """AB + CD = EF - GH"""
        left_canon = self.normalize_signed_sum(stmt.objects[0])
        right_canon = self.normalize_signed_sum(stmt.objects[1])

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
            # Both sides fully numeric
            ok = (net_numeric == 0.0)
            if not ok:
                self.errors.append(self._err(stmt.line, f"Numeric conflict: sides differ by {net_numeric}"))
            return

        left_key = tuple(left_sym)
        right_key = tuple(right_sym)

        if is_hypothesis:
            if not left_sym and right_sym:
                # e.g.  50 = EF so store EF = 50
                self._store_sum(right_key, -net_numeric)
            elif left_sym and not right_sym:
                self._store_sum(left_key, net_numeric)
            else:
                # Both symbolic so record as equality class
                self._store_sum_symbolic(left_key, right_key)
        else:
            cls = next((eq for eq in self.known_equalities if combined_sym in eq), None)
            val = self.class_values.get(cls)
            if val is not None and val == net_numeric:
                return
            # Also allow same-class symbolic equality (net_numeric == 0)
            if net_numeric == 0.0:
                left_cls = next((eq for eq in self.known_equalities if left_key in eq), None)
                right_cls = next((eq for eq in self.known_equalities if right_key in eq), None)
                if left_cls is not None and left_cls == right_cls:
                    return
            self.errors.append(self._err(stmt.line, f"'{left_canon} = {right_canon}' is unproven"))

    def process_statement(self, stmt: Statement, is_hypothesis: bool):
        if stmt.type == 'axiom_application':
            self.last_axiom_failed = not self.apply_axiom(stmt)
            return

        if stmt.type == 'let':
            for p in list(stmt.objects[0]):
                self.defined_objects.add(p)
            return

        if stmt.type == 'equality':
            left = self.normalize_object(stmt.objects[0])
            right = self.normalize_object(stmt.objects[1])
            result = self.get_equality_value(left, right)
            if result == 11:
                self.errors.append(self._err(stmt.line, f"Object '{left}' not defined"));
                return
            if result == 12:
                self.errors.append(self._err(stmt.line, f"Object '{right}' not defined"));
                return
            pair = frozenset([left, right])
            if is_hypothesis:
                self.known_equalities.add(pair)
            else:
                if result == 1: self.errors.append(self._err(stmt.line, f"'{left} = {right}' is unproven"))
                if result == 2: self.errors.append(self._err(stmt.line, f"'{left} = {right}' is false"))
            return

        if stmt.type == 'inequality':
            left = self.normalize_object(stmt.objects[0])
            right = self.normalize_object(stmt.objects[1])
            result = self.get_equality_value(left, right, inequality=True)
            if result == 11:
                self.errors.append(self._err(stmt.line, f"Object '{left}' not defined"));
                return
            if result == 12:
                self.errors.append(self._err(stmt.line, f"Object '{right}' not defined"));
                return
            pair = frozenset([left, right])
            if is_hypothesis:
                self.known_inequalities.add(pair)
            else:
                if result == 1: self.errors.append(self._err(stmt.line, f"'{left} != {right}' is unproven"))
                if result == 2: self.errors.append(self._err(stmt.line, f"'{left} != {right}' is false"))
            return

        if stmt.type == 'assignment':
            left = self.normalize_object(stmt.objects[0])
            right = stmt.objects[1]
            result = self.get_equality_value(left, float(right), numeric_value=True)
            if result == 11:
                self.errors.append(self._err(stmt.line, f"Object '{left}' not defined"));
                return
            left_class = next((eq for eq in self.known_equalities if left in eq), None)
            if is_hypothesis:
                if left_class is None:
                    left_class = frozenset([left])
                    self.known_equalities.add(left_class)
                self.class_values[left_class] = float(right)
            else:
                if result == 1: self.errors.append(self._err(stmt.line, f"'{left} = {right}' is unproven"))
                if result == 2: self.errors.append(self._err(stmt.line, f"'{left} = {right}' is false"))
            return

        if stmt.type == 'sum_assignment':
            self._process_sum_assignment(stmt, is_hypothesis)
            return

        if stmt.type == 'sum_equality':
            self._process_sum_equality(stmt, is_hypothesis)
            return

    def apply_axiom(self, stmt: Statement):
        axiom_name = stmt.objects[0]
        bindings = eval(stmt.value)
        line = stmt.line

        if axiom_name not in self.axioms:
            self.errors.append(self._err(line, f"Axiom '{axiom_name}' not defined"))
            return False

        axiom = self.axioms[axiom_name]

        # ── 1. Resolve numvar bindings to concrete floats ────────────────────────
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

        # ── 2. Sanity-check: every point referenced in the axiom is declared ─────
        declared_points = {p for obj in axiom.let_objects for p in obj}
        for s in list(axiom.given.statements) + axiom.then:
            if s.type in ('assignment', 'sum_assignment', 'sum_equality', 'let_numvar'):
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

        # ── helper: apply bindings then substitute known numeric values ──────────
        def concretize(operands):
            """(sign, name) list → substitute bindings → substitute numeric values."""
            with_bindings = [(s, self.substitute_variables(n, bindings)) for s, n in operands]
            return self._substitute_numeric_values(with_bindings)

        # ── 3. Check hypotheses (given) ──────────────────────────────────────────
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
                if not any(left in eq and right in eq for eq in self.known_equalities):
                    self.errors.append(
                        self._err(line, f"Axiom '{axiom_name}': condition '{left} = {right}' not satisfied"))
                    return False

            elif hyp.type == 'inequality':
                left = self.normalize_object(self.substitute_variables(hyp.objects[0], bindings))
                right = self.normalize_object(self.substitute_variables(hyp.objects[1], bindings))
                if not any(left in iq and right in iq for iq in self.known_inequalities):
                    self.errors.append(
                        self._err(line, f"Axiom '{axiom_name}': condition '{left} != {right}' not satisfied"))
                    return False

            elif hyp.type == 'assignment':
                left = self.normalize_object(self.substitute_variables(hyp.objects[0], bindings))
                expected = float(self.substitute_variables(hyp.objects[1], bindings))
                cls = next((eq for eq in self.known_equalities if left in eq), None)
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
                    cls = next((eq for eq in self.known_equalities if key in eq), None)
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
                    cls = next((eq for eq in self.known_equalities if combined_sym in eq), None)
                    val = self.class_values.get(cls)
                    same_class = False
                    if net_numeric == 0.0:
                        lc = next((eq for eq in self.known_equalities if tuple(left_sym) in eq), None)
                        rc = next((eq for eq in self.known_equalities if tuple(right_sym) in eq), None)
                        same_class = (lc is not None and lc == rc)
                    if not same_class and (val is None or val != net_numeric):
                        self.errors.append(self._err(line, f"Axiom '{axiom_name}': condition not satisfied"))
                        return False

        # ── 4. Apply theses (then) ───────────────────────────────────────────────
        for thesis in axiom.then:

            if thesis.type == 'equality':
                left = self.normalize_object(self.substitute_variables(thesis.objects[0], bindings))
                right = self.normalize_object(self.substitute_variables(thesis.objects[1], bindings))
                self.known_equalities.add(frozenset([left, right]))

            elif thesis.type == 'inequality':
                left = self.normalize_object(self.substitute_variables(thesis.objects[0], bindings))
                right = self.normalize_object(self.substitute_variables(thesis.objects[1], bindings))
                self.known_inequalities.add(frozenset([left, right]))

            elif thesis.type == 'sum_assignment':
                concrete = concretize(thesis.objects[0])
                canon = self.normalize_signed_sum(concrete)
                value = float(self.substitute_variables(thesis.objects[1], bindings))
                numeric, sym = self._split_numeric_symbolic(canon)
                net = value - numeric
                if sym:
                    self._store_sum(tuple(sym), net)
                # if not sym: fully numeric, nothing to store

            elif thesis.type == 'sum_equality':
                left_concrete = concretize(thesis.objects[0])
                right_concrete = concretize(thesis.objects[1])
                left_norm = self.normalize_signed_sum(left_concrete)
                right_norm = self.normalize_signed_sum(right_concrete)

                left_num, left_sym = self._split_numeric_symbolic(left_norm)
                right_num, right_sym = self._split_numeric_symbolic(right_norm)
                net_numeric = right_num - left_num

                left_key = tuple(left_sym)
                right_key = tuple(right_sym)

                if not left_sym and not right_sym:
                    pass  # both numeric, nothing to store
                elif not right_sym:
                    self._store_sum(left_key, net_numeric)
                elif not left_sym:
                    self._store_sum(right_key, -net_numeric)
                else:
                    # Both still symbolic — merge equality classes
                    self._store_sum_symbolic(left_key, right_key)
                    # If net_numeric != 0, one side is offset — store on combined key
                    if net_numeric != 0.0:
                        flipped = [('+' if s == '-' else '-', n) for s, n in right_sym]
                        combined_sym = left_key + tuple(flipped)
                        self._store_sum(combined_sym, net_numeric)

        return True
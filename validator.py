from common_classes import *

class Validator:
    def __init__(self):
        self.defined_objects: Set[str] = set()
        self.known_equalities: Set[frozenset] = set()
        self.known_inequalities: Set[frozenset] = set()
        self.axioms: Dict[str, AxiomDefinition] = {}
        self.errors: List[str] = []

    def validate(self, axioms: Dict[str, AxiomDefinition], hypothesis: Optional[HypothesisBlock],
                 proofs: List[Statement]):
        self.axioms = axioms

        # Process hypothesis
        if hypothesis:
            for stmt in hypothesis.statements:
                self.process_statement(stmt, is_hypothesis=True)
            self.propagate_transitivity()
            print(f"DEBUG: known_equalities = {self.known_equalities}")
            print(f"DEBUG: known_inequalities = {self.known_inequalities}")

        # Validate proofs
        for stmt in proofs:
            self.process_statement(stmt, is_hypothesis=False)

    def normalize_edge(self, edge: str) -> str:
        return ''.join(sorted(edge))

    def normalize_angle(self, angle: str) -> str:
        angle = angle[3:]
        mid = angle[1]
        extremes = sorted(angle[0]+angle[2])
        angle = 'ang'+extremes[0]+mid+extremes[1]
        return angle

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

    def process_statement(self, stmt: Statement, is_hypothesis: bool):
        if stmt.type == 'axiom_application':
            self.apply_axiom(stmt)
        elif stmt.type == 'let':
            obj = stmt.objects[0]
            print(f"DEBUG: Processing 'let {obj}'")
            points = list(obj)
            print(f"DEBUG: Points = {points}")
            for p in points:
                self.defined_objects.add(p)
        elif stmt.type == 'equality':
            left = self.normalize_edge(stmt.objects[0])
            right = self.normalize_edge(stmt.objects[1])

            if not all(p in self.defined_objects for p in left):
                self.errors.append(f"Line {stmt.line}: Object '{left}' not defined")
                return
            if not all(p in self.defined_objects for p in right):
                self.errors.append(f"Line {stmt.line}: Object '{right}' not defined")
                return

            left_class = None
            right_class = None
            for eq_class in self.known_equalities:
                if left in eq_class:
                    left_class = eq_class
                if right in eq_class:
                    right_class = eq_class

            left_ineq_class = None
            right_ineq_class = None
            for ineq_class in self.known_inequalities:
                if left in ineq_class:
                    left_ineq_class = ineq_class
                if right in ineq_class:
                    right_ineq_class = ineq_class

            equality_pair = frozenset([left, right])

            if is_hypothesis:
                self.known_equalities.add(equality_pair)
            else:
                if (None in (left_class, right_class) and None in (left_ineq_class, right_ineq_class)) or (
                        left_class != right_class and left_ineq_class != right_ineq_class):
                    self.errors.append(f"Line {stmt.line}: '{left} = {right}' is unproven")
                elif left_ineq_class == right_ineq_class and None not in (left_ineq_class, right_ineq_class):
                    self.errors.append(f"Line {stmt.line}: '{left} = {right}' is false")

        elif stmt.type == 'inequality':
            left = self.normalize_edge(stmt.objects[0])
            right = self.normalize_edge(stmt.objects[1])

            if not all(p in self.defined_objects for p in left):
                self.errors.append(f"Line {stmt.line}: Object '{left}' not defined")
                return
            if not all(p in self.defined_objects for p in right):
                self.errors.append(f"Line {stmt.line}: Object '{right}' not defined")
                return

            left_class = None
            right_class = None
            for eq_class in self.known_equalities:
                if left in eq_class:
                    left_class = eq_class
                if right in eq_class:
                    right_class = eq_class

            left_ineq_class = None
            right_ineq_class = None
            for ineq_class in self.known_inequalities:
                if left in ineq_class:
                    left_ineq_class = ineq_class
                if right in ineq_class:
                    right_ineq_class = ineq_class

            inequality_pair = frozenset([left, right])

            if is_hypothesis:
                self.known_inequalities.add(inequality_pair)
            else:
                if (None in (left_class, right_class) and None in (left_ineq_class, right_ineq_class)) or (
                        left_class != right_class and left_ineq_class != right_ineq_class):
                    self.errors.append(f"Line {stmt.line}: '{left} = {right}' is unproven")
                elif left_class == right_class and None not in (left_class, right_class):
                    self.errors.append(f"Line {stmt.line}: '{left} = {right}' is false")

        elif stmt.type == 'angle_equality':
            left, right = self.normalize_angle(stmt.objects[0]), self.normalize_angle(stmt.objects[1])

            if len(left) != 6:
                self.errors.append(f"Line {stmt.line}: angles require 3 points (given: {left})")
            if len(right) != 6:
                self.errors.append(f"Line {stmt.line}: angles require 3 points (given: {right})")

            sh_left, sh_right = left[3:], right[3:]

            if not all(p in self.defined_objects for p in sh_left):
                self.errors.append(f"Line {stmt.line}: Angle '{sh_left}' not defined")
                return
            if not all(p in self.defined_objects for p in sh_right):
                self.errors.append(f"Line {stmt.line}: Angle '{sh_right}' not defined")
                return

            left_class = None
            right_class = None
            for eq_class in self.known_equalities:
                if left in eq_class:
                    left_class = eq_class
                if right in eq_class:
                    right_class = eq_class

            left_ineq_class = None
            right_ineq_class = None
            for ineq_class in self.known_inequalities:
                if left in ineq_class:
                    left_ineq_class = ineq_class
                if right in ineq_class:
                    right_ineq_class = ineq_class

            equality_pair = frozenset([left, right])

            if is_hypothesis:
                self.known_equalities.add(equality_pair)
            else:
                if (None in (left_class, right_class) and None in (left_ineq_class, right_ineq_class)) or (left_class!=right_class and left_ineq_class!=right_ineq_class):
                    self.errors.append(f"Line {stmt.line}: '{left} = {right}' is unproven")
                elif left_ineq_class == right_ineq_class and None not in (left_ineq_class, right_ineq_class):
                    self.errors.append(f"Line {stmt.line}: '{left} = {right}' is false")

    def apply_axiom(self, stmt: Statement):
        axiom_name = stmt.objects[0]
        bindings = eval(stmt.value)
        line = stmt.line

        if axiom_name not in self.axioms:
            self.errors.append(f"Line {line}: Axiom '{axiom_name}' not defined")
            return

        axiom = self.axioms[axiom_name]
        declared_objects = set(axiom.let_objects)

        defined_points = set()
        for dec_object in declared_objects:
            for point in dec_object:
                defined_points.add(point)

        all_statements = list(axiom.given.statements) + axiom.then

        for stmt_to_check in all_statements:
            for obj in stmt_to_check.objects:
                if obj.startswith('ang'):
                    obj=obj[3:]
                if not obj:
                    continue
                for point in obj:
                    if point not in defined_points:
                        self.errors.append(f"Axiom '{axiom_name}': Point '{point}' in '{obj}' not declared")
                        return

        for hyp_stmt in axiom.given.statements:
            if hyp_stmt.type == 'let':
                obj = hyp_stmt.objects[0]
                if obj in bindings:
                    concrete_obj = bindings[obj]
                    if not all(p in self.defined_objects for p in concrete_obj):
                        self.errors.append(f"Line {line}: Object '{concrete_obj}' not defined")
                        return

            elif hyp_stmt.type == 'equality':
                left = hyp_stmt.objects[0]
                right = hyp_stmt.objects[1]
                concrete_left = self.substitute_variables(left, bindings)
                concrete_right = self.substitute_variables(right, bindings)
                norm_left = self.normalize_edge(concrete_left)
                norm_right = self.normalize_edge(concrete_right)

                found = False
                for eq_class in self.known_equalities:
                    if norm_left in eq_class and norm_right in eq_class:
                        found = True
                        break

                if not found:
                    self.errors.append(
                        f"Line {line}: Axiom hypothesis '{concrete_left} = {concrete_right}' not satisfied")
                    return

            elif hyp_stmt.type == 'inequality':
                left = hyp_stmt.objects[0]
                right = hyp_stmt.objects[1]
                concrete_left = self.substitute_variables(left, bindings)
                concrete_right = self.substitute_variables(right, bindings)
                norm_left = self.normalize_edge(concrete_left)
                norm_right = self.normalize_edge(concrete_right)

                found = False
                for ineq_class in self.known_inequalities:
                    if norm_left in ineq_class and norm_right in ineq_class:
                        found = True
                        break

                if not found:
                    self.errors.append(
                        f"Line {line}: Axiom hypothesis '{concrete_left} != {concrete_right}' not satisfied")
                    return

            elif hyp_stmt.type == 'angle_equality':
                left = hyp_stmt.objects[0]
                right = hyp_stmt.objects[1]
                concrete_left = self.substitute_variables(left, bindings)
                concrete_right = self.substitute_variables(right, bindings)
                norm_left = self.normalize_angle(concrete_left)
                norm_right = self.normalize_angle(concrete_right)

                found = False
                for eq_class in self.known_equalities:
                    if norm_left in eq_class and norm_right in eq_class:
                        found = True
                        break

                if not found:
                    self.errors.append(
                        f"Line {line}: Axiom hypothesis '{concrete_left} = {concrete_right}' not satisfied")
                    return

        for thesis in axiom.then:
            if thesis.type == 'equality':
                left = self.substitute_variables(thesis.objects[0], bindings)
                right = self.substitute_variables(thesis.objects[1], bindings)
                norm_left = self.normalize_edge(left)
                norm_right = self.normalize_edge(right)

                self.known_equalities.add(frozenset([norm_left, norm_right]))

            elif thesis.type == 'inequality':
                left = self.substitute_variables(thesis.objects[0], bindings)
                right = self.substitute_variables(thesis.objects[1], bindings)
                norm_left = self.normalize_edge(left)
                norm_right = self.normalize_edge(right)
                self.known_inequalities.add(frozenset([norm_left, norm_right]))

            elif thesis.type == 'angle_equality':
                left = self.substitute_variables(thesis.objects[0], bindings)
                right = self.substitute_variables(thesis.objects[1], bindings)
                norm_left = self.normalize_angle(left)
                norm_right = self.normalize_angle(right)
                self.known_equalities.add(frozenset([norm_left, norm_right]))

    def substitute_variables(self, template: str, bindings: Dict[str, str]) -> str:
        """Replace variables in template with concrete values"""
        result = template
        for var, concrete in bindings.items():
            result = result.replace(var, concrete)
        return result
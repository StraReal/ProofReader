import re

from parser import *
from validator import *

@dataclass
class AxiomApplication:
    axiom_name: str
    bindings: Dict[str, str]  # {'ABC': 'ABC', 'DEF': 'GHI'}
    line: int

#lexer
def tokenize(code: str) -> List[Token]:
    tokens = []
    lines = code.split('\n')

    for line_num, line in enumerate(lines, 1):
        pos = 0
        while pos < len(line):
            if line[pos].isspace():
                pos += 1
                continue

            # Hypothesis keyword
            if line[pos:].startswith('Hypothesis'):
                tokens.append(Token('HYPOTHESIS', 'Hypothesis', line_num, line))
                pos += 10

            # Proof keyword
            elif line[pos:].startswith('Proof'):
                tokens.append(Token('PROOF', 'Proof', line_num, line))
                pos += 5
            elif line[pos:].startswith('axiom'):
                tokens.append(Token('AXIOM', 'axiom', line_num, line))
                pos += 5
            elif line[pos:].startswith('theorem'):
                tokens.append(Token('THEOREM', 'theorem', line_num, line))
                pos += 7
            elif line[pos:].startswith('Given'):
                tokens.append(Token('GIVEN', 'Given', line_num, line))
                pos += 5

            elif line[pos:].startswith('Then'):
                tokens.append(Token('THEN', 'Then', line_num, line))
                pos += 4

            elif line[pos:].startswith('let'):
                tokens.append(Token('LET', 'let', line_num, line))
                pos += 3

            elif line[pos:].startswith('iso'):
                tokens.append(Token('ISO', 'iso', line_num, line))
                pos += 3
            elif line[pos:].startswith('median'):
                tokens.append(Token('MEDIAN', 'median', line_num, line))
                pos += 6
            elif line[pos:].startswith('bisector'):
                tokens.append(Token('BISECTOR', 'bisector', line_num, line))
                pos += 8
            elif line[pos:].startswith('square'):
                tokens.append(Token('SQUARE', 'square', line_num, line))
                pos += 6
            elif line[pos:].startswith('equilateral'):
                tokens.append(Token('EQUILATERAL', 'equilateral', line_num, line))
                pos += 11
            elif line[pos:].startswith('base'):
                tokens.append(Token('BASE', 'base', line_num, line))
                pos += 4
            # for importing axioms and theorems
            elif line[pos:].startswith('import'):
                tokens.append(Token('IMPORT', 'import', line_num, line))
                pos += 6

            # Angle prefix
            elif line[pos:].startswith('ang'):
                pos += 3
                word = ''
                while pos < len(line) and line[pos].isalnum():
                    word += line[pos]
                    pos += 1
                tokens.append(Token('ANGLE', f'ang{word}', line_num, line))
                continue

            # Identifiers (ABC, AC, etc.)
            elif line[pos].isalpha():
                word = ''
                while pos < len(line) and (line[pos].isalnum() or line[pos] == '_'):
                    word += line[pos]
                    pos += 1
                # numvars x_1, y_1827, z_13
                if re.match(r'^[xyz]_\d+$', word):
                    tokens.append(Token('NUMVAR', word, line_num, line))
                else:
                    tokens.append(Token('IDENT', word, line_num, line))
                continue

            elif line[pos].isdigit():
                num = ''
                while pos < len(line) and line[pos].isdigit():
                    num += line[pos]
                    pos += 1
                tokens.append(Token('NUMBER', num, line_num, line))
                continue


            elif line[pos:].startswith('#'):
                line = line[:pos]
            elif line[pos] == '{':
                tokens.append(Token('LBRACE', '{', line_num, line))
                pos += 1
            elif line[pos] == '}':
                tokens.append(Token('RBRACE', '}', line_num, line))
                pos += 1
            elif line[pos] == ',' and line[pos:pos + 2] != '=>':
                tokens.append(Token('COMMA', ',', line_num, line))
                pos += 1
            elif line[pos:pos + 2] == '=>':
                tokens.append(Token('ARROW', '=>', line_num, line))
                pos += 2
            elif line[pos:pos + 2] == '!=':
                tokens.append(Token('INEQUALS', '!=', line_num, line))
                pos += 2
            elif line[pos] == '+':
                tokens.append(Token('PLUS', '+', line_num, line))
                pos += 1
            elif line[pos] == '-':
                tokens.append(Token('MINUS', '-', line_num, line))  # was '+'
                pos += 1
            elif line[pos] == '=':
                tokens.append(Token('EQUALS', '=', line_num, line))
                pos += 1
            elif line[pos] == ':':
                tokens.append(Token('COLON', ':', line_num, line))
                pos += 1
            else:
                pos += 1

    tokens.append(Token('EOF', '', len(lines), ''))
    return tokens

filename = 'statement.math'
code = load_file(filename)

imported = []
import_map = {}  # Maps line_number -> (filename, original_line_in_file)

original_lines = code.split('\n')
for i, line in enumerate(original_lines, start=1):
    import_map[i] = (filename, i)

original_lines = code.split('\n')
file_tracker = [(filename, i + 1) for i in range(len(code.split('\n')))]
import_map = {i + 1: file_tracker[i] for i in range(len(file_tracker))}

while True:
    tokens = tokenize(code)
    import_map = {i + 1: file_tracker[i] for i in range(len(file_tracker))}
    parser = Parser(tokens, import_map)
    axioms, theorems, hypothesis, proofs, to_import, ordered = parser.parse()

    if not to_import:
        break

    import_line = to_import[1]

    if to_import[0] not in imported:
        imported.append(to_import[0])
        imported_lines = load_file(f'imports/{to_import[0]}.math').split('\n')

        lines = code.split('\n')
        del lines[import_line - 1]
        del file_tracker[import_line - 1]

        for i, line in enumerate(imported_lines):
            lines.insert(import_line - 1 + i, line)
            file_tracker.insert(import_line - 1 + i, (to_import[0], i + 1))

        code = '\n'.join(lines)

import_map = {i + 1: file_tracker[i] for i in range(len(file_tracker))}

validator = Validator(import_map)
validator.validate(axioms, hypothesis, ordered, proofs)

print("=== Axioms ===")
for name, axiom in axioms.items():
    print(f"  {name}: {len(axiom.given.statements)} hypothesis statements")

print("=== Parsed ===")
if hypothesis:
    print(f"Hypothesis: {len(hypothesis.statements)} statements")
print(f"Proofs: {len(proofs)} statements")

print("\n=== Validation ===")
if validator.errors:
    for error in validator.errors:
        print(f"Error: {error}")
else:
    print("All returned valid")
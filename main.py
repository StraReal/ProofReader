import re

from parser import *
from validator import *

@dataclass
class AxiomApplication:
    axiom_name: str
    bindings: Dict[str, str]  # {'ABC': 'ABC', 'DEF': 'GHI'}
    line: int

simple_keywords = {
    'let': 'LET',
    'iso': 'ISO',
    'in': 'IN',
    'median': 'MEDIAN',
    'bisector': 'BISECTOR',
    'square': 'SQUARE',
    'rectangle': 'RECTANGLE',
    'equilateral': 'EQUILATERAL',
    'import': 'IMPORT',
    'contains': 'CONTAINS',
    'print': 'PRINT',
}

#lexer
def tokenize(code: str, import_map: dict) -> List[Token]:
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
            elif line[pos:].startswith('axiom '):
                tokens.append(Token('AXIOM', 'axiom', line_num, line))
                pos += 5
            elif line[pos:].startswith('theorem '):
                tokens.append(Token('THEOREM', 'theorem', line_num, line))
                pos += 7
            elif line[pos:].startswith('Given'):
                tokens.append(Token('GIVEN', 'Given', line_num, line))
                pos += 5

            elif line[pos:].startswith('Then'):
                tokens.append(Token('THEN', 'Then', line_num, line))
                pos += 4

            matched = False
            for keyword, token_type in simple_keywords.items():
                if line[pos:].startswith(keyword):
                    end_pos = pos + len(keyword)
                    if end_pos >= len(line):
                        tokens.append(Token(token_type, keyword, line_num, line))
                        pos += len(keyword)
                        matched = True
                        break
                    if not line[end_pos].isspace():
                        continue
                    tokens.append(Token(token_type, keyword, line_num, line))
                    pos += len(keyword)
                    matched = True
                    break

            if matched:
                continue

            # Angle prefix
            if line[pos:].startswith('ang'):
                pos += 3
                word = ''
                while pos < len(line) and line[pos].isalnum():
                    word += line[pos]
                    pos += 1
                if not (word.isupper() and len(word) == 3):
                    print_error(line_num, f"{word} is not a valid angle", import_map)
                    sys.exit(1)
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

            elif line[pos] == '"':
                string = '"'
                closed = False
                pos += 1
                while pos < len(line):
                    string += line[pos]
                    if line[pos] == '"':
                        closed = True
                        break
                    pos += 1
                if not closed:
                    print_error(line_num, f"Syntax Error: Unclosed quotes.",import_map)
                    sys.exit(1)
                tokens.append(Token('STRING', string, line_num, line))
                pos += 1
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
            elif line[pos] == '<':
                tokens.append(Token('LESSTHAN', '-', line_num, line))  # was '+'
                pos += 1
            elif line[pos] == '>':
                tokens.append(Token('GREATER', '-', line_num, line))  # was '+'
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
    import_map = {i + 1: file_tracker[i] for i in range(len(file_tracker))}
    tokens = tokenize(code, import_map)
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
            file_tracker.insert(import_line - 1 + i, (f"{to_import[0]}.math", i + 1))

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
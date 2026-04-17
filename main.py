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
                tokens.append(Token('HYPOTHESIS', 'Hypothesis', line_num))
                pos += 10

            # Proof keyword
            elif line[pos:].startswith('Proof'):
                tokens.append(Token('PROOF', 'Proof', line_num))
                pos += 5

            elif line[pos:].startswith('axiom'):
                tokens.append(Token('AXIOM', 'axiom', line_num))
                pos += 5
            elif line[pos:].startswith('theorem'):
                tokens.append(Token('THEOREM', 'theorem', line_num))
                pos += 7
            elif line[pos:].startswith('Given'):
                tokens.append(Token('GIVEN', 'Given', line_num))
                pos += 5

            elif line[pos:].startswith('Then'):
                tokens.append(Token('THEN', 'Then', line_num))
                pos += 4

            elif line[pos:].startswith('let'):
                tokens.append(Token('LET', 'let', line_num))
                pos += 3

            elif line[pos:].startswith('iso'):
                tokens.append(Token('ISO', 'iso', line_num))
                pos += 3
            elif line[pos:].startswith('square'):
                tokens.append(Token('SQUARE', 'square', line_num))
                pos += 6
            elif line[pos:].startswith('equilateral'):
                tokens.append(Token('EQUILATERAL', 'equilateral', line_num))
                pos += 6
            elif line[pos:].startswith('base'):
                tokens.append(Token('BASE', 'base', line_num))
                pos += 4
            # for importing axioms and theorems
            elif line[pos:].startswith('import'):
                tokens.append(Token('IMPORT', 'import', line_num))
                pos += 6

            # Angle prefix
            elif line[pos:].startswith('ang'):
                pos += 3
                word = ''
                while pos < len(line) and line[pos].isalnum():
                    word += line[pos]
                    pos += 1
                tokens.append(Token('ANGLE', f'ang{word}', line_num))
                continue

            # Identifiers (ABC, AC, etc.)
            elif line[pos].isalpha():
                word = ''
                while pos < len(line) and line[pos].isalnum():
                    word += line[pos]
                    pos += 1
                tokens.append(Token('IDENT', word, line_num))
                continue

            # Numbers
            elif line[pos].isdigit():
                num = ''
                while pos < len(line) and line[pos].isdigit():
                    num += line[pos]
                    pos += 1
                tokens.append(Token('NUMBER', num, line_num))
                continue

            elif line[pos] == '{':
                tokens.append(Token('LBRACE', '{', line_num))
                pos += 1
            elif line[pos] == '}':
                tokens.append(Token('RBRACE', '}', line_num))
                pos += 1
            elif line[pos] == ',' and line[pos:pos + 2] != '=>':
                tokens.append(Token('COMMA', ',', line_num))
                pos += 1
            elif line[pos:pos + 2] == '=>':
                tokens.append(Token('ARROW', '=>', line_num))
                pos += 2
            elif line[pos:pos + 2] == '!=':
                tokens.append(Token('INEQUALS', '!=', line_num))
                pos += 2
            elif line[pos] == '=':
                tokens.append(Token('EQUALS', '=', line_num))
                pos += 1
            elif line[pos] == ':':
                tokens.append(Token('COLON', ':', line_num))
                pos += 1
            else:
                pos += 1

    tokens.append(Token('EOF', '', len(lines)))
    return tokens

code = load_file('statement.math')

while True:
    tokens = tokenize(code)
    parser = Parser(tokens)
    axioms, hypothesis, proofs, to_import = parser.parse()
    if not to_import:
        break
    lines = code.split('\n')
    del lines[to_import[1]-1]

    imported_lines = load_file(f'{to_import[0]}.math').split('\n')
    for i, line in enumerate(imported_lines):
        lines.insert(i+to_import[1], line)

    code = '\n'.join(lines)

validator = Validator()
validator.validate(axioms, hypothesis, proofs)

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
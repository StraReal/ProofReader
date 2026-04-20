import re

from parser import *
from validator import *

@dataclass
class AxiomApplication:
    axiom_name: str
    bindings: Dict[str, str]  # {'ABC': 'ABC', 'DEF': 'GHI'}
    line: int

simple_keywords = { #require space or end
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
    'axiom': 'AXIOM',
    'theorem': 'THEOREM',
    'operation': 'OPERATION',
    '->': 'ARROW_TYPE',
    'type': 'TYPE',
    'is congruent to': 'EQUALS',
    #'validate_assignment': 'VALIDATE_ASSIGNMENT',
}

colon_keywords = {
    'Then': 'THEN',
    'Given': 'GIVEN',
    'Hypothesis': 'HYPOTHESIS',
    'Proof': 'PROOF',
}

nonwhitespace_keywords = {
    '{': 'LBRACE',
    '}': 'RBRACE',
    '[': 'LBRACKET',
    ']': 'RBRACKET',
    '(': 'LPAR',
    ')': 'RPAR',
    ',': 'COMMA',
    ':': 'COLON',
    '=>': 'CONCL_ARROW',
    '@': 'AT',
}

operators = {
    '+': 'PLUS',
    '-': 'MINUS',
    '*': 'MULTIPLY',
    '/': 'DIVIDE',
    '=': 'ASSIGN',
    '>': 'GREATERTHAN',
    '<': 'LESSTHAN',
    '!=': 'INEQUALS',
    'equals': 'EQUALS',
    'is': 'EQUALS',
}

literals = {
    'true': ('LITBOOL', bool),
    'false': ('LITBOOL', bool)
}

def check_balanced(code: str, import_map: dict):
    stack = []
    matching = {')': '(', ']': '[', '}': '{', '"': '"'}
    openers = set('([{"')
    closers = set(')]}"')
    in_string = False
    in_comment = False
    line = 1

    for i, char in enumerate(code):
        if char == '\n':
            line += 1
            in_comment = False
            continue

        if in_comment:
            continue

        if char == '#':
            in_comment = True
            continue

        if char == '"':
            in_string = not in_string
            continue

        if in_string:
            continue

        if char in openers:
            stack.append((char, i, line))
        elif char in closers:
            if not stack:
                print_error(line, f"Unmatched '{char}'", import_map)
                sys.exit(1)
            opener, pos, opener_line = stack.pop()
            if opener != matching[char]:
                print_error(line, f"Expected '{matching[char]}' to close '{opener}' from line {opener_line}, got '{char}'", import_map)
                sys.exit(1)

    if stack:
        opener, pos, opener_line = stack[-1]
        print_error(opener_line, f"Unclosed '{opener}'", import_map)
        sys.exit(1)

#lexer
def tokenize(code: str, import_map: dict) -> List[Token]:
    tokens = []
    lines = code.split('\n')

    for line_num, line in enumerate(lines, 1):
        pos = 0
        while pos < len(line):
            if line[pos:].startswith('#'):
                break
            elif line[pos].isspace():
                pos += 1
                continue
            matched = False
            op_matched = False

            for keyword, token_type in literals.items():
                if line[pos:].startswith(keyword):
                    end_pos = pos + len(keyword)
                    if end_pos >= len(line):
                        tokens.append(Token(token_type[0], token_type[1](keyword), line_num, line))
                        pos += len(keyword)
                        matched = True
                        break
                    if not line[end_pos].isspace():
                        continue
                    tokens.append(Token(token_type[0], token_type[1](keyword), line_num, line))
                    pos += len(keyword)
                    matched = True
                    break
            if matched:
                continue

            for keyword, token_type in colon_keywords.items():
                if line[pos:].startswith(keyword):
                    colon = False
                    while pos < len(line):
                        if line[pos] == ':':
                            colon = True
                            break
                        pos += 1
                    if not colon:
                        print_error(line_num, f"Syntax Error: Missing colon in front of {keyword}", import_map)
                        sys.exit(1)
                    tokens.append(Token(token_type, keyword, line_num, line))
                    pos += len(keyword)
                    matched = True
                    break
            if matched:
                continue


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

            for op in sorted(nonwhitespace_keywords, key=len, reverse=True):
                if line[pos].startswith(op):
                    tokens.append(Token(nonwhitespace_keywords[op], op, line_num, line))
                    pos+=len(op)
                    op_matched = True
                    break
            if op_matched:
                continue

            for op in sorted(operators, key=len, reverse=True):
                if line[pos:].startswith(op):
                    tokens.append(Token(operators[op], op, line_num, line))
                    pos+=len(op)
                    op_matched = True
                    break
            if op_matched:
                continue

            elif match := re.match(r'[a-z][a-zA-Z0-9_]* ', line[pos:]):
                word = match.group(0).strip()
                if re.match(r'^[a-z]_\d+$', word):
                    tokens.append(Token('NUMVAR', word, line_num, line))
                else:
                    if word.islower():
                        tokens.append(Token('VARIABLE', word, line_num, line))
                pos += len(word)
                continue

            # Identifiers (ABC, AC, etc.)
            elif line[pos].isalpha():
                word = ''
                while pos < len(line) and (line[pos].isalnum() or line[pos] == '_'):
                    word += line[pos]
                    pos += 1
                if word.isupper():
                    tokens.append(Token('IDENT', word, line_num, line))
                else:
                    tokens.append(Token('VARIABLE', word, line_num, line))
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

            #numbers
            elif line[pos].isdigit() or line[pos] == '-':
                if line[pos] == '-':
                    negative = True
                    num = '-'
                    pos += 1
                else:
                    negative = False
                    num = ''
                decimal = False
                while pos < len(line) and (line[pos].isdigit() or line[pos] == '.'):
                    if line[pos] == '.':
                        if decimal:
                            print_error(line_num, f"Syntax Error: Number contains multiple decimal points.",import_map)
                            sys.exit(1)
                        decimal = True
                    num += line[pos]
                    pos += 1

                if decimal:
                    num_type = 'LITFLOAT'
                    num = float(num)
                elif negative:
                    num_type = 'LITINT'
                    num = int(num)
                else:
                    num_type = 'LITNAT'
                    num = int(num)
                tokens.append(Token(num_type, num, line_num, line))
                continue

            if line[pos] == ' ':
                pos += 1
            else:
                print_error(line_num, f"Syntax Error: Invalid character '{line[pos]}'", import_map)
                sys.exit(1)

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
    check_balanced(code, import_map)
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
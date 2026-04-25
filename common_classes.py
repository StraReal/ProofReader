from dataclasses import dataclass
from typing import List, Optional, Dict, Set, Tuple, Sequence, Any, Union
import sys


@dataclass
class OperationDefinition:
    left_type: str
    operator: str
    right_type: str
    return_type: str
    cases: list  # pattern matching cases
    attributes: dict

@dataclass(slots=True, frozen=True)
class Operator:
    symbol: str
    prefix: int | None = None
    postfix: int | None = None
    infix: tuple[int, bool] | None = None
    distfix: tuple[str, int, bool, str] | None = None

@dataclass
class Statement:
    type: str  # 'let', 'equality', 'angle_claim'
    objects: List[any]|str  # ABC, AC, BC, etc.
    value: Optional[str] = None  # For equalities/angles
    line: int = 0
    goal: bool = True
    in_let: bool = False

@dataclass
class Variable:
    name: str

@dataclass
class Literal:
    value: str

@dataclass
class Expression:
    operator: str
    left: 'Expression| Tuple[str, any]'
    right: 'Expression| Tuple[str, any]'
    line: int = None

@dataclass
class HypothesisBlock:
    statements: List['Statement']

@dataclass
class AxiomDefinition:
    name: str
    given: List[Statement]
    then: List[Statement]
    let_objects: List[str]
    let_numvars: List[str]

@dataclass
class TheoremDefinition:
    name: str
    given: List[Statement]
    then: List[Statement]
    proof: List[Statement]
    let_objects: List[str]
    let_numvars: List[str]

@dataclass
class Token:
    type: str  # 'HYPOTHESIS', 'LET', 'IDENT', 'EQUALS', 'ANGLE', 'NUMBER', 'COLON', 'EOF'...
    value: Any
    line_num: int
    line: str

def load_file(filename: str) -> str:
    try:
        with open(filename, 'r') as f:
            return f.read()
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found")
        return ""

def print_error(line, msg, import_map):
    file, lineno = get_infile_line(line, import_map)
    print(f"{file} | Line {lineno}: {msg}")

def get_infile_line(line_num, import_map):
    if line_num in import_map:
        filename, original_line = import_map[line_num]
        return (filename, original_line)
    else:
        return (None, line_num)
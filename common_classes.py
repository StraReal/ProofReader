from dataclasses import dataclass
from typing import List, Optional, Dict, Set, Tuple, Sequence
import sys

@dataclass
class Statement:
    type: str  # 'let', 'equality', 'angle_claim'
    objects: List[str]  # ABC, AC, BC, etc.
    value: Optional[str] = None  # For equalities/angles
    line: int = 0

@dataclass
class HypothesisBlock:
    statements: List['Statement']

@dataclass
class AxiomDefinition:
    name: str
    given: HypothesisBlock
    then: List[Statement]
    let_objects: List[str]
    let_numvars: List[str]

@dataclass
class TheoremDefinition:
    name: str
    given: HypothesisBlock
    then: List[Statement]
    proof: List[Statement]
    let_objects: List[str]
    let_numvars: List[str]

@dataclass
class Token:
    type: str  # 'HYPOTHESIS', 'LET', 'IDENT', 'EQUALS', 'ANGLE', 'NUMBER', 'COLON', 'EOF'...
    value: str
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
from dataclasses import dataclass
from typing import List, Optional, Dict, Set

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

@dataclass
class Token:
    type: str  # 'HYPOTHESIS', 'LET', 'IDENT', 'EQUALS', 'ANGLE', 'NUMBER', 'COLON', 'EOF'...
    value: str
    line: int

def load_file(filename: str) -> str:
    try:
        with open(filename, 'r') as f:
            return f.read()
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found")
        return ""
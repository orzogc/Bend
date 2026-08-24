# regression (AUDIT 6a): a malformed import head gets the import
# diagnostic, not the parser's 'expected def/type/assert' pointing at
# the i
import Wat
assert main:
  Nat

def main():
  1n
$$ bend %
Error:
- message  : an import ('import Base', or 'import <path> as <Name>')

# the pre-freeze \x.f lambda form is dead syntax: lambdas are k => body
# and `\` heads only the match forms \{..} and \{}.
# ported from bend3: same law, bend4 error page
import Base

assert main:
  U32

def main(): (\x.x)(3)
$$ bend %
Error:
- expected : '{'
- observed : 'x'
Location:
 8 | 
 9>| def main(): (\x.x)(3)
10 |

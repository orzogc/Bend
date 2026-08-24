# audit 023: reserved names cannot be used as datatype parameters.
# ported from bend3: U32 is a library name in bend4, so the keyword
# probe is `match`
type Bad<match: Type>:
  Bb10{}
$$ bend %
Error:
- expected : a name (got the keyword 'match')
- observed : ':'
Location:
3 | # probe is `match`
4>| type Bad<match: Type>:
5 |   Bb10{}

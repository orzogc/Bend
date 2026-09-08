# a tab indents like any whitespace: bend4 layout is shape-delimited,
# so the tab-indented body parses.
# ported from bend3: bend3 rejected tab indentation; bend4 pins the
# opposite (whitespace-irrelevant) law
type Vq1 is Data:
	Qv1{}

law main:
  Vq1

def main():
	Qv1{}

#|Qv1{}
